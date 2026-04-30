/*
 * guard_smt_division.c
 *
 * Transform SMT-LIB 2 files: for each literal L that contains a subterm of
 * the form (/ num den) where den is not a numeric constant, replace L with
 * (and L (not (= den 0))).
 *
 * Usage:  ./guard_smt_division <file.smt2|directory>
 * Output: nodiv/<relative/path/to/file.smt2>
 */

#define _POSIX_C_SOURCE 200809L
#include <z3.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <dirent.h>
#include <errno.h>

/* ============================================================
 * String buffer
 * ============================================================ */

typedef struct {
    char  *data;
    size_t len;
    size_t cap;
} StrBuf;

static void strbuf_init(StrBuf *b) {
    b->data = NULL;
    b->len = b->cap = 0;
}

static void strbuf_ensure(StrBuf *b, size_t extra) {
    size_t need = b->len + extra + 1;
    if (need > b->cap) {
        b->cap = need * 2 + 64;
        b->data = realloc(b->data, b->cap);
        if (!b->data) { perror("realloc"); exit(1); }
    }
}

static void strbuf_append(StrBuf *b, const char *s, size_t n) {
    strbuf_ensure(b, n);
    memcpy(b->data + b->len, s, n);
    b->len += n;
    b->data[b->len] = '\0';
}

static void strbuf_appends(StrBuf *b, const char *s) {
    if (s) strbuf_append(b, s, strlen(s));
}

/* ============================================================
 * String vector
 * ============================================================ */

typedef struct {
    char **items;
    int    size;
    int    cap;
} StrVec;

static void strvec_init(StrVec *v) {
    v->items = NULL;
    v->size = v->cap = 0;
}

static void strvec_push(StrVec *v, char *s) {
    if (v->size == v->cap) {
        v->cap = v->cap ? v->cap * 2 : 8;
        v->items = realloc(v->items, (size_t)v->cap * sizeof(char *));
        if (!v->items) { perror("realloc"); exit(1); }
    }
    v->items[v->size++] = s;
}

/* Frees all items and the backing array. NULL items are handled safely. */
static void strvec_free(StrVec *v) {
    for (int i = 0; i < v->size; i++) free(v->items[i]);
    free(v->items);
    v->items = NULL;
    v->size = v->cap = 0;
}

/* ============================================================
 * Z3 AST vector (dynamic array, no ownership of ASTs)
 * ============================================================ */

typedef struct {
    Z3_ast *items;
    int     size;
    int     cap;
} AstVec;

static void astvec_init(AstVec *v) {
    v->items = NULL;
    v->size = v->cap = 0;
}

static void astvec_push(AstVec *v, Z3_ast a) {
    if (v->size == v->cap) {
        v->cap = v->cap ? v->cap * 2 : 8;
        v->items = realloc(v->items, (size_t)v->cap * sizeof(Z3_ast));
        if (!v->items) { perror("realloc"); exit(1); }
    }
    v->items[v->size++] = a;
}

static void astvec_free(AstVec *v) {
    free(v->items);
    v->items = NULL;
    v->size = v->cap = 0;
}

/* ============================================================
 * SMT2 command splitter
 * ============================================================ */

static StrVec parse_smt2_commands(const char *text) {
    StrVec cmds;
    strvec_init(&cmds);
    size_t i = 0, n = strlen(text);

    while (i < n) {
        /* skip whitespace */
        while (i < n && (text[i] == ' ' || text[i] == '\t' ||
                         text[i] == '\n' || text[i] == '\r'))
            i++;
        if (i >= n) break;

        /* skip line comments */
        if (text[i] == ';') {
            while (i < n && text[i] != '\n') i++;
            if (i < n) i++;
            continue;
        }

        if (text[i] != '(') { i++; continue; }

        size_t start = i;
        int depth = 0;
        bool in_string = false, in_comment = false;

        while (i < n) {
            char c = text[i];
            if (in_comment) {
                if (c == '\n') in_comment = false;
            } else if (in_string) {
                if (c == '\\') i++;       /* skip escaped character */
                else if (c == '"') in_string = false;
            } else {
                if      (c == ';')  in_comment = true;
                else if (c == '"')  in_string  = true;
                else if (c == '(')  depth++;
                else if (c == ')') {
                    depth--;
                    if (depth == 0) {
                        size_t len = i - start + 1;
                        char *cmd = malloc(len + 1);
                        if (!cmd) { perror("malloc"); exit(1); }
                        memcpy(cmd, text + start, len);
                        cmd[len] = '\0';
                        strvec_push(&cmds, cmd);
                        i++;
                        break;
                    }
                }
            }
            i++;
        }
    }
    return cmds;
}

/* Returns a pointer into a static buffer; valid until the next call. */
static const char *get_command_name(const char *cmd) {
    static char buf[128];
    const char *p = cmd;
    while (*p && (*p == '(' || *p == ' ' || *p == '\t' || *p == '\n')) p++;
    size_t i = 0;
    while (*p && *p != ' ' && *p != '\t' && *p != '\n' &&
           *p != '(' && *p != ')' && i < 127)
        buf[i++] = *p++;
    buf[i] = '\0';
    return i ? buf : NULL;
}

/* ============================================================
 * Z3 helpers
 * ============================================================ */

/* Silent error handler: we check Z3_get_error_code() ourselves. */
static void z3_error_handler(Z3_context ctx, Z3_error_code e) {
    (void)ctx; (void)e;
}

static bool is_numeric_const(Z3_context ctx, Z3_ast e) {
    if (Z3_is_numeral_ast(ctx, e)) return true;
    if (!Z3_is_app(ctx, e)) return false;
    Z3_app app = Z3_to_app(ctx, e);
    Z3_decl_kind k = Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, app));
    if ((k == Z3_OP_TO_REAL || k == Z3_OP_TO_INT) &&
        Z3_get_app_num_args(ctx, app) == 1)
        return is_numeric_const(ctx, Z3_get_app_arg(ctx, app, 0));
    return false;
}

/* ---- simple integer set for visited AST IDs ---- */
typedef struct { unsigned *data; int size, cap; } IdSet;

static void idset_init(IdSet *s) { s->data = NULL; s->size = s->cap = 0; }
static void idset_free(IdSet *s) { free(s->data); s->data = NULL; s->size = s->cap = 0; }

/* Returns true if id was newly inserted; false if it was already present. */
static bool idset_add(IdSet *s, unsigned id) {
    for (int i = 0; i < s->size; i++)
        if (s->data[i] == id) return false;
    if (s->size == s->cap) {
        s->cap = s->cap ? s->cap * 2 : 16;
        s->data = realloc(s->data, (size_t)s->cap * sizeof(unsigned));
        if (!s->data) { perror("realloc"); exit(1); }
    }
    s->data[s->size++] = id;
    return true;
}

/* Collect all non-constant denominators reachable from e. */
static void collect_dens_rec(Z3_context ctx, Z3_ast e,
                              AstVec *dens, IdSet *seen) {
    unsigned id = Z3_get_ast_id(ctx, e);
    if (!idset_add(seen, id)) return;
    if (!Z3_is_app(ctx, e)) return;
    Z3_app app = Z3_to_app(ctx, e);
    unsigned nargs = Z3_get_app_num_args(ctx, app);
    if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, app)) == Z3_OP_DIV
        && nargs == 2) {
        Z3_ast den = Z3_get_app_arg(ctx, app, 1);
        if (!is_numeric_const(ctx, den))
            astvec_push(dens, den);
    }
    for (unsigned i = 0; i < nargs; i++)
        collect_dens_rec(ctx, Z3_get_app_arg(ctx, app, i), dens, seen);
}

static AstVec get_non_const_dens(Z3_context ctx, Z3_ast e) {
    AstVec dens; astvec_init(&dens);
    IdSet seen;  idset_init(&seen);
    collect_dens_rec(ctx, e, &dens, &seen);
    idset_free(&seen);
    return dens;
}

static bool ast_is_bool(Z3_context ctx, Z3_ast e) {
    return Z3_get_sort_kind(ctx, Z3_get_sort(ctx, e)) == Z3_BOOL_SORT;
}

static Z3_decl_kind app_kind(Z3_context ctx, Z3_ast e) {
    return Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, e)));
}

static bool is_atom(Z3_context ctx, Z3_ast e) {
    if (!ast_is_bool(ctx, e)) return false;
    if (Z3_get_ast_kind(ctx, e) == Z3_QUANTIFIER_AST) return false;
    if (!Z3_is_app(ctx, e)) return false;
    switch (app_kind(ctx, e)) {
        case Z3_OP_AND:
        case Z3_OP_OR:
        case Z3_OP_NOT:
        case Z3_OP_IMPLIES:
        case Z3_OP_TRUE:
        case Z3_OP_FALSE:
        case Z3_OP_ITE:
            return false;
        default:
            return true;
    }
}

static bool is_literal(Z3_context ctx, Z3_ast e) {
    if (!Z3_is_app(ctx, e)) return false;
    if (app_kind(ctx, e) == Z3_OP_NOT) {
        Z3_app app = Z3_to_app(ctx, e);
        if (Z3_get_app_num_args(ctx, app) == 1)
            return is_atom(ctx, Z3_get_app_arg(ctx, app, 0));
        return false;
    }
    return is_atom(ctx, e);
}

static Z3_ast make_nonzero_guard(Z3_context ctx, Z3_ast den) {
    Z3_sort_kind sk = Z3_get_sort_kind(ctx, Z3_get_sort(ctx, den));
    Z3_ast zero = (sk == Z3_REAL_SORT)
        ? Z3_mk_real(ctx, 0, 1)
        : Z3_mk_int(ctx, 0, Z3_mk_int_sort(ctx));
    return Z3_mk_not(ctx, Z3_mk_eq(ctx, den, zero));
}

/* Deduplicate dens by their s-expression string representation. */
static AstVec dedup_dens(Z3_context ctx, const AstVec *dens) {
    AstVec unique; astvec_init(&unique);
    StrVec keys;   strvec_init(&keys);
    for (int i = 0; i < dens->size; i++) {
        /* Z3_ast_to_string returns a string managed by Z3; copy immediately. */
        const char *s = Z3_ast_to_string(ctx, dens->items[i]);
        bool found = false;
        for (int j = 0; j < keys.size; j++)
            if (strcmp(keys.items[j], s) == 0) { found = true; break; }
        if (!found) {
            astvec_push(&unique, dens->items[i]);
            strvec_push(&keys, strdup(s));
        }
    }
    strvec_free(&keys);
    return unique;
}

/* ============================================================
 * Formula transformation
 * ============================================================ */

static Z3_ast transform_formula(Z3_context ctx, Z3_ast e, bool *changed) {
    if (!ast_is_bool(ctx, e)) return e;

    /* ---- literal: leaf of the boolean tree ---- */
    if (is_literal(ctx, e)) {
        AstVec dens = get_non_const_dens(ctx, e);
        if (dens.size == 0) { astvec_free(&dens); return e; }
        AstVec unique = dedup_dens(ctx, &dens);
        astvec_free(&dens);

        AstVec args; astvec_init(&args);
        astvec_push(&args, e);
        for (int i = 0; i < unique.size; i++)
            astvec_push(&args, make_nonzero_guard(ctx, unique.items[i]));
        astvec_free(&unique);

        *changed = true;
        Z3_ast result = Z3_mk_and(ctx, (unsigned)args.size, args.items);
        astvec_free(&args);
        return result;
    }

    if (!Z3_is_app(ctx, e)) return e;

    Z3_app app = Z3_to_app(ctx, e);
    Z3_decl_kind k = app_kind(ctx, e);
    unsigned nargs = Z3_get_app_num_args(ctx, app);

    /* ---- propositional connectives: recurse ---- */
    if (k == Z3_OP_AND) {
        AstVec new_args; astvec_init(&new_args);
        for (unsigned i = 0; i < nargs; i++)
            astvec_push(&new_args,
                transform_formula(ctx, Z3_get_app_arg(ctx, app, i), changed));
        Z3_ast r = Z3_mk_and(ctx, (unsigned)new_args.size, new_args.items);
        astvec_free(&new_args);
        return r;
    }
    if (k == Z3_OP_OR) {
        AstVec new_args; astvec_init(&new_args);
        for (unsigned i = 0; i < nargs; i++)
            astvec_push(&new_args,
                transform_formula(ctx, Z3_get_app_arg(ctx, app, i), changed));
        Z3_ast r = Z3_mk_or(ctx, (unsigned)new_args.size, new_args.items);
        astvec_free(&new_args);
        return r;
    }
    if (k == Z3_OP_NOT && nargs == 1) {
        Z3_ast inner = Z3_get_app_arg(ctx, app, 0);
        /* not(non-atom): recurse inside */
        if (!is_atom(ctx, inner))
            return Z3_mk_not(ctx, transform_formula(ctx, inner, changed));
        /* not(atom) is a literal; already handled above */
        return e;
    }
    if (k == Z3_OP_IMPLIES && nargs == 2) {
        Z3_ast a = transform_formula(ctx, Z3_get_app_arg(ctx, app, 0), changed);
        Z3_ast b = transform_formula(ctx, Z3_get_app_arg(ctx, app, 1), changed);
        return Z3_mk_implies(ctx, a, b);
    }
    if (k == Z3_OP_ITE && nargs == 3) {
        Z3_ast c = transform_formula(ctx, Z3_get_app_arg(ctx, app, 0), changed);
        Z3_ast t = transform_formula(ctx, Z3_get_app_arg(ctx, app, 1), changed);
        Z3_ast f = transform_formula(ctx, Z3_get_app_arg(ctx, app, 2), changed);
        return Z3_mk_ite(ctx, c, t, f);
    }

    /* Quantifiers and other structures: leave unchanged. */
    return e;
}

/* ============================================================
 * simplify_to_real: replace (to_real N) with N.0
 * ============================================================ */

static char *simplify_to_real(const char *text) {
    static const char needle[] = "(to_real ";
    static const size_t nlen   = sizeof(needle) - 1; /* = strlen(needle) */

    StrBuf out; strbuf_init(&out);
    const char *p   = text;
    const char *end = text + strlen(text);

    while (p < end) {
        const char *found = strstr(p, needle);
        if (!found) { strbuf_append(&out, p, (size_t)(end - p)); break; }

        strbuf_append(&out, p, (size_t)(found - p));

        const char *q = found + nlen;
        while (q < end && (*q == ' ' || *q == '\t')) q++;
        const char *num_start = q;
        while (q < end && *q >= '0' && *q <= '9') q++;
        size_t num_len = (size_t)(q - num_start);
        while (q < end && (*q == ' ' || *q == '\t')) q++;

        if (num_len > 0 && q < end && *q == ')') {
            strbuf_append(&out, num_start, num_len);
            strbuf_appends(&out, ".0");
            p = q + 1;
        } else {
            /* Not a simple integer literal: emit needle verbatim and advance */
            strbuf_append(&out, needle, nlen);
            p = found + nlen;
        }
    }
    return out.data ? out.data : strdup("");
}

/* ============================================================
 * Context-command filter
 * ============================================================ */

static bool is_context_cmd(const char *name) {
    if (!name) return false;
    static const char *ctx_cmds[] = {
        "set-logic", "set-option", "set-info",
        "declare-fun", "declare-const", "declare-sort",
        "define-fun", "define-sort", "define-const",
        NULL
    };
    for (int i = 0; ctx_cmds[i]; i++)
        if (strcmp(name, ctx_cmds[i]) == 0) return true;
    return false;
}

/* ============================================================
 * Per-assertion transformation
 * ============================================================ */

/* Returns a newly-allocated string (caller must free). */
static char *transform_assert(const StrVec *ctx_cmds,
                               const char *assert_cmd,
                               bool *changed) {
    /* Build the full SMT2 context + assertion string for Z3 to parse */
    StrBuf full; strbuf_init(&full);
    for (int i = 0; i < ctx_cmds->size; i++) {
        strbuf_appends(&full, ctx_cmds->items[i]);
        strbuf_appends(&full, "\n");
    }
    strbuf_appends(&full, assert_cmd);

    Z3_config  cfg = Z3_mk_config();
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_set_error_handler(ctx, z3_error_handler);

    Z3_ast_vector vec = Z3_parse_smtlib2_string(
        ctx, full.data, 0, NULL, NULL, 0, NULL, NULL);
    free(full.data);

    Z3_error_code ec = Z3_get_error_code(ctx);
    if (ec != Z3_OK) {
        fprintf(stderr,
            "Warning: could not parse assertion, keeping original.\n  %s\n",
            Z3_get_error_msg(ctx, ec));
        Z3_del_context(ctx);
        return strdup(assert_cmd);
    }

    unsigned sz = Z3_ast_vector_size(ctx, vec);
    if (sz == 0) {
        Z3_del_context(ctx);
        return strdup(assert_cmd);
    }

    Z3_ast formula;
    if (sz == 1) {
        formula = Z3_ast_vector_get(ctx, vec, 0);
    } else {
        Z3_ast *args = malloc(sz * sizeof(Z3_ast));
        if (!args) { perror("malloc"); exit(1); }
        for (unsigned i = 0; i < sz; i++)
            args[i] = Z3_ast_vector_get(ctx, vec, i);
        formula = Z3_mk_and(ctx, sz, args);
        free(args);
    }

    Z3_ast transformed = transform_formula(ctx, formula, changed);

    /* Copy the s-expression string before deleting the context */
    const char *sexpr = Z3_ast_to_string(ctx, transformed);
    StrBuf result; strbuf_init(&result);
    strbuf_appends(&result, "(assert ");
    strbuf_appends(&result, sexpr);
    strbuf_appends(&result, ")");

    Z3_del_context(ctx);

    char *simplified = simplify_to_real(result.data);
    free(result.data);
    return simplified;
}

/* ============================================================
 * File I/O helpers
 * ============================================================ */

static char *slurp_file(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); return NULL; }
    if (fseek(f, 0, SEEK_END) < 0) { perror(path); fclose(f); return NULL; }
    long sz = ftell(f);
    if (sz < 0) { perror(path); fclose(f); return NULL; }
    rewind(f);
    char *buf = malloc((size_t)sz + 1);
    if (!buf) { perror("malloc"); fclose(f); return NULL; }
    if (fread(buf, 1, (size_t)sz, f) != (size_t)sz && sz > 0) {
        fprintf(stderr, "Error reading %s\n", path);
        free(buf); fclose(f); return NULL;
    }
    buf[sz] = '\0';
    fclose(f);
    return buf;
}

static bool file_contains_division(const char *path) {
    char *text = slurp_file(path);
    if (!text) return false;
    bool found = strchr(text, '/') != NULL;
    free(text);
    return found;
}

/* Equivalent to mkdir -p */
static int makedirs(const char *path) {
    char *p = strdup(path);
    if (!p) return -1;
    for (char *q = p + 1; *q; q++) {
        if (*q == '/') {
            *q = '\0';
            if (mkdir(p, 0755) < 0 && errno != EEXIST) {
                free(p); return -1;
            }
            *q = '/';
        }
    }
    int ret = (mkdir(p, 0755) < 0 && errno != EEXIST) ? -1 : 0;
    free(p);
    return ret;
}

/* ============================================================
 * File-level processing
 * ============================================================ */

/* Returns newly-allocated output text; caller must free. NULL on error. */
static char *transform_file_content(const char *input_path, bool *changed_out) {
    char *text = slurp_file(input_path);
    if (!text) return NULL;

    StrVec commands = parse_smt2_commands(text);
    free(text);

    StrVec ctx_cmds; strvec_init(&ctx_cmds);
    StrBuf result;   strbuf_init(&result);
    bool changed = false;

    for (int i = 0; i < commands.size; i++) {
        const char *name = get_command_name(commands.items[i]);
        if (is_context_cmd(name)) {
            strvec_push(&ctx_cmds, strdup(commands.items[i]));
            strbuf_appends(&result, commands.items[i]);
        } else if (name && strcmp(name, "assert") == 0) {
            char *t = transform_assert(&ctx_cmds, commands.items[i], &changed);
            strbuf_appends(&result, t);
            free(t);
        } else {
            strbuf_appends(&result, commands.items[i]);
        }
        strbuf_appends(&result, "\n");
    }

    strvec_free(&commands);
    strvec_free(&ctx_cmds);

    *changed_out = changed;
    return result.data ? result.data : strdup("");
}

static void process_file(const char *input_path) {
    if (!file_contains_division(input_path)) {
        printf("Skipped (no '/'): %s\n", input_path);
        return;
    }

    bool changed = false;
    char *result = transform_file_content(input_path, &changed);
    if (!result) return;

    if (!changed) {
        printf("Skipped (no non-constant denominator): %s\n", input_path);
        free(result);
        return;
    }

    /* Output path: nodiv/<input_path> */
    StrBuf outpath; strbuf_init(&outpath);
    strbuf_appends(&outpath, "nodiv/");
    strbuf_appends(&outpath, input_path);

    /* Create parent directory */
    {
        char *dir = strdup(outpath.data);
        char *last_slash = strrchr(dir, '/');
        if (last_slash) {
            *last_slash = '\0';
            if (makedirs(dir) < 0) {
                fprintf(stderr, "Error creating directory %s: %s\n",
                        dir, strerror(errno));
                free(dir); free(outpath.data); free(result);
                return;
            }
        }
        free(dir);
    }

    FILE *f = fopen(outpath.data, "w");
    if (!f) {
        fprintf(stderr, "Error opening %s for writing: %s\n",
                outpath.data, strerror(errno));
        free(outpath.data); free(result);
        return;
    }
    fputs(result, f);
    fclose(f);

    printf("Written: %s\n", outpath.data);
    free(outpath.data);
    free(result);
}

/* ============================================================
 * Directory walking
 * ============================================================ */

static int cmp_strp(const void *a, const void *b) {
    return strcmp(*(const char *const *)a, *(const char *const *)b);
}

static void collect_smt2_files(const char *dir_path, StrVec *files) {
    DIR *d = opendir(dir_path);
    if (!d) { perror(dir_path); return; }

    StrVec found_files; strvec_init(&found_files);
    StrVec subdirs;     strvec_init(&subdirs);

    struct dirent *entry;
    while ((entry = readdir(d))) {
        if (entry->d_name[0] == '.') continue;

        StrBuf path; strbuf_init(&path);
        strbuf_appends(&path, dir_path);
        strbuf_appends(&path, "/");
        strbuf_appends(&path, entry->d_name);

        struct stat st;
        if (stat(path.data, &st) < 0) { free(path.data); continue; }

        if (S_ISDIR(st.st_mode)) {
            strvec_push(&subdirs, path.data);
        } else if (S_ISREG(st.st_mode)) {
            size_t len = strlen(entry->d_name);
            if (len > 5 && strcmp(entry->d_name + len - 5, ".smt2") == 0)
                strvec_push(&found_files, path.data);
            else
                free(path.data);
        } else {
            free(path.data);
        }
    }
    closedir(d);

    if (found_files.size > 0)
        qsort(found_files.items, (size_t)found_files.size,
              sizeof(char *), cmp_strp);
    if (subdirs.size > 0)
        qsort(subdirs.items, (size_t)subdirs.size,
              sizeof(char *), cmp_strp);

    /* Transfer found files to output (ownership transferred, items NULLed) */
    for (int i = 0; i < found_files.size; i++) {
        strvec_push(files, found_files.items[i]);
        found_files.items[i] = NULL;
    }
    free(found_files.items);

    /* Recurse into subdirectories */
    for (int i = 0; i < subdirs.size; i++) {
        collect_smt2_files(subdirs.items[i], files);
        free(subdirs.items[i]);
        subdirs.items[i] = NULL;
    }
    free(subdirs.items);
}

/* ============================================================
 * main
 * ============================================================ */

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <file.smt2|directory>\n", argv[0]);
        return 1;
    }

    struct stat st;
    if (stat(argv[1], &st) < 0) {
        fprintf(stderr, "Error: cannot access %s: %s\n",
                argv[1], strerror(errno));
        return 1;
    }

    if (S_ISREG(st.st_mode)) {
        process_file(argv[1]);
    } else if (S_ISDIR(st.st_mode)) {
        StrVec files; strvec_init(&files);
        collect_smt2_files(argv[1], &files);
        if (files.size == 0) {
            fprintf(stderr, "No .smt2 files found in %s\n", argv[1]);
            strvec_free(&files);
            return 1;
        }
        for (int i = 0; i < files.size; i++)
            process_file(files.items[i]);
        strvec_free(&files);
    } else {
        fprintf(stderr, "Error: %s is not a file or directory\n", argv[1]);
        return 1;
    }

    return 0;
}
