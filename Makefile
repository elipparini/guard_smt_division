CC      = gcc
CFLAGS  = -O2 -Wall -Wextra -std=c11 $(shell pkg-config --cflags z3)
LDFLAGS = $(shell pkg-config --libs z3)
PROG    = guard_smt_division

$(PROG): guard_smt_division.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

clean:
	rm -f $(PROG)

test: $(PROG)
	@echo "=== Test 1: single file (with division) ==="
	./$(PROG) test_folder/div_test1.smt2
	@echo "--- nodiv/test_folder/div_test1.smt2 ---"
	@cat nodiv/test_folder/div_test1.smt2
	@echo "=== Test 2: single file (no division) ==="
	./$(PROG) test_folder/nodiv_test.smt2
	@echo "=== Test 3: directory ==="
	./$(PROG) test_folder

.PHONY: clean test
