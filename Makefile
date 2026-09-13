COBC ?= cobc
COBFLAGS ?= -free -Wall -Wno-linkage -Wno-others -I src/copy -O2
COMMON = src/tc-methods.cob src/tc-spines.cob src/primitive-well-founded.cob src/primitive-wf-support.cob src/string-literal.cob src/nat-reduce.cob src/nested-support.cob src/nested-lower.cob src/nested-restore.cob src/primitive-reflection.cob src/primitive-quotes.cob src/primitive-equations.cob src/nat-literal.cob src/quot.cob src/primitive.cob src/inductive-reduce.cob src/projection.cob src/inductive-generate.cob src/inductive.cob src/expr-build.cob src/replay.cob src/equiv.cob src/reduction.cob src/defeq.cob src/tc-cache.cob src/level-native.cob src/type-checker.cob src/environment.cob src/expr-ops.cob src/transform-cache.cob src/expr.cob src/list.cob src/blob.cob src/arena.cob src/hashtab.cob src/name.cob src/level.cob src/bignum.cob

# Secondary public ENTRY points avoid GnuCOBOL 3.2's whole-stack scan in
# nonrecursive helpers. Debug retains the primary entry and recursion checks.
# Compile each file separately to avoid GnuCOBOL 3.2 compiler-state corruption.
FAST_HELPERS ?= 1
MODE ?= release
BUILD = bin/build/$(MODE)
OBJECTS = $(COMMON:src/%.cob=$(BUILD)/objects/%.o)
PARSER = src/parser-fast.cob src/stream.cob src/json.cob src/parser.cob src/parser-expr.cob src/parser-decl.cob
PARSER_OBJECTS = $(PARSER:src/%.cob=$(BUILD)/objects/%.o)
NAT_OBJECTS = $(addprefix $(BUILD)/objects/,arena.o blob.o hashtab.o name.o level.o tc-cache.o bignum.o)
PROGRAMS = lean4cobol level-test expr-test nat-test storage-test hash-test
PUBLIC = $(addprefix bin/,$(PROGRAMS))

.NOTPARALLEL:
.PHONY: all test clean debug FORCE $(PUBLIC)
all: $(PUBLIC)

# Public paths always select the requested mode, even when its binary is older.
$(PUBLIC): bin/%: $(BUILD)/%
	ln -sfn build/$(MODE)/$* $@

# Flag changes invalidate only this mode's objects. Unchanged flags keep mtimes.
$(BUILD)/config: FORCE
	@mkdir -p $(BUILD)
	@printf '%s\n' '$(COBC) | $(COBFLAGS) | $(FAST_HELPERS)' > $@.tmp
	@cmp -s $@ $@.tmp || cp $@.tmp $@
	@rm -f $@.tmp
FORCE:

$(BUILD)/objects/%.o: src/%.cob scripts/prepare-cobol.py $(wildcard src/copy/*.cpy) $(BUILD)/config
	mkdir -p $@.build
ifeq ($(FAST_HELPERS),1)
	python3 scripts/prepare-cobol.py $< $@.build/source.cob
	cd $@.build && $(COBC) $(COBFLAGS) -I $(abspath src/copy) --save-temps -c -o $(abspath $@) source.cob
else
	cd $@.build && $(COBC) $(COBFLAGS) -I $(abspath src/copy) --save-temps -c -o $(abspath $@) $(abspath $<)
endif
$(BUILD)/lean4cobol: src/main.cob $(PARSER_OBJECTS) $(OBJECTS) $(wildcard src/copy/*.cpy) $(BUILD)/config
	mkdir -p $@.build
	$(COBC) $(COBFLAGS) --save-temps=$@.build -x -o $@ src/main.cob $(PARSER_OBJECTS) $(OBJECTS)
$(BUILD)/level-test: tests/level-driver.cob $(OBJECTS) $(wildcard src/copy/*.cpy) $(BUILD)/config
	mkdir -p $@.build
	$(COBC) $(COBFLAGS) --save-temps=$@.build -x -o $@ $< $(OBJECTS)
$(BUILD)/expr-test: tests/expr-driver.cob $(OBJECTS) $(wildcard src/copy/*.cpy) $(BUILD)/config
	mkdir -p $@.build
	$(COBC) $(COBFLAGS) --save-temps=$@.build -x -o $@ $< $(OBJECTS)
$(BUILD)/nat-test: tests/nat-driver.cob $(NAT_OBJECTS) $(wildcard src/copy/*.cpy) $(BUILD)/config
	mkdir -p $@.build
	$(COBC) $(COBFLAGS) --save-temps=$@.build -x -o $@ $< $(NAT_OBJECTS)
$(BUILD)/hash-test: tests/hash-driver.cob src/copy/hash-native.cpy src/copy/hash-mix.cpy $(BUILD)/config
	mkdir -p $@.build
	$(COBC) $(COBFLAGS) --save-temps=$@.build -x -o $@ $<
$(BUILD)/storage-test: tests/storage-driver.cob $(OBJECTS) $(wildcard src/copy/*.cpy) $(BUILD)/config
	mkdir -p $@.build
	$(COBC) $(COBFLAGS) --save-temps=$@.build -x -o $@ $< $(OBJECTS)
test: all
	bin/storage-test
	python3 tests/test.py
debug:
	$(MAKE) MODE=debug FAST_HELPERS=0 COBFLAGS='-free -Wall -Wno-linkage -Wno-others -I src/copy -debug -g' test
clean:
	rm -rf bin
