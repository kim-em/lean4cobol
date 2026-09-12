# String literals

`string-constructor(state, expr, result)` returns a non-string expression
unchanged. For a string literal it constructs exactly the pinned
Lean4Lean.Expr.strLitToConstructor term: String.ofList applied to a List.{0} of
Char.ofNat applications, one per Unicode scalar. List.nil/List.cons carry the
Char type argument. The parser validates UTF-8; expansion decodes it backwards
to build the list in its original order. It rebinds the byte-arena view after
each interning step, so growth while interning scalar numerals is safe.

Literal whnf itself remains a literal. Expansion is invoked on demand:

- `def-string-core` compares a literal with a unary String.ofList application
  whose universe list is empty. Equality tries both directions after structure
  eta and before unit-like equality, as in the reference.
- `reduce-projection-core` expands and normalizes a string structure before
  selecting its constructor field. Its interface now carries checking depth.
- `ind-reduce` expands and normalizes a string major premise before choosing
  its generated recursor rule.

Expression nodes cache whether they contain a string literal. On the first
such declaration, replay marks strings as encountered and replays String.ofList
and Char.ofNat before checking the declaration. Both type and value contribute;
unsafe declarations remain skipped. The flag is global to the replay, matching
the reference's hasStrings state, while expression metadata is purely structural.

`tests/strings.lean` exports equality, projection and recursor examples using
the pinned exporter. The long example creates new scalar numeral blobs while
expanding an 8,192-character literal. `tests/test_strings.py` checks the fixture,
forged expected values, raw/escaped JSON, missing primitive dependencies,
reordered declarations and unsafe literals. The manifest records source and
stream hashes for reproduction.
