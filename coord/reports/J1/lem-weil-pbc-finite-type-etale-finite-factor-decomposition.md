# Worker report: lem-weil-pbc-finite-type-etale-finite-factor-decomposition

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-etale-finite-factor-decomposition.json`: split item, six induction steps, Mathlib verdict no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-field-finite-isolated-points.json`: new unsplit auxiliary statement, Mathlib verdict no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-algebra-tensor-product-distributes-product.json`: new Mathlib leaf, exact `Algebra.TensorProduct.prodRight` match.

## Review by J1

I read the item source, Algebra Lemma Tag 00UK (the `lemma-etale-makes-quasi-finite-finite` proof, lines 40362-40420), and the cited one-point input 00UJ. The item statement agrees with 00UK after combining its finitely many finite factors into one factor `A'`; the hypotheses are exactly a finite-type map and a chosen prime, and the conclusion keeps the elementary etale extension, residue-field isomorphism, product decomposition, finite factor, and absence of quasi-finite points in the complementary factor. No declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator` states this item or carries its blueprint id; the item's slopmaster2 audit therefore remains `none`.

The split follows the 00UK induction. Step 1 reduces to the finite set of isolated points in the finite-type fibre and uses the new auxiliary node plus the fibre-prime bijection and the definition of quasi-finiteness. Step 2 handles the empty set with the zero finite factor. Step 3 applies the reviewed 00UJ node to one isolated point and forms the complementary idempotent factor. Step 4 checks the fibre spectrum after the residue-field-preserving etale base change, identifies the complementary factor's primes, and removes the selected point. Step 5 applies the induction hypothesis, distributes tensor product over the idempotent product via the new Mathlib leaf, combines finite factors, and composes etale/residue maps. Step 6 retains the induction hypothesis's non-quasi-finite complement. The only elementary steps are the zero-factor base case and the final restatement of the induction conclusion.

The auxiliary node is self-contained and states only that a finitely generated algebra over a field has finitely many isolated spectrum points; it is intentionally `unsplit` because no exact Mathlib declaration was found. Its searches cover LeanSearch, Loogle, and Mathlib-source grep. The tensor node states the exact binary product equivalence and records `Mathlib/RingTheory/TensorProduct/Pi.lean:82-87`.

Whole-blueprint searches for the item and both child statements found no same statement (`same_as: []`). The child `blueprint.from` records the item's nearest ancestor and the exact 00UK induction clauses it serves. No attachment, source error, or wanted document was found. No Lean source was written or compiled.

## Attachments

None.

## WANTED

None.

## What was checked

The item was previously unsplit and had no proof. The proof now names every non-elementary dependency in its steps, keeps `proof_deps` equal to the union of step uses, and does not cite the item itself. The finite-factor induction is stated explicitly, including the base case, the decrease of the fibre-point count, and the final product regrouping. Existing source declarations 00UJ and 00UL were checked; neither is an exact attachment for the finite-type 00UK statement.

## Remaining

The finite-isolated-point auxiliary node remains for a later stage-1 worker. The child records and item are otherwise complete for delivery; no source checkout build is required or permitted at this stage.
