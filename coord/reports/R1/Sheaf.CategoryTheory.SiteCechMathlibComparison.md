## What changed

Replaced `mathlib_complex_iso_exists` with a complete universal-property proof. The proof
constructs the chosen fibre-product fan in `Over U`, compares it to Mathlib's categorical
product, compares products of sections to section tuples, and verifies compatibility with
all index maps and the alternating differential. The second reading added the proof-only import
`Mathlib.Algebra.Category.Grp.Biproducts` and reused its product limit cone. No import
was removed; existing public imports are required to elaborate the statement.

## Proved and sorry left

The declaration `CategoryTheory.SiteCechComplex.mathlib_complex_iso_exists` is proved.
Holes closed: `CategoryTheory.SiteCechComplex.mathlib_complex_iso_exists` (1 of 1).
Holes added: none. No `sorry` remains in the delivered module and no new node was added.
The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`, as checked by
`#print axioms` in a scratch copy.

## No longer needed

None. The existing imports are used by the statement or proof.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was accurate. The node
`lem-weil-pbc-site-cech-mathlib-comparison` has an updated `proof_origin.note` recording
the realized proof; its proof steps and `proof_deps` remain accurate. The comparison can be implemented directly using Mathlib's
`Fan.IsLimit`, `conePointUniqueUpToIso`, and `Pi.mapIso`; no additional intermediate theorem
or dependency node is required.


## Second reading by R1

1. PASS: Compared the entire delivered module against the repository using `diff`.
   The sole existing declaration, `mathlib_complex_iso_exists`, retains its signature
   byte for byte, including all universes, the finite-wide-pullback hypothesis, the
   arbitrary family, and the arbitrary abelian presheaf. Its docstring and the public
   imports are unchanged. New helpers are private and occur only in the proof.
2. PASS: Compiled the original worker proof cleanly with `lcompile.py`, then compiled
   the shortened version in a scratch copy. `#print axioms` for the main theorem shows
   exactly `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, forbidden
   axiom mechanism, or hollow definition. The choice in `chosenFanIsLimit` is from the
   unique lift supplied by `S.universal`, whose uniqueness is explicitly used.
3. PASS: No statements are split off and no holes or nodes are added. The private
   comparison facts are proved. Reviewed the empty-index case (no positive-length
   tuples), degree zero (one-factor products), and arbitrary index maps (including
   repeated factors): all are covered by the universal-property argument without
   a nonemptiness or injection hypothesis.
4. PASS, with simplification: Searched Mathlib using Loogle for
   `AddCommGrpCat.HasLimit.productLimitCone` and read its source in Grp/Biproducts.lean;
   also searched the library for product cones and Cech isomorphisms. Replaced the
   hand-built tuple-group limit cone with this existing Mathlib cone, saving its
   explicit lift/factorization/uniqueness proof. The new import is proof-only. The
   other two comparisons still require the chosen-product universal property and
   compatibility calculations. All existing imports are needed for the theorem's
   types or their instances, so no dependency is pruned. Read
   `dag/units/sk-thm-p1.json`, including `realized`: this is a tool comparison below
   the unit route and changes none of its statement or steps.
5. PASS: Read the node and the Lean module together. The three proof steps are
   implemented by `productIso`, `degreeIso`, and `degreeIso_indexMap` plus
   `differential_sum`, respectively. Both existing proof dependencies remain used;
   none is newly bypassed. Updated only `proof_origin.note` to describe the actual
   formalization and the second reader's Mathlib simplification.

Changed by the second reading: replaced the tuple-product helper's explicit limit
construction with Mathlib's `productLimitCone`, added its proof-only import, updated
proof-origin metadata, and made the hole accounting and this review explicit.
