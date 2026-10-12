## What changed

Proved `AlgebraicGeometry.Scheme.Modules.single_field_fibre_homology` in
`lean/Sheaf/AlgebraicGeometry/FieldFibreHomology.lean`, without changing its signature or
public imports. Added three fully proved private helpers: `flat_of_finiteLocallyFree`,
`flat_complex_pullback_iso`, and `flat_single_pullback_iso`.

The proof uses the planned `flatComplexDerivedPullback` comparison twice, first for P
and then for the flat single complex on its sole cohomology sheaf. Mathlib truncation
identifies Q(P) with a single complex; homology functor comparisons transfer the
vanishing and rank assertions back to the termwise pulled-back complex. Tensor pullback
and the ordinary pullback are identified using their adjunctions, including equality
of the specified termwise functor on objects and maps.

Added proof-only imports of `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`,
`Sheaf.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact`,
`WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank`,
`Mathlib.Algebra.Homology.DerivedCategory.TStructure`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`, and
`WeilConjectures.CategoryTheory.Abelian.Flat.Basic`.
Updated the item's node proof, proof_deps, and proof_origin to match this argument.
No definition, public interface, target, or other module was changed.

Single-file lcompile passes with no warnings. The delivery dry run supplies the final
static and axiom-probe checks. Edge cases require no additional hypotheses: support
provides all negative vanishing, and the single-complex identities include rank zero,
the empty scheme, and i outside the given support.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.single_field_fibre_homology`
(node `new-field-fibre-homology`). Proved 1 of 1 original sorries; added 0 holes and
split off 0 statements. No sorry remains in the delivered module. All three private
helpers have complete Lean proofs. Existing imported declarations remain the library's
responsibility; none were copied or modified in this delivery.

## No longer needed

No original import, planned proof dependency, node, or module was pruned. The planned
`lem-pc-flat-complex-derived-pullback` is retained and used twice. An exploratory
explicit import of `Mathlib.Algebra.Homology.SingleHomology` was removed because its
required declarations are already available through the retained Mathlib imports.
No global module-unreachability claim is made.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof text said that flatness preserves single cohomology and
rank after tensoring to a field. The map to a field need not be flat: for example a
residue field over a local ring is generally not flat. The relevant flatness is that
of the finite free terms and of the sole locally free cohomology sheaf. The derived
single-object argument supplies the missing justification without assuming f flat.
The field hypothesis is unnecessary for this argument, but its binder and the entire
existing signature are preserved. The proof supplies the negative vanishing from
hge before applying integer-graded truncation.

The unit's route is preserved: this is the forward derived-fibre comparison used in
proof step 4 of the perfect-locus argument; it retains the bounded-flat comparison
and does not bypass any unit-realizing statement or step.

## Second reading by X2

1. **Visible changes and statements.** Compared the delivered module with the repository version. The public theorem signature of `single_field_fibre_homology` is byte-for-byte unchanged, and the added declarations are private proof helpers. No target or existing public declaration was altered.

2. **Proof and axioms.** Compiled `lean/Sheaf/AlgebraicGeometry/FieldFibreHomology.lean` with `lcompile.py`; it succeeds without warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses bounded flat derived-pullback comparison and the single-complex homology identities; no flatness of the map to `Spec R` is assumed. The delivery probe is required to perform the final axiom check.

3. **Statements and searches.** There are no split-off statements or new public nodes in this delivery. The existing node `new-field-fibre-homology` matches the theorem declaration and records the proof route and searches. The edge cases described in the report (rank zero, empty scheme, and indices outside support) are covered by the zero-object and single-complex lemmas.

4. **Pruning and route.** All retained imports are used by the proof or its stated dependencies; the exploratory `SingleHomology` import was removed. The bounded-flat comparison and tensor-closed route required by the unit is preserved, including both applications to the original and single complexes. No unit-realizing node was bypassed and no unrelated module was changed.

5. **DAG agreement.** The node proof steps, dependencies, and origin agree with the Lean proof. The node remains attached to `sk-thm-picard-perfect`; no new holes were introduced. The only change made in this second reading is this report section documenting the checks above.
