## What changed

Proved `AlgebraicGeometry.SingleComplexBaseChange.affineSpectrum_composition_counit_square`
in `Sheaf.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare` by the recorded route.
The general composition factorization follows from `Functor.leftDerived_fac` for the
selected comparison. Equality induction transports it to the second affine path, and
`compare_counit_factorizations` cancels the composition isomorphisms. The termwise
comparison is normalized directly using functoriality.

Added only proved private helpers and a private shorthand for the exact composition
comparison already selected by `exists_derivedPullbackComposition`. Its universal
factorization determines that comparison; no arbitrary new witness is selected.
Public signatures, public definitions, imports, and module settings are unchanged.
Updated the item's two DAG proof steps and proof origin to describe the implemented proof.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.SingleComplexBaseChange.affineSpectrum_composition_counit_square`
(node `lem-pc-affine-spectrum-composition-counit-square`).

Sorries left in the item: none. Holes added: none. Statements split off: none.
All added private helpers are proved; this is a proof from the existing library
composition theorem, not a decomposition into new unproved statements.

## No longer needed

Imports removed: none. Nodes and modules pruned: none. All three original public
imports occur in the statement, and all four original proof dependencies remain used.
The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The implementation follows the original two-step plan.
Lean elaboration required explicit localization universes, normalization of functor
composition on objects, and rewrites focused on the appropriate side of the equation.
No statement correction or forced adaptation was needed.

## Second reading by H2

1. Compared the complete delivered module with the repository version and checked all
   existing declaration statements and visibility using the delivery parser: byte-identical.
   Existing definitions, module settings, docstrings and imports are unchanged. Pass.
2. Read the entire module and compiled it locally with lcompile.py: no errors or warnings
   (56.3 seconds). No sorry, forbidden declaration, or hollow definition occurs. The
   selectedComposition shorthand is exactly the composition family used by the existing
   affineSpectrumDerivedPullbackIso, with its hom specified by the leftDerivedLift equation;
   it introduces no arbitrary existence witness. The scratch axiom check is recorded below.
3. No statements were split off and no new holes or nodes were added. All new private
   lemmas have complete Lean proofs. Checked cancellation and equality transport directly:
   neither requires an invertible counit, K-flatness, nonzero complexes or nonempty schemes.
   Pass.
4. Checked Mathlib LeftDerived.lean (leftDerived_fac, leftDerived_fac_app and leftDerived_ext),
   the existing derived-composition theorem, and neighboring termwise-coherence modules.
   The proof already uses the universal factorization directly; no shorter existing square
   was found by local search and a fresh Loogle search. All three public imports provide
   symbols in the original public statement. All four old proof dependencies remain used,
   so the no-longer-needed list is complete. The unit realized record and its route are
   unchanged. Pass.
5. Compared the node JSON: only proof and proof_origin changed. Its two steps and dependency
   union match the implemented factorization, transport, and cancellation argument. The
   statement, Lean record, chapter, unit and blueprint are unchanged. Pass.

Changes by the second reader: no Lean or DAG repair was needed; added this review and
independent verification to the report.

Independent scratch `#print axioms` check passed (58.5 seconds):
`AlgebraicGeometry.SingleComplexBaseChange.affineSpectrum_composition_counit_square`
depends only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
