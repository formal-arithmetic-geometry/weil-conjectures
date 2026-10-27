## What changed

Proved `AlgebraicGeometry.Etale.properFiniteCoefficientExtensionCore` with its complete
existing signature, both unbounded clauses, and every public import unchanged.
Only the item module and its own node are changed.

A proof-only `import all Sheaf.Paper.EtaleProperCoefficientTensorUnit` reuses two
already proved private helpers from that module:

- `proper_scalarMate_isIso` proves the first clause for every ambient derived object.
  It applies the finite proper projection formula, the invertible restriction/direct-image
  mate, and the homology criterion with conservative ordinary restriction of scalars.
- `scalar_projection_ambient` supplies the unbounded normalized projection equality.
  Its proof uses the normalized scalar/tensor pullback square and geometric counit mates;
  it imposes no boundedness witnesses.

The new proved private lemma `cancel_scalar_comparisons` is elementary category algebra:
substitute this equality, cancel the target scalar/tensor isomorphism, use functoriality,
and cancel the source scalar/tensor isomorphism. Applying it with the signed symmetry
maps gives exactly the ordered equality in the second clause. Proving this cancellation
abstractly avoids simplifier transparency problems in concrete derived tensor expressions.
No transparency option or timeout is changed. No new public declaration or definition is added.

The node now records this reuse and the actual projection and reverse-mate dependencies.
The generic reverse-mate result `lem-sfb-etale-proetale-scalar-mate` is used as a tool
for invertibility of the restriction/direct-image comparison; it replaces the previous
plan to reconstruct that comparison via a general pushforward-composition theorem.
No unit statement or unit proof step is bypassed.

Validation: the final item compiled cleanly through `lcompile.py` in 7.1 seconds,
with no warnings. The import-direction check confirmed that the helper module does
not reach this item, so the added proof import introduces no cycle.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.properFiniteCoefficientExtensionCore`
(node `lem-asd-proper-finite-coefficient-extension-core`).

Added 0 holes. The item module contains 0 remaining `sorry` declarations.
Both reused private helpers already have complete proofs. Existing downstream proof
obligations of the imported projection and normalization theorems are retained.
This is a proof from existing declarations, not a decomposition into new obligations.

## No longer needed

Removed these ten unused direct proof imports:

- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.TensorProjectionAdjunct`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`

The item no longer directly reconstructs the obligations of nodes
`lem-pc-kflat-resolution`, `lem-pur-derived-change-of-rings`,
`lem-pur-change-of-rings-tensor-comparison`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`, and
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`.
The first four remain dependencies of the existing normalization constructions, so
this is removal of redundant direct dependencies, not a claim that their mathematics
is globally unnecessary. The direct-image comparison uses the reverse scalar/pullback
mate instead of the general pushforward-composition route.

The reordered proper projection theorem `lem-amb-proper-coproducts-projection` is not
used in the proof: the reused helper already applies the underlying unbounded theorem
`lem-etale-proper-projection-formula-finite` before adding symmetries. Its original public
import is retained as part of the existing exported interface. No module is withdrawn;
no globally unreachable module is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned K-flat reconstruction had already been implemented in a later module.
The public `scalarMate_restrict_eq_projection` theorem retains bounded-below inputs,
but the proved private `scalar_projection_ambient` supplies precisely the needed
unbounded equality. Reusing it avoids either changing a shared public theorem or
splitting this obligation again.

The reused helpers require neither finiteness of the target coefficient ring nor
Noetherian hypotheses. The item keeps all its original assumptions. The argument
continues to apply to identity morphisms, zero rings, nonflat coefficient maps and
unbounded inputs: it uses derived functoriality and inverse equations only, and
introduces no flatness or boundedness condition.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
