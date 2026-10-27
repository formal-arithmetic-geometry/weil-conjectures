## What changed

Proved `AlgebraicGeometry.ProEtale.ClosedTest.closed_test_unit_evaluation` in
`Sheaf.Paper.ClosedTestUnitEvaluation`, preserving its signature and all existing definitions.
The private helper arguments construct the abelian/internal inverse-image comparison,
normalize the ordinary module comparison on its canonical unit, transfer weak
contractibility to the affine basis, and construct the closed-test comparison from
the inverse mate of the basis restriction square. Scalar compatibility uses the actual
internal unit and the identity-on-sections direct-image comparison. The inverse and
both naturality equations then follow from the normalized comparison.

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`,
`Sheaf.AlgebraicGeometry.ProEtaleModuleSpecializationUnit`,
`Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation`,
`Mathlib.CategoryTheory.Sites.DenseSubsite.Basic`,
`Mathlib.CategoryTheory.Sites.Pullback`, and
`Mathlib.CategoryTheory.Adjunction.Mates`; the actual dependencies provide the
remaining interfaces. The private sheaf-precomposition adjunction is proved over
arbitrary sites before its closed-site application, and continuity proofs are passed locally at
the basis comparison applications to avoid repeated geometric unfolding. The ordinary
module inverse-image construction and inverseSection remain opaque in the proof;
the existing private canonical-unit computation supplies their section equation.
Private instances cache continuity and equivalence of affine-basis restriction. Added private imports for unit coherence, the canonical module
unit and its comparison, specialization coordinates and abelian unit sections, the
source inverse-mate theorem, and ordinary module colimits/exact functors.

Updated the existing node's proof, proof dependencies and proof origin to describe
this route. No other library module, target, public signature or definition changes.
No new nodes or statement corrections. The complete module compiled cleanly through
`lcompile.py` in 45.5 seconds; all six existing definitions and the main theorem
signature were also checked byte-for-byte against the shared source.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.ProEtale.ClosedTest.closed_test_unit_evaluation`
(node `lem-sfb-closed-test-unit-evaluation`). No holes added or split off; no `sorry`
remains in the delivered module. The proof uses the existing named transport theorem
as intended by stage 3; this report does not claim its downstream holes are closed.

## No longer needed

The proof no longer directly uses these planned dependencies, and removes their old
`tool_uses` entries in the same order as the existing record:

- `lem-cbc-local-dense-ordinary-sheaves`: use the existing affine-basis restriction
  equivalence, rather than reconstructing it from a generic density theorem.
- `lem-weil-pbc-proetale-module-specialization-unit`: apply the proved abelian
  specialization-unit theorem and the explicit internal extension-unit comparison.
- `lem-weil-pbc-affine-closed-inverse-image-evaluation`: construct the comparison
  for abelian sheaves by the inverse mate of the restriction square; its equation
  with the actual unit follows directly from the mate and sheafification equations.
- `lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`: build the needed
  basis adjunction directly from precomposition and sheafification adjunctions.
- `lem-weil-pbc-conjugate-iso-unit-equation`: use Mathlib's mate unit equation
  and the proved source inverse-mate invertibility theorem.

These are removals from this node's direct proof route. In particular the existing
closed-site counit proof still imports the closed inverse-image evaluation module;
no upstream declaration or module is withdrawn or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The stated mathematical result and geometric plan need no correction. The existing
closed inverse-image evaluation statement is for set-valued sheaves and does not
itself give the required normalized comparison for abelian sheaves. Its underlying
basis-adjunction argument generalizes, and the mate unit equation supplies the
normalization explicitly. The local counit clause also requires the specialization
assertion transported to the global-section quotient coordinates; the existing
coordinate lemma supplies exactly this missing glue. Empty schemes and zero rings
require no extra assumption: the constructions and equivalence arguments apply
without nonemptiness.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
