## What changed

Restored `AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorComplexHom_comm`
using the canonical termwise tensor isomorphism. A proved private summand formula
identifies its degree components with the components already defined upstream.
The chain-map equation then follows from the hom component of that isomorphism.

Added the private proof import
`WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex` and the proved
private helper `mapCochainComplexμIso_hom_f_eq_desc`. Private proved instance shortcuts and local reducibility settings keep the
concrete instance search within the file time limit. The module tensor definitions
are made transparent again before the explicit unit comparison. Existing public
imports, signatures, declaration attributes and non-sorry definition data are preserved. No other
module is adapted. The maintainer should preserve this import and helper during
future upstream syncs using the appropriate exception record; this worker has
not edited the exceptions table.

## Proved and sorry left

Closed one of the ten original sorry expressions, in
`AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorComplexHom_comm`
(node `lem-sfb-upper-star-tensor-complex-comparison-chain-map`). Added zero holes;
zero statements are split off.

Nine existing holes remain, all in namespace
`AlgebraicGeometry.ProEtale.CondensedRing`:

- `upperStarTensorCounit`: two naturality fields
  (`def-sfb-upper-star-tensor-counit`).
- `isLeftDerivedFunctor₂_upperStarTensor`: one
  (`lem-sfb-derived-pullback-tensor-left-derived`).
- `leftDerivedUpperStarTensorLeftCounit`: two naturality fields
  (`def-sfb-derived-pullback-tensor-left-counit`).
- `isIso_leftDerivedUpperStarTensor`: one
  (`lem-sfb-derived-pullback-tensor-comparison-iso`).
- `monoidal_leftDerivedUpperStar`: three coherence fields
  (`lem-sfb-derived-pullback-strong-monoidal`).

Validation: the complete delivery file compiles in 42.3 seconds with no errors
or warnings. The delivery preflight is the final check.

The preferred archive's full restoration was attempted with the current data
preserved, but those candidates did not pass the single-file 60-second check.
Those experimental candidates are not part of this delivery.

## No longer needed

No original public import or declaration is removed and no module is withdrawn.
The chain-map proof no longer directly uses the old planned proof dependencies
`def-weil-pbc-category-colimit`, `def-sfb-preserves-kflat-quasi-iso` or
`def-sfb-strong-monoidal-functor`: their component calculation is supplied by
`lem-sfb-termwise-strong-monoidal`. These nodes still have other uses; this is
pruning of this proof route only. The statement dependencies are preserved.

The compatibility module
`Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`
cannot be imported here because it imports this item. Its declarations are
preserved; none is claimed to be globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The preferred file cannot be copied wholesale under the current source-library
boundary: it replaces definition data and introduces public declarations. This
restoration instead fills only the chain-map proof and introduces a proved
private helper. The chain-map DAG route is updated to the canonical termwise
comparison; no target statement changes and the unit route is retained.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
