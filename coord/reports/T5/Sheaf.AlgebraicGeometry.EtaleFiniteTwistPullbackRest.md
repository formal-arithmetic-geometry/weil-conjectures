## What changed

Replaced the proof hole of `AlgebraicGeometry.Scheme.etaleFiniteTwistPullback_rest`
with a construction of its derived comparison and exponent-change isomorphisms.
Private helpers establish the roots-of-unity cokernel property, the coefficient-line
Hom adjunction, invertibility of the induced line map, and signed tensor/dual extension.
Added proof imports `Mathlib.CategoryTheory.Abelian.Refinements` and
`Mathlib.Algebra.Homology.ShortComplex.Exact` for the cokernel argument.
Updated the existing node to record this proof route. Public signatures are unchanged.
Added `coord/changes/etale-finite-twist-pullback-rest-proof-commands.md` to record the
file-local universe, option and namespace-opening commands conservatively flagged by
preflight. The record inventories all downstream consumers; no adaptation is needed.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.etaleFiniteTwistPullback_rest`
(node `lem-asd-etale-finite-twist-pullback-rest`). The complete module compiled against the current published build in
10.0 seconds on the resumed attempt of 2026-10-19. Zero `sorry` declarations remain; zero holes added and zero statements
split off. The roots-of-unity cokernel, line-adjunction and signed-power helpers are
all proved in this module. The theorem's signature is textually unchanged. On the latest resumed attempt (2026-10-19), the required dry run passed in full:
commit `c9b51eeade` compiles and passes preflight, classified CODEX for the node
update, change record, and file-local command changes. Nothing was pushed by that dry run.

## No longer needed

Removed proof imports:

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable`
- `Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale`
- `Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction`
- `WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction`
- `WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The local primitive-root cover, representability, jointly surjective cover detection,
ordinary inverse-image coherence, and generic ringed-topos tensor packages are not
needed for this remaining package. The derived clause uses the existing scheme-level
monoidal comparison, and exponent change uses Kummer exactness and adjunctions.
The prior proof dependencies `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`def-pc-tensor-complex-sheaves`, and
`lem-weil-pbc-left-exact-site-inverse-image-tensor` are not applied directly here;
the first two remain available through the unchanged statement imports.
No module files are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old docstring and proof plan described local trivialization and abelian coherence
already assigned to the sibling base package. The remaining theorem only requires
the explicit derived component formula and exponent change. The updated docstring
and node explain those arguments. The retained proof had unresolved elaboration
errors. The continuation repaired the
kernel-map arithmetic and universal-property packaging, made the common coefficient
unit explicit in the dual evaluation calculation, and typed the derived tensor
comparison explicitly. Its component equation now keeps tensor functors folded and
uses an explicit identity cancellation and functoriality calculation. The compile
server intermittently returns no answer: the first resumed dry run received no
answer within 184 seconds. A subsequent direct compile passed in 10.0 seconds.
Earlier direct and delivery-probe runs also compiled the complete proof.
The base-package parameters `r` and `p` remain in the unchanged signature and are
explicitly referenced and then cleared because neither remaining clause needs them.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
