## What changed

Proved `AlgebraicGeometry.ProEtale.finiteRingRelativeScalarComparison` without changing
its statement or the definition of `finiteRingScalarDirectImageMate`. The proof descends
constructible cohomology with finite constant models, applies the existing bounded
constructible origin theorem, reflects a Tor interval, applies the module-valued relative
cohomological-dimension theorem and finite-constant projection formula, and transports the
normalized scalar mate to the pro-etale site. The final naturality step transports its
invertibility to the given K.

Proof imports use the already proved private helpers of
`Sheaf.Paper.FiniteCoefficientDirectImage` and
`Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula` through `import all`.
No source-library file changes and no new declarations are needed.
The exact original theorem signature and scalar-mate definition are preserved.
The item node's proof and dependencies now record this implemented route.
Import pruning is recorded in
`coord/changes/K9-finite-ring-relative-scalar-comparison-imports.md`;
there are zero downstream Lean modules and no consumer adaptations.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.finiteRingRelativeScalarComparison`
(node `lem-sfb-finite-ring-relative-scalar-comparison`), the module's single original hole.
Added holes: none. Sorries left in the delivered module: none.
The proof uses published dependencies whose own postponed proofs remain in their modules;
this does not claim an axiom-free transitive closure.

## No longer needed

The coefficient-sized-model route through `det-pe-finite-tor-comparison-noetherian`
and `lem-sp-etale-scalar-flat-model` is unnecessary here: fixed-module constructible
origin and Tor reflection provide exactly the antecedent required, and the scalar/tensor
comparison directly proves the scalar extension's lower bound. Thus no Noetherianity
of X or Y is needed in the proof. The discarded geometry steps involving properness,
closed immersions, finite-type cancellation and finite type over a Noetherian base
are unnecessary beyond the quasi-compactness and separatedness cancellations retained.

The abelian-sheaf detour through `lem-sbc-higher-direct-image-forget-comparison` and
unpacking `def-kun-cd` is replaced by the existing proved module-valued implementation
`Etale.hasFiniteCohomologicalDimensionMorphism` of relative 0F10. K-flat resolution
and change-of-rings computations are already encapsulated in the existing proved
scalar/tensor and projection helpers; no separate direct import or use of
`lem-pc-kflat-resolution`, `lem-pur-derived-change-of-rings`,
`lem-pur-change-of-rings-tensor-comparison` or
`lem-weil-pbc-exact-functor-complex-cohomology` is needed by this proof.

Direct imports removed (some remain available transitively; the projection module is
retained as an `import all` proof import):

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.ScalarPullbackRepresentativeData
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.AlgebraicGeometry.EtaleScalarFlatModel
import Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.EtaleUnboundedRestrictionComparison
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
```

Obsolete top-level `tool_uses` approvals removed (retained approvals keep their order):
`lem-weil-pbc-finite-type-over-noetherian`,
`det-pe-finite-tor-comparison-noetherian`,
`lem-sp-etale-scalar-flat-model`,
`lem-sbc-higher-direct-image-forget-comparison`,
`lem-weil-pbc-exact-functor-complex-cohomology`,
`lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`,
`lem-pur-change-of-rings-tensor-comparison`.

Only dependencies of this item are pruned; no module is withdrawn and no claim is made
that these nodes have become globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original plan's Noetherian finite-Tor comparison is stated in coefficient site-model
categories, whereas this item's signature uses fixed ModuleCat-valued sheaves. Existing
fixed-module descent and Tor-reflection results give a shorter route. The original plan
also overlooked the existing module-valued relative cohomological-dimension theorem.
Neither issue requires a statement or definition repair. The unit's finite-ring route
through the etale origin and the relative projection formula is retained.

Edge cases: finite zero rings, empty schemes, the zero complex and empty Tor intervals
are covered by the used declarations. No coefficient flatness, finite projective
dimension, or absolute cohomological-dimension assumption is introduced.

Searches: leanfinder for finite-ring scalar extension and direct image returned only
unrelated algebraic etale lemmas; Loogle found `NatTrans.isIso_app_iff_of_iso` for the
final naturality transport; grep and local rg found the fixed-module descent,
Tor-reflection, relative cohomological-dimension, scalar lower-bound and projection
helpers used here.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
