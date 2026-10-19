## What changed

Proved `AlgebraicGeometry.Scheme.sfAmbientCompactSupport_preservesCoproducts_and_hasAmbientDatum_of_fullCD`
in `lean/Sheaf/AlgebraicGeometry/FullCdAmbientAdjoint.lean`, with its complete existing signature,
universes and public import surface preserved. Updated its proof-in-words docstring and its node's
proof route. Added only private, proved local helpers; no definition or intermediate public
statement was changed, and no consumer adaptation or change record is necessary.

The proof transports FullCD to fixed-scalar sheaves, applies the existing qcqs
coproduct/injective-sum acyclicity theorem and finite-CD criterion, then Brown representability.
It transports the adjunction to intrinsic coefficients and composes with the open adjunction.
For comparisons, it combines proper/open support with open base change, the clopen section,
and derived pushforward composition obtained by adjoint uniqueness. A common refinement gives
an isomorphism between every candidate and the distinguished one. Transporting the one adjunction
along these isomorphisms, with a constant right-adjoint family, proves all datum equations.
All choices here are among proved isomorphisms or chosen adjoints; no arbitrary data are chosen
from an unproved mere-existence theorem.

New direct proof imports are:

- `Sheaf.AlgebraicGeometry.ProEtaleGrothendieckSectionCoproducts`
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`
- `Sheaf.CategoryTheory.FiniteCohomologicalDimensionInjectiveCoproducts`
- `WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp`
- `WeilConjectures.Compactification.Cofiltered`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale`

The conditional FullCD/Brown existence-unit route remains in place. The unit's `realized` lists
are empty; none of its mandated statement or step realizations is bypassed.

Validation: the authorized single-file server compiler accepted the completed proof in 14.3 s;
its sole docstring whitespace warning was corrected, and a clean verification passed in 56.0 s.
The original signature was compared verbatim; no Lean line exceeds 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.sfAmbientCompactSupport_preservesCoproducts_and_hasAmbientDatum_of_fullCD`
(node `lem-sp-fullcd-ambient-adjoint`).

Added 0 holes; split off 0 statements. There are no `sorry`s left in any delivered Lean file.
This proves the item from existing declarations, as required by stage 3; existing imported
obligations, including normalized intrinsic realization and proper/open support, are not
claimed proved by this delivery. All private helpers and the final combining proof are complete.

## No longer needed

Removed these direct proof imports (the public statement imports are preserved):

- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Mathlib.Algebra.Category.Grp.AB`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `Mathlib.Algebra.Category.Ring.Limits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact`
- `Mathlib.CategoryTheory.Limits.Preserves.Finite`
- `Sheaf.CategoryTheory.KInjectiveComputes`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`
- `Sheaf.Paper.ProfinitePointPullback`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.CategoryTheory.Abelian.RightDerived`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.Compactification.CategoryBaseChange`
- `Mathlib.CategoryTheory.Adjunction.Basic`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.Paper.FiniteDirectImageComposition`
- `Sheaf.Paper.RingedProjectionRestriction`
- `Sheaf.Paper.SfCommonStageDirectImage`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`

The shorter proof does not use the following former direct DAG dependencies:

- `def-weil-derived-direct-image`
- `def-weil-extension-by-zero`
- `def-weil-pbc-constant-sheaf`
- `def-weil-pbc-proetale-site`
- `lem-cbc-proetale-extension-zero-base-change`
- `lem-kun-finite-cd-acyclic-complex`
- `lem-kun-grothendieck-derived-coproducts`
- `lem-pc-right-derived-functor-triangulated`
- `lem-pur-kinjective-degreewise-existence`
- `lem-pur-kinjective-restrict-localized`
- `lem-pur-ringed-site-grothendieck-abelian`
- `lem-sp-kinjective-computes`
- `lem-weil-derived-direct-image-composition`
- `lem-weil-extension-by-zero-exact`
- `lem-weil-pbc-adjunction-of-natural-bijection`
- `lem-weil-pbc-condensed-qcqs-pushforward-continuity`
- `lem-weil-pbc-derived-functor-injective-vanishing`
- `lem-weil-pbc-profinite-point-pullback`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-ringed-projection-restriction`
- `lem-weil-proetale-module-direct-image-left-exact`
- `lem-weil-proetale-weakly-etale-localization`

These are direct-dependency removals, not a claim that every named module leaves the entire
target import closure. Generic abelian, derived and site infrastructure remains available
through the retained interfaces. The categorical qcqs theorem replaces the condensed-coefficient
continuity/point-pullback argument. The proved finite-CD injective-sum criterion packages the
acyclic-complex/coproduct infrastructure. Derived pushforward composition follows from adjoint
uniqueness rather than the finite-direct-image composition module. Ordinary weakly-etale
base change and exact descent replace the separate localized restriction and extension-zero
base-change wrappers. Taking the derived mate handles restriction without a separate
K-injective-restriction proof. Choosing comparisons to a fixed candidate avoids individual
geometric comparison coherence, equalizing parallel refinements, and independence of each
chosen common refinement. Only existence of a common refinement is used.

Removed obsolete entries of the existing `tool_uses` approval list only; no approvals added.
No module is withdrawn or deleted by this delivery.

## Where the brief, the DAG or earlier work was wrong

The former proof plan imposed coherence of the individual geometric refinement comparisons,
which is stronger than the actual `SfAmbientExceptionalRightAdjointDatum` fields. Those fields
require coherent natural isomorphisms but do not prescribe them to be the geometric maps.
The fixed-candidate construction satisfies every field without that extra obligation. This
changes the proof route only, not the target statement or the definition of the datum.

The FullCD hypothesis already contains exactly the original-source vanishing needed here;
its pro-etale-base-change conjunct is retained in the statement but is unnecessary for this
implication. There is no assertion of FullCD for arbitrary proper morphisms.

Earlier attempts were blocked before elaboration by a missing published RefinementCategory
object file. The dependency is now available: the retained full proof has compiled. There was
no report or completed delivery at resumption, so no interrupted delivery mutation was repeated.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
