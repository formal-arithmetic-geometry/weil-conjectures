/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AllContinuousScalarMate
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.RingedProjectionFirstShift
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.ScalarModelImmersionExtension
import WeilConjectures.AlgebraicGeometry.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.KFlatScalarComparisonNormalization
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.AlgebraicGeometry.TameBoundaryScalarComparison

/-!
# Open direct image and all-continuous algebraic-closure scalar extension

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), the separate all-continuous coefficient comparison obligation
(blueprint: lem-sfb-continuous-algcl-open-scalar-comparison).

The arrow is the existing normalized counit mate, and both sides live in the ordinary
ambient module derived category. The input has finite constant scalar models. The
coefficient ring on the target is C(-, PadicAlgCl ell) for its norm topology.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical counit mate for a quasi-compact open immersion is invertible on bounded
constructible finite-field-coefficient inputs with finite constant scalar models.
Source: blueprint main-20261015, direct-image proof paragraph (3), all-continuous
compatibility obligation (blueprint: lem-sfb-continuous-algcl-open-scalar-comparison).

Proof, following the five DAG steps:
1. Define every beta by the normalized scalar/pullback square and the geometric counit.
Restriction from B to A_E reflects isomorphisms and commutes with derived direct image
(lem-weil-pbc-ring-sheaf-change-adjunction). The K-flat scalar-adjunction formula of
lem-pur-sheaf-ring-derived-coefficient-adjunction identifies its underlying arrow,
after tensor symmetry, with the projection morphism with fixed module B_X. By
lem-sfb-ringed-projection-first-shift this arrow respects shifts and connecting maps;
lem-sf-triangle-two-out-of-three gives triangle closure of its isomorphism locus.
2. Zero, finite sums and isomorphic objects stay in that locus. For a retract C of G
with maps i and r, naturality gives the inverse F(r) beta_G^{-1} H(i), where
F = T_X Rj_{*,A_E} and H = Rj_{*,B} T_U. The theorem
lem-sfb-tame-pair-proper-generators now reduces to G = Rq_* K on a regular tame pair,
with proper maps p and q, inverse-image open j', and K = (b_! L)[0].
3. The lisse module L is locally finite free over E and hence has a finite constant
model. By lem-sfb-scalar-model-immersion-extension, K is bounded constructible.
The finite-E clause of lem-sfb-rational-open-direct-image-constructible gives the
same property for Rj'_* K. This checks both proper-comparison inputs.
4. The K-flat comparison of lem-sfb-kflat-scalar-comparison-normalization identifies
beta with the mate of the inverse normalized pullback square. Its coherence and the
adjunction-compatible compositors of lem-sfb-ringed-derived-monoidal-comparisons
allow lem-weil-pbc-mate-pasting to give beta_fg = Rf_*(beta_g) followed after beta_f.
For jq = pj' this yields Rj_*(beta_q) beta_j = Rp_*(beta_j') beta_p, with the same
normalized derived-direct-image compositors on both sides.
5. Apply lem-sfb-continuous-algcl-proper-scalar-comparison to p and q using step 3.
Apply lem-sfb-continuous-algcl-tame-boundary-comparison to j' using the generator's
regular tame-pair data. The right side of the equality in step 4 and the factor
Rj_*(beta_q) are invertible, so beta_j is invertible for G. Steps 1 and 2 finish
for C. This proves invertibility of the specified mate without asserting that its
all-continuous-coefficient source or target is constructible. -/
theorem continuousAlgClOpenScalarComparison_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime] (_hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) U)))
    (_hC : constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) U C) :
    IsIso (tameBoundaryScalarComparison ℓ E j C) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
