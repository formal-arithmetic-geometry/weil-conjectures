/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionDerivedTensorComparison
public import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.SixFunctors.SfbHomFilteredColimit.DerivedInternalHomFilteredColimitData
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTotalComparison


/-! # Normalized internal-to-section Hom comparison data

Source: Stacks Project, Tags 08J9, 0A95, 03EK, 07A4 and 07A6; the agent
presentation-transport argument in the DAG
(blueprint: def-sfb-internal-section-scalar-hom-transport-data).

The continuity arrows below are termwise colimit arrows of whole functorial
representative systems. They are not colimits formed in a derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- Avoid unresolved maximum universes in unrelated imported coefficient instances.
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures
open scoped CategoryTheory.Obj
open CategoryTheory.InternalAbelianSheafModule

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local irreducible] Sheaf.monoidalCategory

attribute [local irreducible] CondensedRing.derivedHom CondensedRing.derivedTensor
  CondensedRing.internalScalarTensorIso
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

attribute [local instance] isCommMonObj_condensedRingObj

universe a₀ b₀ a₁ b₁


variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

-- Reuse the concrete section-derived instances from the comparison data module.
-- Their instance attributes are local there, so consumers must enable them again.
attribute [local instance] localProEtModulesHasDerivedCategory
  localProEtScalarHasDerivedCategory

section Scalar
variable {X}
variable {Λ}
variable {Γ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}}
  [MonObj Γ] [IsCommMonObj Γ] (a : Λ ⟶ Γ) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap.{u} a Z))]

/-- The internal restricted comparison is the five normalized adjunction bijections
at the identity, using the native closed adjunction and scalar tensor comparison.
Source: Stacks 07A6, 08J9
(blueprint: def-sfb-internal-section-scalar-hom-transport-data). -/
def internalRestrictedHom (K : DerivedCategory.{u + 1} (Internal.{u} Λ X))
    (N : DerivedCategory.{u + 1} (Internal.{u} Γ X)) :
    (Mod.comap (coefficientMap.{u} a X)).mapDerivedCategory.obj
        (((CondensedRing.derivedHom.{u} Γ X).obj
          (op ((CondensedRing.internalScalarExtension.{u} a X).obj K))).obj N) ⟶
      ((CondensedRing.derivedHom.{u} Λ X).obj (op K)).obj
        ((Mod.comap (coefficientMap.{u} a X)).mapDerivedCategory.obj N) :=
  (CondensedRing.derivedTensorHomAdjunction.{u} Λ K).homEquiv _ _
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap.{u} a X)).homEquiv _ _
      (((CondensedRing.internalScalarTensorIso.{u} a X).hom.app K).app _ ≫
        ((CondensedRing.derivedTensorHomAdjunction.{u} Γ
          ((CondensedRing.internalScalarExtension.{u} a X).obj K)).homEquiv _ _).symm
          (((Mod.derivedExtendMapDerivedCategoryAdjunction
            (coefficientMap.{u} a X)).homEquiv _ _).symm (𝟙 _))))

variable (X)
  (M : ScalarHomModels.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X))
  (μ : ∀ {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (f : R ⟶ S),
    ScalarHomTensorComparison.{u + 1, u, u, u + 1} M f)
  (PΛ : HomPresentation.{u} Λ X (M.closed (ring.{u} Λ X)) (M.model (ring.{u} Λ X)))
  (PΓ : HomPresentation.{u} Γ X (M.closed (ring.{u} Γ X)) (M.model (ring.{u} Γ X)))

end Scalar

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
