/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Mathlib.Algebra.Homology.HomologicalComplexLimits

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
/-! # Koszul reconstruction of a derived-complete reduction tower

Source: Stacks Project, algebraization.tex Tag 0A0E and sites-cohomology.tex Tag 0941
(blueprint: lem-pur-derived-complete-koszul-reconstruction).

The strict towers and quotient maps are the canonical constructions of
`def-pur-principal-koszul-quotient-towers`. Total right derived inverse limit is
provided by the recorded strict-tower homotopy-limit dependency.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
variable {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "𝓞" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "𝒜" => ringedSiteModules.{r} 𝓞

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem principalAugmentation_quasiIso
    (t : (SheafOfModules.unit 𝓞).sections)
    (hreg : Mono (globalSectionMultiplication R t)) (m : ℕ) :
    QuasiIso (principalAugmentation R t m) := by
  have hp (n : ℕ) : Mono (endoPow (globalSectionMultiplication R t) n) := by
    induction n with
    | zero => change Mono (𝟙 _); infer_instance
    | succ n hn => change Mono (endoPow _ n ≫ _); infer_instance
  let f := endoPow (globalSectionMultiplication R t) (m + 1)
  have : Mono f := hp (m + 1)
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have : PreservesFiniteLimits (CochainComplex.singleFunctor 𝒜 0) :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single 𝒜 (.up ℤ) 0))
  have : PreservesFiniteColimits (CochainComplex.singleFunctor 𝒜 0) :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single 𝒜 (.up ℤ) 0))
  have hSC := hS.map_of_exact (CochainComplex.singleFunctor 𝒜 0)
  exact CochainComplex.mappingCone.quasiIso_descShortComplex hSC

variable [HasDerivedCategory.{w} 𝒜]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ 𝒜)]

/-- Total right derived inverse limit supplied by the strict-tower dependency. The defining
universal property determines this functor up to unique natural isomorphism.
Source: Stacks Tag 0941 (blueprint: lem-pur-derived-complete-koszul-reconstruction). -/
noncomputable def koszulRlim : DerivedCategory.{w} (ℕᵒᵖ ⥤ 𝒜) ⥤ DerivedCategory.{w} 𝒜 :=
  Classical.choose (ringedStrictTowerHomotopyLimitIndependentCoefficients J 𝓞
    (fun U a b ↦ @mul_comm (R.obj.obj U) _ a b))

/-- The derived strict Koszul completion, using the total right derived inverse limit.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-derived-complete-koszul-reconstruction). -/
noncomputable def koszulCompletion (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) : DerivedCategory.{w} 𝒜 :=
  (koszulRlim R).obj (DerivedCategory.Q.obj
    (koszulTowerComplex R (koszulTensorTower R P t)))

set_option maxHeartbeats 1000000 in
-- Destructing the strict-limit universal property elaborates its full dependent interface.
end CategoryTheory
