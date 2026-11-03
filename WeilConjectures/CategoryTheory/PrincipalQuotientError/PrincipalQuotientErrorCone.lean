/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-! # Principal regular quotient error cones

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-tower/sk-lem-sp-tower.proof.md, second paragraph, first two sentences
(blueprint: lem-sp-principal-quotient-error-cone).

The existing principal quotient at index `n` is `R/t^(n+1)R`. All indices below
use this convention. The two-term cone is the unit-normalized model of
`A_n ⊗ K_m`. Every map is constructed from cokernels, single complexes and cones.
-/

@[expose] public section

set_option autoImplicit false

set_option backward.defeqAttrib.useBackward true

universe u v r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PrincipalQuotientError

open Opposite

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

variable (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
  R)).sections)

set_option hygiene false in
local notation "𝓞" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance] SheafOfModules.symmetricCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

set_option linter.style.haveILetI false in
/-- Multiplication by the given global section on a module sheaf.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def scalar (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
  RingCat.{r})).obj R)) : M ⟶ M :=
  ⟨PresheafOfModules.sectionsSMul M.val ⟨t.val, t.property⟩⟩

/-- The canonical projection to the existing principal quotient.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def projection (n : ℕ) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⟶
      principalQuotient R t n :=
  cokernel.π (endoPow (globalSectionMultiplication R t) (n + 1))

private lemma endoPow_add {D : Type*} [Category* D]
    {X : D} (f : X ⟶ X) (a b : ℕ) :
    endoPow f (a + b) = endoPow f a ≫ endoPow f b := by
  induction b with
  | zero => simp [endoPow]
  | succ b ih =>
      change endoPow f (a + b) ≫ f = endoPow f a ≫ (endoPow f b ≫ f)
      rw [ih, Category.assoc]

private lemma scalar_naturality
    {M N : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj R)} (f : M ⟶ N) :
    scalar R t M ≫ f = f ≫ scalar R t N := by
  apply SheafOfModules.hom_ext
  exact (PresheafOfModules.sectionsSMul_naturality f.val ⟨t.val, t.property⟩).symm

private lemma scalar_unit :
    scalar R t (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj R)) = globalSectionMultiplication R t := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let x : R.obj.obj U := x
  change (@id (R.obj.obj U) (t.val U)) * x = x * (@id (R.obj.obj U) (t.val U))
  exact mul_comm _ _

private lemma endoPow_naturality {D : Type*} [Category* D]
    {X Y : D} (a : X ⟶ X) (b : Y ⟶ Y) (f : X ⟶ Y)
    (h : a ≫ f = f ≫ b) (k : ℕ) :
    endoPow a k ≫ f = f ≫ endoPow b k := by
  induction k with
  | zero => simp [endoPow]
  | succ k ih =>
      change (endoPow a k ≫ a) ≫ f = f ≫ (endoPow b k ≫ b)
      rw [Category.assoc, h, ← Category.assoc, ih, Category.assoc]

private lemma projection_scalar (n k : ℕ) :
    projection R t n ≫ endoPow (scalar R t (principalQuotient R t n)) k =
      endoPow (globalSectionMultiplication R t) k ≫ projection R t n := by
  apply (endoPow_naturality _ _ _ _ k).symm
  rw [← scalar_unit R t]
  exact scalar_naturality R t _

/-- The higher power vanishes after projection to a lower quotient.
Proof: write n+1=(n-m)+(m+1), then use the cokernel relation.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem quotient_zero (n m : ℕ) (h : m ≤ n) :
    endoPow (globalSectionMultiplication R t) (n + 1) ≫ projection R t m = 0 := by
  rw [show n + 1 = (n - m) + (m + 1) by omega,
    endoPow_add, Category.assoc]
  change _ ≫ (_ ≫ cokernel.π _) = 0
  rw [cokernel.condition, comp_zero]

/-- The canonical quotient transition from level n+1 to level m+1.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def quotientMap (n m : ℕ) (h : m ≤ n) :
    principalQuotient R t n ⟶ principalQuotient R t m :=
  cokernel.desc _ (projection R t m) (quotient_zero R t n m h)

/-- The formula t^(n-m)x descends from the level-m quotient.
Proof: multiplying a t^(m+1)-multiple by t^(n-m) gives a t^(n+1)-multiple.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem raise_zero (n m : ℕ) (h : m ≤ n) :
    endoPow (globalSectionMultiplication R t) (m + 1) ≫
      (endoPow (globalSectionMultiplication R t) (n - m) ≫ projection R t n) = 0 := by
  rw [← Category.assoc, ← endoPow_add]
  rw [show (m + 1) + (n - m) = n + 1 by omega]
  exact cokernel.condition _

/-- The canonical injection candidate x ↦ t^(n-m)x between principal quotients.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def raise (n m : ℕ) (h : m ≤ n) :
    principalQuotient R t m ⟶ principalQuotient R t n :=
  cokernel.desc _ (endoPow (globalSectionMultiplication R t) (n - m) ≫
    projection R t n) (raise_zero R t n m h)

/-- Multiplication by t^(m+1) on the degree-zero level-n quotient complex.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def differential (n m : ℕ) :
    principalReduction R t n ⟶ principalReduction R t n :=
  (CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
    RingCat.{r})).obj R)) 0).map
    (endoPow (scalar R t (principalQuotient R t n)) (m + 1))

/-- The complex [A_n → A_n] in degrees -1 and 0, with differential t^(m+1).
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def quotientKoszul (n m : ℕ) : CochainComplex (ringedSiteModules.{r} ((sheafCompose J
  (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ :=
  CochainComplex.mappingCone (differential R t n m)

/-- The quotient augmentation kills the differential.
Proof: the quotient to A_m kills t^(m+1), sectionwise before sheafification.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem augmentation_zero (n m : ℕ) (h : m ≤ n) :
    differential R t n m ≫
      (CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
        RingCat.{r})).obj R)) 0).map (quotientMap R t n m h) = 0 := by
  unfold differential
  rw [← Functor.map_comp]
  have hz : endoPow (scalar R t (principalQuotient R t n)) (m + 1) ≫
      quotientMap R t n m h = 0 := by
    have : Epi (projection R t n) := by unfold projection; infer_instance
    apply (cancel_epi (projection R t n)).1
    rw [← Category.assoc, projection_scalar, Category.assoc]
    change _ ≫ (cokernel.π _ ≫ cokernel.desc _ _ _) = _
    rw [cokernel.π_desc]
    simpa only [projection, comp_zero] using
      (cokernel.condition (endoPow (globalSectionMultiplication R t) (m + 1)))
  rw [hz, Functor.map_zero]

/-- The augmentation is zero on the shifted source and the quotient on the target.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def augmentation (n m : ℕ) (h : m ≤ n) :
    quotientKoszul R t n m ⟶ principalReduction R t m :=
  CochainComplex.mappingCone.descShortComplex
    (ShortComplex.mk (differential R t n m)
      ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J (forget₂
        CommRingCat.{r} RingCat.{r})).obj R)) 0).map (quotientMap R t n m h))
      (augmentation_zero R t n m h))

/-- The actual shifted mapping cone of the canonical augmentation.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def errorCone (n m : ℕ) (h : m ≤ n) :
    CochainComplex (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj R)) ℤ :=
  (CochainComplex.mappingCone (augmentation R t n m h))⟦(-1 : ℤ)⟧

/-- The degree-minus-one component x ↦ t^(n-m)x, with both cone inclusions.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def comparisonComponent (n m : ℕ) (h : m ≤ n) :
    principalQuotient R t m ⟶ (errorCone R t n m h).X (-1) :=
  raise R t n m h ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (principalQuotient R t n)).inv ≫
    HomologicalComplex.homotopyCofiber.inlX (differential R t n m) 0 (-1) (by decide) ≫
    HomologicalComplex.homotopyCofiber.inlX (augmentation R t n m h) (-1) (-2) (by decide) ≫
    ((CochainComplex.mappingCone (augmentation R t n m h)).shiftFunctorObjXIso
      (-1) (-1) (-2) rfl).inv

set_option maxHeartbeats 2000000 in
-- Component calculations through the nested cone maps need additional heartbeats.
set_option linter.style.haveILetI false in
set_option maxHeartbeats 1000000 in
-- Reduction of the explicit cone inverse needs more than the default heartbeat budget.
variable {S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)

variable (s : (SheafOfModules.unit
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)).sections)
  (hf : ∀ U : Cᵒᵖ, f.hom.app U (t.val U) = s.val U)

set_option maxHeartbeats 2000000 in
-- Component calculations through the nested cone maps need additional heartbeats.
set_option maxHeartbeats 2000000 in
-- Elaborating the two nested cone comparisons requires additional heartbeats.
set_option maxHeartbeats 2000000 in
-- Elaborating the two nested cone comparisons requires additional heartbeats.
end CategoryTheory.PrincipalQuotientError
