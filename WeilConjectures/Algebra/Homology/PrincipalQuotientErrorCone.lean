/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowersSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.BifunctorShift
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

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

variable (t : (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj
  R)).sections)

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

private lemma single_map_zero {D : Type*} [Category* D] [Preadditive D]
    [HasZeroObject D] {X Y : D} (f : X ⟶ Y) :
    ((CochainComplex.singleFunctor D 0).map f).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).inv :=
  HomologicalComplex.single_map_f_self _ _ _

@[reassoc]
private lemma single_map_inv {D : Type*} [Category* D] [Preadditive D]
    [HasZeroObject D] {X Y : D} (f : X ⟶ Y) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫
        ((CochainComplex.singleFunctor D 0).map f).f 0 =
      f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).inv := by
  rw [single_map_zero]
  simp only [Iso.inv_hom_id_assoc]

@[reassoc]
private lemma single_map_hom {D : Type*} [Category* D] [Preadditive D]
    [HasZeroObject D] {X Y : D} (f : X ⟶ Y) :
    ((CochainComplex.singleFunctor D 0).map f).f 0 ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫ f := by
  rw [single_map_zero]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma single_restriction_f {D E : Type*} [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [HasZeroObject D] [HasZeroObject E]
    (H : D ⥤ E) [H.Additive] {X : E} {Y : D} (f : X ⟶ H.obj Y) :
    ((CochainComplex.singleFunctor E 0).map f ≫
        (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).inv.app Y).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom ≫
        f ≫ H.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).inv := by
  rw [HomologicalComplex.comp_f, single_map_zero,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

@[reassoc]
private lemma single_restriction_inv {D E : Type*} [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [HasZeroObject D] [HasZeroObject E]
    (H : D ⥤ E) [H.Additive] {X : E} {Y : D} (f : X ⟶ H.obj Y) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫
        ((CochainComplex.singleFunctor E 0).map f ≫
          (HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0).inv.app Y).f 0 =
      f ≫ H.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).inv := by
  rw [HomologicalComplex.comp_f, single_map_zero,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

@[reassoc]
private lemma cone_inl_map {D : Type*} [Category* D] [Preadditive D]
    [HasBinaryBiproducts D] {K₁ L₁ K₂ L₂ : CochainComplex D ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (p q : ℤ) (h : (ComplexShape.up ℤ).Rel q p) :
    HomologicalComplex.homotopyCofiber.inlX φ₁ p q h ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f q =
      a.f p ≫ HomologicalComplex.homotopyCofiber.inlX φ₂ p q h := by
  change (CochainComplex.mappingCone.inl φ₁).v p q (by change q + 1 = p at h; omega) ≫ _ =
    _ ≫ (CochainComplex.mappingCone.inl φ₂).v p q (by change q + 1 = p at h; omega)
  simp [CochainComplex.mappingCone.map]

@[reassoc]
private lemma cone_inl_restriction {D E : Type*} [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [HasBinaryBiproducts D] [HasBinaryBiproducts E]
    {K L : CochainComplex D ℤ} (φ : K ⟶ L) (H : D ⥤ E) [H.Additive]
    (p q : ℤ) (h : (ComplexShape.up ℤ).Rel q p) :
    HomologicalComplex.homotopyCofiber.inlX
        ((H.mapHomologicalComplex (.up ℤ)).map φ) p q h ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso φ H).inv.f q =
      H.map (HomologicalComplex.homotopyCofiber.inlX φ p q h) := by
  change (CochainComplex.mappingCone.inl _).v p q
      (by change q + 1 = p at h; omega) ≫
    (CochainComplex.mappingCone.mapHomologicalComplexXIso φ H q).inv = _
  rw [CochainComplex.mappingCone.mapHomologicalComplexXIso_eq φ H q p h]
  simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso'_inv,
    Preadditive.comp_add, CochainComplex.mappingCone.inl_v_fst_v_assoc,
    CochainComplex.mappingCone.inl_v_snd_v_assoc, zero_comp, add_zero]
  rfl

@[reassoc]
private lemma cone_inr_map {D : Type*} [Category* D] [Preadditive D]
    [HasBinaryBiproducts D] {K₁ L₁ K₂ L₂ : CochainComplex D ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (q : ℤ) :
    (CochainComplex.mappingCone.inr φ₁).f q ≫
        (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f q =
      b.f q ≫ (CochainComplex.mappingCone.inr φ₂).f q := by
  simp [CochainComplex.mappingCone.map]

@[reassoc]
private lemma cone_inr_restriction {D E : Type*} [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [HasBinaryBiproducts D] [HasBinaryBiproducts E]
    {K L : CochainComplex D ℤ} (φ : K ⟶ L) (H : D ⥤ E) [H.Additive] (q : ℤ) :
    (CochainComplex.mappingCone.inr ((H.mapHomologicalComplex (.up ℤ)).map φ)).f q ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso φ H).inv.f q =
      H.map ((CochainComplex.mappingCone.inr φ).f q) := by
  change (CochainComplex.mappingCone.inr _).f q ≫
    (CochainComplex.mappingCone.mapHomologicalComplexXIso φ H q).inv = _
  rw [CochainComplex.mappingCone.mapHomologicalComplexXIso_eq φ H q (q + 1) rfl]
  simp [CochainComplex.mappingCone.mapHomologicalComplexXIso'_inv]

@[reassoc]
private lemma cone_map_restriction {D E : Type*} [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [HasBinaryBiproducts D] [HasBinaryBiproducts E]
    {K₁ L₁ K₂ L₂ : CochainComplex D ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂) (H : D ⥤ E) [H.Additive] :
    CochainComplex.mappingCone.map
        ((H.mapHomologicalComplex (.up ℤ)).map φ₁)
        ((H.mapHomologicalComplex (.up ℤ)).map φ₂)
        ((H.mapHomologicalComplex (.up ℤ)).map a)
        ((H.mapHomologicalComplex (.up ℤ)).map b)
        (by simpa only [← Functor.map_comp] using
          congrArg (H.mapHomologicalComplex (.up ℤ)).map comm) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso φ₂ H).inv =
      (CochainComplex.mappingCone.mapHomologicalComplexIso φ₁ H).inv ≫
        (H.mapHomologicalComplex (.up ℤ)).map
          (CochainComplex.mappingCone.map φ₁ φ₂ a b comm) := by
  apply HomologicalComplex.hom_ext
  intro q
  rw [CochainComplex.mappingCone.ext_from_iff _ (q + 1) q (by omega)]
  constructor
  · change HomologicalComplex.homotopyCofiber.inlX _ (q + 1) q rfl ≫ _ =
      HomologicalComplex.homotopyCofiber.inlX _ (q + 1) q rfl ≫ _
    simp only [HomologicalComplex.comp_f, cone_inl_map_assoc,
      cone_inl_restriction_assoc, cone_inl_restriction,
      Functor.mapHomologicalComplex_map_f, ← H.map_comp, cone_inl_map]
  · simp only [HomologicalComplex.comp_f, cone_inr_map_assoc,
      cone_inr_restriction_assoc, cone_inr_restriction,
      Functor.mapHomologicalComplex_map_f, ← H.map_comp, cone_inr_map]

private lemma shift_square {D E : Type*} [Category* D] [Category* E]
    [HasShift D ℤ] [HasShift E ℤ] (U : D ⥤ E) [U.CommShift ℤ]
    {X Y : E} {X' Y' : D} (a : X ⟶ Y) (b : Y ⟶ U.obj Y')
    (a' : X ⟶ U.obj X') (b' : X' ⟶ Y') (h : a ≫ b = a' ≫ U.map b') (n : ℤ) :
    a⟦n⟧' ≫ (b⟦n⟧' ≫ (U.commShiftIso n).inv.app Y') =
      (a'⟦n⟧' ≫ (U.commShiftIso n).inv.app X') ≫ U.map (b'⟦n⟧') := by
  have hn := ((U.commShiftIso n).inv).naturality b'
  dsimp only [Functor.comp_map] at hn
  calc
    _ = (a ≫ b)⟦n⟧' ≫ (U.commShiftIso n).inv.app Y' := by
      rw [Functor.map_comp, Category.assoc]
    _ = (a' ≫ U.map b')⟦n⟧' ≫ (U.commShiftIso n).inv.app Y' := by rw [h]
    _ = _ := by rw [Functor.map_comp, Category.assoc, hn, Category.assoc]

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

private lemma comparisonComponent_eq (n m : ℕ) (h : m ≤ n) :
    comparisonComponent R t n m h =
      raise R t n m h ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (principalQuotient R t n)).inv ≫
        HomologicalComplex.homotopyCofiber.inlX (differential R t n m) 0 (-1) (by decide) ≫
        HomologicalComplex.homotopyCofiber.inlX
          (augmentation R t n m h) (-1) (-2) (by decide) := by
  rfl

private lemma raise_scalar_zero (n m : ℕ) (h : m ≤ n) :
    raise R t n m h ≫ endoPow (scalar R t (principalQuotient R t n)) (m + 1) = 0 := by
  have : Epi (projection R t m) := by unfold projection; infer_instance
  apply (cancel_epi (projection R t m)).1
  change cokernel.π _ ≫ (cokernel.desc _ _ _ ≫ _) = _
  rw [cokernel.π_desc_assoc, Category.assoc, projection_scalar,
    ← Category.assoc, ← endoPow_add]
  rw [show (n - m) + (m + 1) = n + 1 by omega]
  simpa only [projection, comp_zero] using
    (cokernel.condition (endoPow (globalSectionMultiplication R t) (n + 1)))

/-- The prescribed component is a cycle and therefore defines a chain map.
Proof: its differential is ±t^(m+1)t^(n-m)x=±t^(n+1)x=0; all other components vanish.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem comparisonComponent_cycle (n m : ℕ) (h : m ≤ n) (k : ℤ)
    (hk : (ComplexShape.up ℤ).Rel (-1) k) :
    comparisonComponent R t n m h ≫ (errorCone R t n m h).d (-1) k = 0 := by
  have hk' : k = 0 := by
    change -1 + 1 = k at hk
    omega
  subst k
  simp only [comparisonComponent, errorCone, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, Preadditive.comp_neg, neg_eq_zero]
  change (raise R t n m h ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (principalQuotient R t n)).inv ≫
        (CochainComplex.mappingCone.inl (differential R t n m)).v 0 (-1) rfl ≫
        (CochainComplex.mappingCone.inl (augmentation R t n m h)).v (-1) (-2) rfl) ≫
      ((CochainComplex.mappingCone (augmentation R t n m h)).d (-2) (-1)) = 0
  have hz : (CochainComplex.mappingCone.inl (differential R t n m)).v 0 (-1) rfl ≫
      (augmentation R t n m h).f (-1) = 0 := by
    exact CochainComplex.mappingCone.inl_v_descShortComplex_f
      (ShortComplex.mk (differential R t n m) _ (augmentation_zero R t n m h))
      0 (-1) rfl
  have hd : (CochainComplex.mappingCone.inl (differential R t n m)).v 0 (-1) rfl ≫
      (quotientKoszul R t n m).d (-1) 0 =
      (differential R t n m).f 0 ≫
        (CochainComplex.mappingCone.inr (differential R t n m)).f 0 := by
    simpa only [quotientKoszul, principalReduction, CochainComplex.singleFunctor_obj_d,
      zero_comp,
      sub_zero] using
      CochainComplex.mappingCone.inl_v_d (differential R t n m) 0 (-1) 1 rfl rfl
  have hc : raise R t n m h ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (principalQuotient R t n)).inv ≫
      (differential R t n m).f 0 = 0 := by
    simp only [differential, single_map_zero, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, raise_scalar_zero, zero_comp]
  simp only [Category.assoc,
    CochainComplex.mappingCone.inl_v_d (augmentation R t n m h) (-1) (-2) 0 rfl rfl,
    Preadditive.comp_sub, reassoc_of% hz]
  simp only [reassoc_of% hd, reassoc_of% hc, zero_comp, comp_zero, sub_self]

/-- The specified map A_m[1] → Cone(ε)[-1], with no choice of representatives.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def comparison (n m : ℕ) (h : m ≤ n) :
    (principalReduction R t m)⟦(1 : ℤ)⟧ ⟶ errorCone R t n m h :=
  ((CochainComplex.singleFunctors (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
    RingCat.{r})).obj R))).shiftIso 1 (-1) 0 rfl).hom.app
      (principalQuotient R t m) ≫
    HomologicalComplex.mkHomFromSingle (comparisonComponent R t n m h)
      (comparisonComponent_cycle R t n m h)

/-- The quotient map commutes with multiplication on the two-term complexes.
Proof: the quotient maps are R-linear and multiplication by a global section is natural.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem transition_square (n' n m : ℕ) (h : n ≤ n') :
    differential R t n' m ≫
        (CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J (forget₂
          CommRingCat.{r} RingCat.{r})).obj R)) 0).map (quotientMap R t n' n h) =
      (CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
        RingCat.{r})).obj R)) 0).map (quotientMap R t n' n h) ≫
        differential R t n m := by
  unfold differential
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact endoPow_naturality _ _ _ (scalar_naturality R t _) _

/-- The strict quotient transition on the two copies of A_n.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def koszulTransition (n' n m : ℕ) (h : n ≤ n') :
    quotientKoszul R t n' m ⟶ quotientKoszul R t n m :=
  CochainComplex.mappingCone.map _ _
    ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj R)) 0).map (quotientMap R t n' n h))
    ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj R)) 0).map (quotientMap R t n' n h))
    (transition_square R t n' n m h)

/-- The quotient transitions commute with the augmentations.
Proof: both maps vanish on the shifted cone summand and are the same quotient on the other.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem errorTransition_square (n' n m : ℕ) (h : m ≤ n) (h' : n ≤ n') :
    augmentation R t n' m (h.trans h') ≫ 𝟙 _ =
      koszulTransition R t n' n m h' ≫ augmentation R t n m h := by
  let F := CochainComplex.singleFunctor
    (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj R)) 0
  let S₁ := ShortComplex.mk (differential R t n' m)
    (F.map (quotientMap R t n' m (h.trans h')))
    (augmentation_zero R t n' m (h.trans h'))
  let S₂ := ShortComplex.mk (differential R t n m)
    (F.map (quotientMap R t n m h)) (augmentation_zero R t n m h)
  let φ : S₁ ⟶ S₂ :=
    { τ₁ := F.map (quotientMap R t n' n h')
      τ₂ := F.map (quotientMap R t n' n h')
      τ₃ := 𝟙 _
      comm₁₂ := (transition_square R t n' n m h').symm
      comm₂₃ := by
        dsimp only [S₁, S₂]
        rw [Category.comp_id, ← F.map_comp]
        congr 1
        have : Epi (projection R t n') := by unfold projection; infer_instance
        apply (cancel_epi (projection R t n')).1
        simp only [quotientMap, projection, cokernel.π_desc_assoc, cokernel.π_desc] }
  exact (CochainComplex.mappingCone.map_descShortComplex S₁ S₂ φ).symm

/-- The actual quotient transition of shifted error cones, identity on A_m.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def errorTransition (n' n m : ℕ) (h : m ≤ n) (h' : n ≤ n') :
    errorCone R t n' m (h.trans h') ⟶ errorCone R t n m h :=
  (CochainComplex.mappingCone.map _ _ (koszulTransition R t n' n m h') (𝟙 _)
    (errorTransition_square R t n' n m h h'))⟦(-1 : ℤ)⟧'

private lemma errorTransition_f (n' n m : ℕ) (h : m ≤ n) (h' : n ≤ n') :
    (errorTransition R t n' n m h h').f (-1) =
      (CochainComplex.mappingCone.map _ _ (koszulTransition R t n' n m h') (𝟙 _)
        (errorTransition_square R t n' n m h h')).f (-2) := by
  rfl

@[reassoc]
private lemma koszulTransition_inl (n' n m : ℕ) (h : n ≤ n') :
    HomologicalComplex.homotopyCofiber.inlX
        (differential R t n' m) 0 (-1) (by decide) ≫
        (koszulTransition R t n' n m h).f (-1) =
      ((CochainComplex.singleFunctor _ 0).map (quotientMap R t n' n h)).f 0 ≫
        HomologicalComplex.homotopyCofiber.inlX
          (differential R t n m) 0 (-1) (by decide) := by
  exact cone_inl_map (differential R t n' m) (differential R t n m) _ _
    (transition_square R t n' n m h) 0 (-1) (by decide)

@[reassoc]
private lemma errorTransition_inl (n' n m : ℕ) (h : m ≤ n) (h' : n ≤ n') :
    HomologicalComplex.homotopyCofiber.inlX
        (augmentation R t n' m (h.trans h')) (-1) (-2) (by decide) ≫
        (errorTransition R t n' n m h h').f (-1) =
      (koszulTransition R t n' n m h').f (-1) ≫
        HomologicalComplex.homotopyCofiber.inlX
          (augmentation R t n m h) (-1) (-2) (by decide) := by
  rw [errorTransition_f]
  exact cone_inl_map (augmentation R t n' m (h.trans h'))
    (augmentation R t n m h) _ _ (errorTransition_square R t n' n m h h')
    (-1) (-2) (by decide)

/-- The canonical principal quotient comparison is a quasi-isomorphism.
Proof: on the presheaf quotient R(U)/t^(n+1), cancellation of the regular element gives
ker(t^(m+1))=t^(n-m)A_n and identifies it with A_m. The quotient to A_m is surjective,
and its kernel is the image of t^(m+1). Thus the error has cohomology A_m in degree -1
and zero elsewhere. Exact module sheafification preserves this calculation. This is
steps 1 and 2 of the node, using the cited module category, cone and quasi-isomorphism
notions and lem-weil-pbc-ringed-site-module-sheafification-exact.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem comparison_quasiIso (ht : Mono (globalSectionMultiplication R t))
    (n m : ℕ) (h : m ≤ n) : QuasiIso (comparison R t n m h) := by
  sorry

private lemma comparison_f (n m : ℕ) (h : m ≤ n) :
    (comparison R t n m h).f (-1) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (principalQuotient R t m)).hom ≫
        comparisonComponent R t n m h := by
  simp only [comparison, HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f]
  rfl

private lemma raise_transition (n' n m : ℕ) (h : m ≤ n) (h' : n ≤ n') :
    raise R t n' m (h.trans h') ≫ quotientMap R t n' n h' =
      endoPow (scalar R t (principalQuotient R t m)) (n' - n) ≫ raise R t n m h := by
  have : Epi (projection R t m) := by unfold projection; infer_instance
  apply (cancel_epi (projection R t m)).1
  rw [← Category.assoc, ← Category.assoc, projection_scalar]
  simp only [Category.assoc, raise, quotientMap, projection, cokernel.π_desc]
  rw [← Category.assoc, ← endoPow_add]
  congr 2
  omega

set_option maxHeartbeats 2000000 in
-- Component calculations through the nested cone maps need additional heartbeats.
/-- Under the specified quasi-isomorphisms the transition is multiplication by t^(n'-n).
Proof: in degree -1 both composites send x to t^(n'-m)x modulo t^(n+1), since
(n-m)+(n'-n)=n'-m. In every other degree the source is zero. The equality is strict,
so also holds after localization in the derived category. This is node proof step 3;
it includes n=m and n'=n.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem comparison_transition (n' n m : ℕ) (h : m ≤ n) (h' : n ≤ n') :
    comparison R t n' m (h.trans h') ≫ errorTransition R t n' n m h h' =
      ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J (forget₂
        CommRingCat.{r} RingCat.{r})).obj R)) 0).map
        (endoPow (scalar R t (principalQuotient R t m)) (n' - n)))⟦(1 : ℤ)⟧' ≫
      comparison R t n m h := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = -1
  · subst i
    simp only [HomologicalComplex.comp_f, comparison_f,
      CochainComplex.shiftFunctor_map_f', Int.reduceAdd, comparisonComponent_eq,
      Category.assoc]
    rw [errorTransition_inl, koszulTransition_inl_assoc, single_map_inv_assoc,
      single_map_hom_assoc]
    erw [reassoc_of% (raise_transition R t n' n m h h')]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (principalQuotient R t m) (i + 1) (by omega)).eq_of_src _ _

/-- The two-term model identifies with the recorded total tensor, with factors reversed
by the symmetry if desired. This is an identification of actual complexes, before
localization, because the node prescribes their components.
Proof: only one tensor summand occurs in each of degrees -1 and 0. The unitors identify
both terms with A_n and the differential with multiplication by t^(m+1).
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem quotientKoszul_tensor_model (n m : ℕ) :
    ∃ e : ((koszulTensorFunctor R (principalReduction R t n)).obj
        (principalKoszul R t m)) ≅ quotientKoszul R t n m,
      koszulRepresentativeAugmentation R (principalReduction R t n) t m ≫ e.hom =
        CochainComplex.mappingCone.inr (differential R t n m) := by
  sorry

/-- The existing restriction of scalars, along a morphism of commutative ring sheaves.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable abbrev coefficientRestriction {S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :=
  SheafOfModules.restrictScalars.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map f)

/-- Restriction of scalars on complexes, using the existing termwise functor.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable abbrev complexRestriction {S : Sheaf J CommRingCat.{r}} (f : R ⟶ S) :=
  (coefficientRestriction R f).mapHomologicalComplex (.up ℤ)

variable {S : Sheaf J CommRingCat.{r}} (f : R ⟶ S)

/-- The canonical R-linear map R → S, with S regarded as an R-module.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def unitRingMap :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⟶
      (coefficientRestriction R f).obj
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).val.obj U)
        (Y := ((coefficientRestriction R f).obj (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S))).val.obj U)
        { toFun := f.hom.app U
          map_add' := map_add _
          map_smul' := fun a b ↦ (f.hom.app U).hom.map_mul a b }
      naturality := fun {U V} g ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact CategoryTheory.congr_fun (f.hom.naturality g) x }

variable (s : (SheafOfModules.unit
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S)).sections)
  (hf : ∀ U : Cᵒᵖ, f.hom.app U (t.val U) = s.val U)

private lemma scalar_restriction
    (hf : ∀ U : Cᵒᵖ, f.hom.app U (t.val U) = s.val U)
    (M : ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj S)) :
    scalar R t ((coefficientRestriction R f).obj M) =
      (coefficientRestriction R f).map (scalar S s M) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let x : M.val.obj U := x
  change (f.hom.app U).hom (t.val U) • x = (@id (S.obj.obj U) (s.val U)) • x
  rw [hf U]
  rfl

private lemma map_endoPow {D E : Type*} [Category* D] [Category* E]
    (F : D ⥤ E) {X : D} (a : X ⟶ X) (k : ℕ) :
    F.map (endoPow a k) = endoPow (F.map a) k := by
  induction k with
  | zero => exact F.map_id _
  | succ k ih =>
      change F.map (endoPow a k ≫ a) = endoPow (F.map a) k ≫ F.map a
      rw [F.map_comp, ih]

/-- A ring morphism preserving the section kills the source relation in the target quotient.
Proof: f(t^(n+1)x)=s^(n+1)f(x), which vanishes after the target quotient projection.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem quotientRingMap_zero
    (hf : ∀ U : Cᵒᵖ, f.hom.app U (t.val U) = s.val U) (n : ℕ) :
    endoPow (globalSectionMultiplication R t) (n + 1) ≫
      (unitRingMap R f ≫ (coefficientRestriction R f).map (projection S s n)) = 0 := by
  have hc : globalSectionMultiplication R t ≫ unitRingMap R f =
      unitRingMap R f ≫ (coefficientRestriction R f).map
        (globalSectionMultiplication S s) := by
    rw [← scalar_unit R t, ← scalar_unit S s,
      ← scalar_restriction R t f s hf]
    exact scalar_naturality R t _
  rw [← Category.assoc, endoPow_naturality _ _ _ hc, Category.assoc,
    ← map_endoPow, ← Functor.map_comp]
  change _ ≫ (coefficientRestriction R f).map (_ ≫ cokernel.π _) = 0
  rw [cokernel.condition, Functor.map_zero, comp_zero]

/-- The canonical quotient map induced by the ring morphism; no arbitrary lift is chosen.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def quotientRingMap (n : ℕ) :
    principalQuotient R t n ⟶ (coefficientRestriction R f).obj (principalQuotient S s n) :=
  cokernel.desc _
    (unitRingMap R f ≫ (coefficientRestriction R f).map (projection S s n))
    (quotientRingMap_zero R t f s hf n)

/-- The induced map of degree-zero quotient complexes, with the canonical single comparison.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def singleRingMap (n : ℕ) :
    principalReduction R t n ⟶ (complexRestriction R f).obj (principalReduction S s n) :=
  (CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
    RingCat.{r})).obj R)) 0).map (quotientRingMap R t f s hf n) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (coefficientRestriction R f) (.up ℤ) 0).inv.app (principalQuotient S s n)

private lemma singleRingMap_f (n : ℕ) :
    (singleRingMap R t f s hf n).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (principalQuotient R t n)).hom ≫
        quotientRingMap R t f s hf n ≫ (coefficientRestriction R f).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (principalQuotient S s n)).inv :=
  single_restriction_f (coefficientRestriction R f) (quotientRingMap R t f s hf n)

@[reassoc]
private lemma singleRingMap_f_inv (n : ℕ) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (principalQuotient R t n)).inv ≫
        (singleRingMap R t f s hf n).f 0 =
      quotientRingMap R t f s hf n ≫ (coefficientRestriction R f).map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (principalQuotient S s n)).inv :=
  single_restriction_inv (coefficientRestriction R f) (quotientRingMap R t f s hf n)

/-- Coefficient change commutes with the scalar differential.
Proof: use f(t)=s on every section and the quotient universal property, then the
naturality of the canonical single-complex comparison.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem differentialRingMap_square (n m : ℕ) :
    differential R t n m ≫ singleRingMap R t f s hf n =
      singleRingMap R t f s hf n ≫ (complexRestriction R f).map (differential S s n m) := by
  let F := CochainComplex.singleFunctor
    (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj R)) 0
  let G := CochainComplex.singleFunctor
    (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj S)) 0
  let T := coefficientRestriction R f
  let e := HomologicalComplex.singleMapHomologicalComplex T (.up ℤ) 0
  have hc : endoPow (scalar R t (principalQuotient R t n)) (m + 1) ≫
      quotientRingMap R t f s hf n =
      quotientRingMap R t f s hf n ≫ T.map
        (endoPow (scalar S s (principalQuotient S s n)) (m + 1)) := by
    rw [map_endoPow]
    apply endoPow_naturality
    rw [← scalar_restriction R t f s hf]
    exact scalar_naturality R t _
  change F.map _ ≫ (F.map _ ≫ e.inv.app _) =
    (F.map _ ≫ e.inv.app _) ≫ (complexRestriction R f).map (G.map _)
  rw [← Category.assoc, ← F.map_comp, hc, F.map_comp, Category.assoc,
    Category.assoc]
  congr 1
  exact e.inv.naturality _

/-- The actual coefficient map of two-term quotient complexes, formed by the cone square.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def koszulRingMap (n m : ℕ) :
    quotientKoszul R t n m ⟶ (complexRestriction R f).obj (quotientKoszul S s n m) :=
  CochainComplex.mappingCone.map _ _ (singleRingMap R t f s hf n)
    (singleRingMap R t f s hf n) (differentialRingMap_square R t f s hf n m) ≫
    (CochainComplex.mappingCone.mapHomologicalComplexIso (differential S s n m)
      (coefficientRestriction R f)).inv

@[reassoc]
private lemma koszulRingMap_inl (n m : ℕ) :
    HomologicalComplex.homotopyCofiber.inlX (differential R t n m) 0 (-1) (by decide) ≫
        (koszulRingMap R t f s hf n m).f (-1) =
      (singleRingMap R t f s hf n).f 0 ≫ (coefficientRestriction R f).map
        (HomologicalComplex.homotopyCofiber.inlX (differential S s n m) 0 (-1) (by decide)) := by
  unfold koszulRingMap
  rw [HomologicalComplex.comp_f, ← Category.assoc,
    cone_inl_map (differential R t n m)
      ((complexRestriction R f).map (differential S s n m))
      (singleRingMap R t f s hf n) (singleRingMap R t f s hf n)
      (differentialRingMap_square R t f s hf n m) 0 (-1) (by decide),
    Category.assoc, cone_inl_restriction]

private lemma quotientRingMap_transition (n m : ℕ) (h : m ≤ n) :
    quotientMap R t n m h ≫ quotientRingMap R t f s hf m =
      quotientRingMap R t f s hf n ≫
        (coefficientRestriction R f).map (quotientMap S s n m h) := by
  have : Epi (projection R t n) := by unfold projection; infer_instance
  apply (cancel_epi (projection R t n)).1
  simp only [quotientMap, quotientRingMap, projection, cokernel.π_desc_assoc,
    Category.assoc, ← Functor.map_comp, cokernel.π_desc]

private lemma singleRingMap_transition (n m : ℕ) (h : m ≤ n) :
    (CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) 0).map (quotientMap R t n m h) ≫
      singleRingMap R t f s hf m =
    singleRingMap R t f s hf n ≫ (complexRestriction R f).map
      ((CochainComplex.singleFunctor (ringedSiteModules.{r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj S)) 0).map (quotientMap S s n m h)) := by
  unfold singleRingMap
  rw [← Category.assoc, ← Functor.map_comp, quotientRingMap_transition,
    Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (HomologicalComplex.singleMapHomologicalComplex
    (coefficientRestriction R f) (.up ℤ) 0).inv.naturality _

/-- Coefficient change commutes with the quotient augmentation.
Proof: the two composites vanish on the shifted cone summand, and on the target summand
both are the quotient of f. This uses only f(t)=s, not flatness of f.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem augmentationRingMap_square (n m : ℕ) (h : m ≤ n) :
    augmentation R t n m h ≫ singleRingMap R t f s hf m =
      koszulRingMap R t f s hf n m ≫
        (complexRestriction R f).map (augmentation S s n m h) := by
  let F := CochainComplex.singleFunctor
    (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj R)) 0
  let G := CochainComplex.singleFunctor
    (ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat.{r}
      RingCat.{r})).obj S)) 0
  let U := complexRestriction R f
  let S₁ := ShortComplex.mk (differential R t n m)
    (F.map (quotientMap R t n m h)) (augmentation_zero R t n m h)
  let S₂ := ShortComplex.mk (differential S s n m)
    (G.map (quotientMap S s n m h)) (augmentation_zero S s n m h)
  let φ : S₁ ⟶ S₂.map U :=
    { τ₁ := singleRingMap R t f s hf n
      τ₂ := singleRingMap R t f s hf n
      τ₃ := singleRingMap R t f s hf m
      comm₁₂ := (differentialRingMap_square R t f s hf n m).symm
      comm₂₃ := (singleRingMap_transition R t f s hf n m h).symm }
  have hc := CochainComplex.mappingCone.map_descShortComplex S₁ (S₂.map U) φ
  have he := CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex
    (coefficientRestriction R f) S₂
  change CochainComplex.mappingCone.descShortComplex S₁ ≫ φ.τ₃ =
    (_ ≫ (CochainComplex.mappingCone.mapHomologicalComplexIso S₂.f
      (coefficientRestriction R f)).inv) ≫
        U.map (CochainComplex.mappingCone.descShortComplex S₂)
  rw [← he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact hc.symm

/-- The canonical coefficient map of the actual shifted error cones.
The standard cone and shift comparisons place the target in restricted scalars.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
noncomputable def errorRingMap (n m : ℕ) (h : m ≤ n) :
    errorCone R t n m h ⟶ (complexRestriction R f).obj (errorCone S s n m h) := by
  unfold errorCone
  exact (CochainComplex.mappingCone.map _ _ (koszulRingMap R t f s hf n m)
    (singleRingMap R t f s hf m) (augmentationRingMap_square R t f s hf n m h) ≫
    (CochainComplex.mappingCone.mapHomologicalComplexIso (augmentation S s n m h)
      (coefficientRestriction R f)).inv)⟦(-1 : ℤ)⟧' ≫
    ((complexRestriction R f).commShiftIso (-1 : ℤ)).inv.app
      (CochainComplex.mappingCone (augmentation S s n m h))

private lemma errorRingMap_f (n m : ℕ) (h : m ≤ n) :
    (errorRingMap R t f s hf n m h).f (-1) =
      (CochainComplex.mappingCone.map _ _ (koszulRingMap R t f s hf n m)
          (singleRingMap R t f s hf m) (augmentationRingMap_square R t f s hf n m h) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso (augmentation S s n m h)
          (coefficientRestriction R f)).inv).f (-2) := by
  rfl

private lemma raise_ringMap (n m : ℕ) (h : m ≤ n) :
    raise R t n m h ≫ quotientRingMap R t f s hf n =
      quotientRingMap R t f s hf m ≫
        (coefficientRestriction R f).map (raise S s n m h) := by
  have hc : globalSectionMultiplication R t ≫ unitRingMap R f =
      unitRingMap R f ≫ (coefficientRestriction R f).map
        (globalSectionMultiplication S s) := by
    rw [← scalar_unit R t, ← scalar_unit S s,
      ← scalar_restriction R t f s hf]
    exact scalar_naturality R t _
  have hp := endoPow_naturality _ _ _ hc (n - m)
  rw [← map_endoPow] at hp
  have : Epi (projection R t m) := by unfold projection; infer_instance
  apply (cancel_epi (projection R t m)).1
  simp only [raise, quotientRingMap, projection, cokernel.π_desc_assoc,
    Category.assoc, ← Functor.map_comp, cokernel.π_desc]
  rw [← Category.assoc, hp, Category.assoc, ← Functor.map_comp]

set_option maxHeartbeats 2000000 in
-- Component calculations through the nested cone maps need additional heartbeats.
/-- The specified quasi-isomorphism is natural under every section-preserving ring morphism.
Proof: f(t^(n-m)x)=s^(n-m)f(x) on the presheaf quotient. Sheafification preserves this
identity. The single, cone and shift comparisons give the same equality for chain maps.
This is node proof step 4, with no flatness assumption on the morphism of rings.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem comparison_naturality (n m : ℕ) (h : m ≤ n) :
    comparison R t n m h ≫ errorRingMap R t f s hf n m h =
      (singleRingMap R t f s hf m)⟦(1 : ℤ)⟧' ≫
        ((complexRestriction R f).commShiftIso 1).inv.app (principalReduction S s m) ≫
        (complexRestriction R f).map (comparison S s n m h) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = -1
  · subst i
    change (comparison R t n m h).f (-1) ≫ (errorRingMap R t f s hf n m h).f (-1) =
      (singleRingMap R t f s hf m).f 0 ≫
        (coefficientRestriction R f).map ((comparison S s n m h).f (-1))
    simp only [comparison_f, comparisonComponent_eq, errorRingMap_f,
      HomologicalComplex.comp_f, singleRingMap_f, Functor.map_comp, Category.assoc]
    erw [cone_inl_map_assoc, cone_inl_restriction]
    rw [koszulRingMap_inl_assoc, singleRingMap_f_inv_assoc]
    erw [Iso.map_inv_hom_id_assoc]
    erw [reassoc_of% (raise_ringMap R t f s hf n m h)]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (principalQuotient R t m) (i + 1) (by omega)).eq_of_src _ _

set_option maxHeartbeats 2000000 in
-- Elaborating the two nested cone comparisons requires additional heartbeats.
private lemma koszulRingMap_transition (n' n m : ℕ) (h : n ≤ n') :
    koszulTransition R t n' n m h ≫ koszulRingMap R t f s hf n m =
      koszulRingMap R t f s hf n' m ≫
        (complexRestriction R f).map (koszulTransition S s n' n m h) := by
  unfold koszulTransition koszulRingMap
  simp only [Category.assoc]
  rw [← cone_map_restriction]
  rw [← CochainComplex.mappingCone.map_comp_assoc,
    ← CochainComplex.mappingCone.map_comp_assoc]
  congr 2 <;> exact singleRingMap_transition R t f s hf n' n h

set_option maxHeartbeats 2000000 in
-- Elaborating the two nested cone comparisons requires additional heartbeats.
/-- The quotient transitions of error cones are natural under the same ring morphisms.
Proof: the quotients of f commute with quotient transitions in both A_n components, and
with the identity on A_m. Apply functoriality of the actual cone and shift comparisons.
This is the transition part of node proof step 4, including n=m and n'=n.
Source: sk-lem-sp-tower.proof.md, paragraph 2
(blueprint: lem-sp-principal-quotient-error-cone). -/
theorem errorTransition_naturality (n' n m : ℕ) (h : m ≤ n) (h' : n ≤ n') :
    errorTransition R t n' n m h h' ≫ errorRingMap R t f s hf n m h =
      errorRingMap R t f s hf n' m (h.trans h') ≫
        (complexRestriction R f).map (errorTransition S s n' n m h h') := by
  have hc :
      CochainComplex.mappingCone.map _ _ (koszulTransition R t n' n m h') (𝟙 _)
          (errorTransition_square R t n' n m h h') ≫
        (CochainComplex.mappingCone.map _ _ (koszulRingMap R t f s hf n m)
          (singleRingMap R t f s hf m) (augmentationRingMap_square R t f s hf n m h) ≫
          (CochainComplex.mappingCone.mapHomologicalComplexIso
            (augmentation S s n m h) (coefficientRestriction R f)).inv) =
      (CochainComplex.mappingCone.map _ _ (koszulRingMap R t f s hf n' m)
          (singleRingMap R t f s hf m)
          (augmentationRingMap_square R t f s hf n' m (h.trans h')) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso
          (augmentation S s n' m (h.trans h')) (coefficientRestriction R f)).inv) ≫
        (complexRestriction R f).map
          (CochainComplex.mappingCone.map _ _ (koszulTransition S s n' n m h') (𝟙 _)
            (errorTransition_square S s n' n m h h')) := by
    simp only [Category.assoc]
    rw [← cone_map_restriction]
    rw [← CochainComplex.mappingCone.map_comp_assoc,
      ← CochainComplex.mappingCone.map_comp_assoc]
    simp only [Category.id_comp, Functor.map_id, Category.comp_id,
      koszulRingMap_transition R t f s hf n' n m h']
  exact shift_square (complexRestriction R f) _ _ _ _ hc (-1)

end CategoryTheory.PrincipalQuotientError
