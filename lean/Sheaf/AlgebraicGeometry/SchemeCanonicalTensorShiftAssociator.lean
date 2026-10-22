/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.SchemeCanonicalTensorShift
import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne
import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution

/-! # First-variable tensor translation and reassociation

Source: Stacks Project, Tag 06YH, total tensor localization, and the triple-totalization
calculation in lem-sc-scheme-canonical-shift-unit-associativity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry

-- Cancel the b-comparison from the (a + b)-square, then use faithfulness of shift by b.
private theorem core_of_add
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    (a b : ℤ) (hb : NatTrans.CommShiftCore τ b)
    (hab : NatTrans.CommShiftCore τ (a + b)) : NatTrans.CommShiftCore τ a := by
  constructor
  ext X
  apply (shiftFunctor D b).map_injective
  have h := hab.shift_app_comm τ X
  simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
    Functor.comp_obj] at h
  have hD := (shiftFunctorAdd D a b).inv.naturality (τ.app X)
  have hC := τ.naturality ((shiftFunctorAdd C a b).hom.app X)
  dsimp at hD hC
  simp only [Category.assoc] at h ⊢
  rw [← hD] at h
  rw [← reassoc_of% hC] at h
  rw [← hb.shift_app_comm_assoc τ] at h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp]
  have h := (cancel_epi (F.map ((shiftFunctorAdd C a b).hom.app X))).1 h
  have h := (cancel_epi ((F.commShiftIso b).hom.app (X⟦a⟧))).1 h
  apply (cancel_mono ((shiftFunctorAdd D a b).inv.app (G.obj X))).1
  simpa only [Category.assoc] using h

-- The zero square and cancellation give -1; addition then covers every integer.
private theorem shift_of_one
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    (h : NatTrans.CommShiftCore τ (1 : ℤ)) : NatTrans.CommShift τ ℤ := by
  apply NatTrans.CommShift.of_core
  have hn : NatTrans.CommShiftCore τ (-1 : ℤ) :=
    core_of_add τ (-1) 1 h (by simpa using (NatTrans.CommShiftCore.zero ℤ))
  intro n
  induction n using Int.induction_on with
  | zero => exact NatTrans.CommShiftCore.zero ℤ
  | succ n ih => exact ih.add h
  | pred n ih => simpa only [sub_eq_add_neg] using ih.add hn

-- The two sides are natural transformations, so equality transports across an isomorphism.
private theorem core_of_iso_representatives
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
    {ι : Type*} (obj : ι → C) (S : ι → Prop)
    (hS : ∀ X, ∃ P, S P ∧ Nonempty (obj P ≅ X))
    (h : ∀ P, S P →
      (F.commShiftIso (1 : ℤ)).hom.app (obj P) ≫ (τ.app (obj P))⟦(1 : ℤ)⟧' =
        τ.app ((obj P)⟦(1 : ℤ)⟧) ≫ (G.commShiftIso (1 : ℤ)).hom.app (obj P)) :
    NatTrans.CommShiftCore τ (1 : ℤ) := by
  constructor
  let α := (F.commShiftIso (1 : ℤ)).hom ≫
    Functor.whiskerRight τ (shiftFunctor D (1 : ℤ))
  let β := Functor.whiskerLeft (shiftFunctor C (1 : ℤ)) τ ≫
    (G.commShiftIso (1 : ℤ)).hom
  change α = β
  ext X
  obtain ⟨P, hP, ⟨e⟩⟩ := hS X
  rw [← cancel_epi ((shiftFunctor C (1 : ℤ) ⋙ F).map e.hom),
    α.naturality, β.naturality]
  congr 1
  exact h P hP

-- A commuting square transports along isomorphisms of its source and target functors.
private theorem core_of_commShift_iso
    {C : Type*} {D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F₀ F₁ G₀ G₁ : C ⥤ D}
    [F₀.CommShift ℤ] [F₁.CommShift ℤ] [G₀.CommShift ℤ] [G₁.CommShift ℤ]
    (τ₀ : F₀ ⟶ G₀) (τ₁ : F₁ ⟶ G₁) (eF : F₀ ≅ F₁) (eG : G₀ ≅ G₁)
    [NatTrans.CommShift eF.hom ℤ] [NatTrans.CommShift eG.hom ℤ]
    (hc : eF.hom ≫ τ₁ = τ₀ ≫ eG.hom)
    (n : ℤ) (h : NatTrans.CommShiftCore τ₀ n) : NatTrans.CommShiftCore τ₁ n := by
  constructor
  ext A
  rw [← cancel_epi (eF.hom.app (A⟦n⟧))]
  have hcA := congr_app hc A
  have hcn := congr_app hc (A⟦n⟧)
  dsimp at hcA hcn
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← NatTrans.shift_app_comm_assoc eF.hom, ← Functor.map_comp, hcA,
    Functor.map_comp, h.shift_app_comm_assoc, NatTrans.shift_app_comm]
  rw [← reassoc_of% hcn]

-- Naturality in the middle tensor factor transports the reassociation square.
private theorem associator_core_of_iso_middle
    {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [(curriedTensor C).CommShift₂Int]
    {K₀ K : C} (e : K₀ ≅ K) (M : C) (n : ℤ)
    (h : NatTrans.CommShiftCore (tensorRightTensor K₀ M).hom n) :
    NatTrans.CommShiftCore (tensorRightTensor K M).hom n := by
  let eF := (curriedTensor C).flip.mapIso (e ⊗ᵢ Iso.refl M)
  let eG := Functor.isoWhiskerRight ((curriedTensor C).flip.mapIso e) (tensorRight M)
  have : NatTrans.CommShift eF.hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) (e ⊗ᵢ Iso.refl M).hom
  have : NatTrans.CommShift ((curriedTensor C).flip.mapIso e).hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) e.hom
  have : NatTrans.CommShift eG.hom ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerRight ((curriedTensor C).flip.mapIso e).hom (tensorRight M)) ℤ
    infer_instance
  apply core_of_commShift_iso (tensorRightTensor K₀ M).hom
    (tensorRightTensor K M).hom eF eG _ n h
  ext A
  change A ◁ (e.hom ⊗ₘ 𝟙 M) ≫ (α_ A K M).inv =
    (α_ A K₀ M).inv ≫ (A ◁ e.hom) ▷ M
  simpa only [tensorHom_id] using associator_inv_naturality_middle A e.hom M

-- Naturality in the final tensor factor transports the reassociation square.
private theorem associator_core_of_iso_right
    {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [(curriedTensor C).CommShift₂Int]
    (K : C) {M₀ M : C} (e : M₀ ≅ M) (n : ℤ)
    (h : NatTrans.CommShiftCore (tensorRightTensor K M₀).hom n) :
    NatTrans.CommShiftCore (tensorRightTensor K M).hom n := by
  let eF := (curriedTensor C).flip.mapIso (Iso.refl K ⊗ᵢ e)
  let eG := Functor.isoWhiskerLeft (tensorRight K) ((curriedTensor C).flip.mapIso e)
  have : NatTrans.CommShift eF.hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) (Iso.refl K ⊗ᵢ e).hom
  have : NatTrans.CommShift ((curriedTensor C).flip.mapIso e).hom ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) e.hom
  have : NatTrans.CommShift eG.hom ℤ := by
    change NatTrans.CommShift
      (Functor.whiskerLeft (tensorRight K) ((curriedTensor C).flip.mapIso e).hom) ℤ
    infer_instance
  apply core_of_commShift_iso (tensorRightTensor K M₀).hom
    (tensorRightTensor K M).hom eF eG _ n h
  ext A
  change A ◁ (𝟙 K ⊗ₘ e.hom) ≫ (α_ A K M).inv =
    (α_ A K M₀).inv ≫ (A ⊗ K) ◁ e.hom
  simpa only [id_tensorHom] using associator_inv_naturality_right A K e.hom

-- Localization inverts a K-flat resolution of a complex representing the derived object.
private theorem exists_kFlat_derived_iso (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X) :
    ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
      CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) (DerivedCategory.Q.objPreimage K)
  have : QuasiIso s := hs
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩


/-- Moving a translation out of the first factor commutes with reassociation.
This concerns only the associator and the tensor-shift comparisons, without any unitors.
Source: Stacks Project, Tag 06YH, total tensor localization; the triple-totalization
step of lem-sc-scheme-canonical-shift-unit-associativity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-associator).

Proof. Use schemeCanonicalTensorShift_associator_kFlat_one for shift one at
three K-flat representatives. Every derived object is isomorphic to Q(P) for a
K-flat P: take a K-flat resolution of Q.objPreimage and localize its augmentation.
First extend the square in A by naturality of the two transformations forming
its sides, cancelling the image of the representative isomorphism. Then extend
in M and K using associator naturality and the tensor-morphism shift squares of
CommShift₂Int. This proves CommShiftCore for the natural transformation
(tensorRightTensor K M).hom at shift one. Expand the shift-addition formula;
cancel its invertible comparisons and use faithfulness of shift by one to
recover the shift-minus-one square from the zero square. Integer induction and
CommShiftCore.add give the square for every n. Evaluating at A and expanding
the composite-functor shift comparison gives precisely the displayed identity.
The K-flat representative calculation is a separate theorem; all transport,
cancellation, and integer induction here are proved in Lean. -/
theorem schemeCanonicalTensorShift_associator (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (A K M : schemeDerivedCategory X) (n : ℤ) :
    letI := schemeCanonicalTensorShift X
    letI : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
      fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
    ((tensorRight (K ⊗ M)).commShiftIso n).hom.app A ≫ (α_ A K M).inv⟦n⟧' =
      (α_ (A⟦n⟧) K M).inv ≫
        (((tensorRight K).commShiftIso n).hom.app A) ▷ M ≫
        ((tensorRight M).commShiftIso n).hom.app (A ⊗ K) := by
  let := schemeCanonicalTensorShift X
  let : ∀ B : schemeDerivedCategory X, (tensorRight B).CommShift ℤ :=
    fun B ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) B
  have h : NatTrans.CommShiftCore (tensorRightTensor K M).hom (1 : ℤ) := by
    obtain ⟨T, hT, ⟨eK⟩⟩ := exists_kFlat_derived_iso X K
    obtain ⟨U, hU, ⟨eM⟩⟩ := exists_kFlat_derived_iso X M
    apply associator_core_of_iso_middle eK M (1 : ℤ)
    apply associator_core_of_iso_right (DerivedCategory.Q.obj T) eM (1 : ℤ)
    apply core_of_iso_representatives
      (tensorRightTensor (DerivedCategory.Q.obj T) (DerivedCategory.Q.obj U)).hom
      (fun P ↦ DerivedCategory.Q.obj P) (CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf))
      (exists_kFlat_derived_iso X)
    intro P hP
    simpa only [tensorRightTensor_hom_app, Functor.commShiftIso_comp_hom_app,
      tensorRight, Functor.flip, curriedTensor,
      Functor.comp_obj] using schemeCanonicalTensorShift_associator_kFlat_one X P T U hP hT hU
  have := shift_of_one (tensorRightTensor K M).hom h
  simpa only [tensorRightTensor_hom_app, Functor.commShiftIso_comp_hom_app,
    tensorRight, Functor.flip, curriedTensor,
    Functor.comp_obj] using NatTrans.shift_app_comm (tensorRightTensor K M).hom n A

end AlgebraicGeometry
