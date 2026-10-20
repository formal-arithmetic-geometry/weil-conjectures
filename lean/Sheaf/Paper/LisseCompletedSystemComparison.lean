/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.LisseCompletedSystemData
import Sheaf.Paper.LisseCompletedCoefficientIso
import Sheaf.Paper.LisseCompletedPointwiseComparison
import Sheaf.Paper.LisseCompletedTensorOperations
import Mathlib.Tactic.Choose

/-! # Completed lisse systems: existence of the normalized comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ u₆ v₆
namespace CategoryTheory
variable {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {D₁ : Type u₄} [Category.{v₄} D₁]
  {D₂ : Type u₅} [Category.{v₅} D₂] {D₃ : Type u₆} [Category.{v₆} D₃]

private theorem lift_identity (R : C₁ ⥤ D₁) (ff : R.FullyFaithful)
    (T : C₁ ⥤ C₁) (L : D₁ ⥤ D₁) (δ : R ⋙ L ≅ T ⋙ R) (i : L ≅ 𝟭 D₁) :
    ∃ j : T ≅ 𝟭 C₁, δ.hom ≫ Functor.whiskerRight j.hom R =
      Functor.whiskerLeft R i.hom := by
  let e : T ⋙ R ≅ (𝟭 C₁) ⋙ R := δ.symm ≪≫ isoWhiskerLeft R i
  let h := ff.whiskeringRight C₁
  let j := h.preimageIso e
  have hj : Functor.whiskerRight j.hom R = e.hom := h.map_preimage e.hom
  refine ⟨j, ?_⟩
  rw [hj]
  simp [e]

private theorem lift_composition (R₁ : C₁ ⥤ D₁) (R₂ : C₂ ⥤ D₂) (R₃ : C₃ ⥤ D₃)
    (ff : R₃.FullyFaithful)
    (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (T₃ : C₁ ⥤ C₃)
    (L₁ : D₁ ⥤ D₂) (L₂ : D₂ ⥤ D₃) (L₃ : D₁ ⥤ D₃)
    (δ₁ : R₁ ⋙ L₁ ≅ T₁ ⋙ R₂) (δ₂ : R₂ ⋙ L₂ ≅ T₂ ⋙ R₃)
    (δ₃ : R₁ ⋙ L₃ ≅ T₃ ⋙ R₃) (k : L₁ ⋙ L₂ ≅ L₃) :
    ∃ j : T₁ ⋙ T₂ ≅ T₃,
      Functor.whiskerLeft R₁ k.hom ≫ δ₃.hom =
        Functor.whiskerRight δ₁.hom L₂ ≫ Functor.whiskerLeft T₁ δ₂.hom ≫
          Functor.whiskerRight j.hom R₃ := by
  let e : (T₁ ⋙ T₂) ⋙ R₃ ≅ T₃ ⋙ R₃ :=
    isoWhiskerLeft T₁ δ₂.symm ≪≫ isoWhiskerRight δ₁.symm L₂ ≪≫
      isoWhiskerLeft R₁ k ≪≫ δ₃
  let h := ff.whiskeringRight C₁
  let j := h.preimageIso e
  have hj : Functor.whiskerRight j.hom R₃ = e.hom := h.map_preimage e.hom
  refine ⟨j, ?_⟩
  rw [hj]
  change _ = (isoWhiskerRight δ₁ L₂).hom ≫ (isoWhiskerLeft T₁ δ₂).hom ≫ _
  simp only [e, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.symm_hom]
  rw [← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id', Category.id_comp,
    ← whiskerRight_comp_assoc, Iso.hom_inv_id, whiskerRight_id', Category.id_comp]

private theorem descend_identity (E : C₁ ≌ C₂)
    (T : C₂ ⥤ C₂) (L : C₁ ⥤ C₁)
    (δ : L ⋙ E.functor ≅ E.functor ⋙ T) (i : L ≅ 𝟭 C₁) :
    ∃ j : T ≅ 𝟭 C₂, δ.hom ≫ Functor.whiskerLeft E.functor j.hom =
      Functor.whiskerRight i.hom E.functor := by
  let e : E.functor ⋙ T ≅ E.functor ⋙ (𝟭 C₂) :=
    δ.symm ≪≫ isoWhiskerRight i E.functor
  let h := (Equivalence.congrLeft (E := C₂) E).fullyFaithfulInverse
  let j := h.preimageIso e
  have hj : Functor.whiskerLeft E.functor j.hom = e.hom := h.map_preimage e.hom
  refine ⟨j, ?_⟩
  rw [hj]
  simp [e]

private theorem descend_composition (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) (E₃ : C₃ ≌ D₃)
    (T₁ : D₁ ⥤ D₂) (T₂ : D₂ ⥤ D₃) (T₃ : D₁ ⥤ D₃)
    (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (L₃ : C₁ ⥤ C₃)
    (δ₁ : L₁ ⋙ E₂.functor ≅ E₁.functor ⋙ T₁)
    (δ₂ : L₂ ⋙ E₃.functor ≅ E₂.functor ⋙ T₂)
    (δ₃ : L₃ ⋙ E₃.functor ≅ E₁.functor ⋙ T₃) (k : L₁ ⋙ L₂ ≅ L₃) :
    ∃ j : T₁ ⋙ T₂ ≅ T₃,
      Functor.whiskerRight k.hom E₃.functor ≫ δ₃.hom =
        Functor.whiskerLeft L₁ δ₂.hom ≫ Functor.whiskerRight δ₁.hom T₂ ≫
          Functor.whiskerLeft E₁.functor j.hom := by
  let e : E₁.functor ⋙ (T₁ ⋙ T₂) ≅ E₁.functor ⋙ T₃ :=
    isoWhiskerRight δ₁.symm T₂ ≪≫ isoWhiskerLeft L₁ δ₂.symm ≪≫
      isoWhiskerRight k E₃.functor ≪≫ δ₃
  let h := (Equivalence.congrLeft (E := D₃) E₁).fullyFaithfulInverse
  let j := h.preimageIso e
  have hj : Functor.whiskerLeft E₁.functor j.hom = e.hom := h.map_preimage e.hom
  refine ⟨j, ?_⟩
  rw [hj]
  change _ = (isoWhiskerLeft L₁ δ₂).hom ≫ (isoWhiskerRight δ₁ T₂).hom ≫ _
  simp only [e, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.symm_hom]
  rw [← whiskerRight_comp_assoc, Iso.hom_inv_id, whiskerRight_id', Category.id_comp,
    ← whiskerLeft_comp_assoc, Iso.hom_inv_id, whiskerLeft_id', Category.id_comp]
end CategoryTheory

namespace CategoryTheory
open CategoryTheory.Functor
variable {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {D₁ : Type u₄} [Category.{v₄} D₁]
  {D₂ : Type u₅} [Category.{v₅} D₂] {D₃ : Type u₆} [Category.{v₆} D₃]

private theorem mate_identity (E : C₁ ≌ D₁) (L : C₁ ⥤ C₁) (T : D₁ ⥤ D₁)
    (δ : L ⋙ E.functor ≅ E.functor ⋙ T)
    (ε : E.inverse ⋙ L ≅ T ⋙ E.inverse)
    (hm : ∀ Y, E.functor.map (ε.hom.app Y) ≫ E.counitIso.hom.app (T.obj Y) =
      δ.hom.app (E.inverse.obj Y) ≫ T.map (E.counitIso.hom.app Y))
    (i : L ≅ 𝟭 C₁) (j : T ≅ 𝟭 D₁)
    (hd : δ.hom ≫ whiskerLeft E.functor j.hom = whiskerRight i.hom E.functor) :
    ε.hom ≫ whiskerRight j.hom E.inverse = whiskerLeft E.inverse i.hom := by
  ext Y
  apply E.functor.map_injective
  apply (cancel_mono (E.counitIso.hom.app Y)).1
  change E.functor.map (ε.hom.app Y ≫ E.inverse.map (j.hom.app Y)) ≫ _ =
    E.functor.map (i.hom.app (E.inverse.obj Y)) ≫ _
  rw [E.functor.map_comp, Category.assoc]
  erw [E.counit_naturality (j.hom.app Y)]
  rw [← Category.assoc, hm]
  rw [Category.assoc]
  erw [j.hom.naturality (E.counitIso.hom.app Y)]
  rw [← Category.assoc]
  have h := congrArg (fun f => f.app (E.inverse.obj Y)) hd
  change δ.hom.app (E.inverse.obj Y) ≫ j.hom.app _ =
    E.functor.map (i.hom.app (E.inverse.obj Y)) at h
  simpa only [Functor.comp_obj, Functor.id_map] using congrArg
    (fun f => f ≫ E.counitIso.hom.app Y) h

private theorem mate_composition (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂) (E₃ : C₃ ≌ D₃)
    (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (L₃ : C₁ ⥤ C₃)
    (T₁ : D₁ ⥤ D₂) (T₂ : D₂ ⥤ D₃) (T₃ : D₁ ⥤ D₃)
    (δ₁ : L₁ ⋙ E₂.functor ≅ E₁.functor ⋙ T₁)
    (δ₂ : L₂ ⋙ E₃.functor ≅ E₂.functor ⋙ T₂)
    (δ₃ : L₃ ⋙ E₃.functor ≅ E₁.functor ⋙ T₃)
    (ε₁ : E₁.inverse ⋙ L₁ ≅ T₁ ⋙ E₂.inverse)
    (ε₂ : E₂.inverse ⋙ L₂ ≅ T₂ ⋙ E₃.inverse)
    (ε₃ : E₁.inverse ⋙ L₃ ≅ T₃ ⋙ E₃.inverse)
    (hm₁ : ∀ Y, E₂.functor.map (ε₁.hom.app Y) ≫ E₂.counitIso.hom.app (T₁.obj Y) =
      δ₁.hom.app (E₁.inverse.obj Y) ≫ T₁.map (E₁.counitIso.hom.app Y))
    (hm₂ : ∀ Y, E₃.functor.map (ε₂.hom.app Y) ≫ E₃.counitIso.hom.app (T₂.obj Y) =
      δ₂.hom.app (E₂.inverse.obj Y) ≫ T₂.map (E₂.counitIso.hom.app Y))
    (hm₃ : ∀ Y, E₃.functor.map (ε₃.hom.app Y) ≫ E₃.counitIso.hom.app (T₃.obj Y) =
      δ₃.hom.app (E₁.inverse.obj Y) ≫ T₃.map (E₁.counitIso.hom.app Y))
    (i : L₁ ⋙ L₂ ≅ L₃) (j : T₁ ⋙ T₂ ≅ T₃)
    (hd : whiskerRight i.hom E₃.functor ≫ δ₃.hom =
      whiskerLeft L₁ δ₂.hom ≫ whiskerRight δ₁.hom T₂ ≫ whiskerLeft E₁.functor j.hom) :
    whiskerLeft E₁.inverse i.hom ≫ ε₃.hom =
      whiskerRight ε₁.hom L₂ ≫ whiskerLeft T₁ ε₂.hom ≫ whiskerRight j.hom E₃.inverse := by
  ext Y
  apply E₃.functor.map_injective
  apply (cancel_mono (E₃.counitIso.hom.app (T₃.obj Y))).1
  change E₃.functor.map (i.hom.app (E₁.inverse.obj Y) ≫ ε₃.hom.app Y) ≫ _ =
    E₃.functor.map (L₂.map (ε₁.hom.app Y) ≫ ε₂.hom.app (T₁.obj Y) ≫
      E₃.inverse.map (j.hom.app Y)) ≫ _
  simp only [Functor.map_comp, Category.assoc]
  erw [E₃.counit_naturality (j.hom.app Y)]
  rw [← Category.assoc (E₃.functor.map (ε₂.hom.app _))]
  erw [hm₂]
  simp only [Category.assoc]
  rw [hm₃]
  have h := congrArg (fun f => f.app (E₁.inverse.obj Y)) hd
  change E₃.functor.map (i.hom.app _) ≫ δ₃.hom.app _ =
    δ₂.hom.app _ ≫ T₂.map (δ₁.hom.app _) ≫ j.hom.app _ at h
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  erw [← j.hom.naturality (E₁.counitIso.hom.app Y)]
  have hn := δ₂.hom.naturality (ε₁.hom.app Y)
  change E₃.functor.map (L₂.map (ε₁.hom.app Y)) ≫ δ₂.hom.app _ =
    δ₂.hom.app _ ≫ T₂.map (E₂.functor.map (ε₁.hom.app Y)) at hn
  dsimp only [Functor.comp_obj] at hn
  rw [← Category.assoc (E₃.functor.map (L₂.map (ε₁.hom.app Y))), hn]
  simp only [Functor.comp_map, Category.assoc]
  rw [← T₂.map_comp_assoc, ← hm₁, T₂.map_comp]
  simp only [Category.assoc]
  rfl
end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CompletedLisse

/-- Reduction and inverse limit identify completed integral lisse modules with normalized
finite-free etale systems. Raw rational realization is fully faithful. These comparisons
commute with all module pullbacks and finite coefficient inclusions, with the stated
normalizations and identity/composition equations.
Source: BS 6.8.4(1),(4), 5.1.5 and 6.8.2, pp.35,58--59
(blueprint: lem-per-lisse-completed-system-comparison).

Proof: Obtain the continuous integral reduction datum and its residue-normalized
coefficient isomorphism by uniqueness of limits. Use the pointwise comparison and the
normalized tensor-operation construction. Precomposition by the integral equivalence is
fully faithful on functor categories: lift the ambient tensor identity and composition
isomorphisms to the etale system categories after inserting the reduction isomorphisms.
Their defining equations are exactly reduction_id and reduction_comp. Postcomposition
by the fully faithful rational realization similarly lifts the rational tensor comparisons
to raw rational categories, giving realization_id and realization_comp.
Reconstruction is the counit mate of reduction. Apply the target equivalence, compose
with its invertible counit, use the mate equations and counit naturality, and cancel.
For identity this reduces to reduction_id. For composition, naturality of the second
reduction isomorphism moves the first reconstruction across it, and reduction_comp
finishes the equality. These are the two proved mate lemmas above. Finally retain the
four actual tensor-adjunction-unit normalizations from the operation construction.
The geometric constructions, including rank zero and empty schemes, are isolated in
the two separate source results; no further geometric hypothesis is used in this assembly. -/
theorem completed_system_comparison (l : ℕ) [Fact l.Prime] : Nonempty (System.{u} l) := by
  classical
  have hc (P : Base.{u} l) : Nonempty (Comparison l P) := by
    obtain ⟨d⟩ := integral_lisse_reduction_equivalence l P.E P.X
    obtain ⟨e, he⟩ := completed_coefficient_iso_exists l P.E P.X d
    obtain ⟨c, _, _⟩ := completed_pointwise_comparison l P d e he
    exact ⟨c⟩
  let c : ∀ P : Base.{u} l, Comparison l P := fun P => (hc P).some
  obtain ⟨o⟩ := completed_tensor_operations l c
  have etId (P : Base.{u} l) := CategoryTheory.descend_identity (c P).equivalence
    (o.operation (identity l P)).etale.functor (o.operation (identity l P)).modules.integral
    (o.operation (identity l P)).reduction (o.integralId P)
  choose ei hei using etId
  have rawId (P : Base.{u} l) := CategoryTheory.lift_identity
    (c P).rationalRealization (c P).rationalFullyFaithful
    (o.operation (identity l P)).raw (o.operation (identity l P)).modules.rational
    (o.operation (identity l P)).rational (o.rationalId P)
  choose ri hri using rawId
  have etComp (P Q S : Base.{u} l) (a : Arrow l P Q) (b : Arrow l Q S) :=
    CategoryTheory.descend_composition (c P).equivalence (c Q).equivalence (c S).equivalence
      (o.operation a).etale.functor (o.operation b).etale.functor
      (o.operation (composite l a b)).etale.functor
      (o.operation a).modules.integral (o.operation b).modules.integral
      (o.operation (composite l a b)).modules.integral
      (o.operation a).reduction (o.operation b).reduction
      (o.operation (composite l a b)).reduction (o.integralComp a b)
  choose ec hec using etComp
  have rawComp (P Q S : Base.{u} l) (a : Arrow l P Q) (b : Arrow l Q S) :=
    CategoryTheory.lift_composition (c P).rationalRealization (c Q).rationalRealization
      (c S).rationalRealization (c S).rationalFullyFaithful
      (o.operation a).raw (o.operation b).raw (o.operation (composite l a b)).raw
      (o.operation a).modules.rational (o.operation b).modules.rational
      (o.operation (composite l a b)).modules.rational
      (o.operation a).rational (o.operation b).rational
      (o.operation (composite l a b)).rational (o.rationalComp a b)
  choose rc hrc using rawComp
  refine ⟨{
    comparison := c
    operation := o.operation
    integralId := o.integralId
    etaleId := ei
    rationalId := o.rationalId
    rawId := ri
    integralId_normalization := o.integralId_normalization
    rationalId_normalization := o.rationalId_normalization
    reduction_id := hei
    reconstruction_id := ?_
    realization_id := hri
    integralComp := o.integralComp
    etaleComp := fun {P Q S} a b => ec P Q S a b
    rationalComp := o.rationalComp
    rawComp := fun {P Q S} a b => rc P Q S a b
    integralComp_normalization := o.integralComp_normalization
    rationalComp_normalization := o.rationalComp_normalization
    reduction_comp := fun {P Q S} a b => hec P Q S a b
    reconstruction_comp := ?_
    realization_comp := fun {P Q S} a b => hrc P Q S a b }⟩
  · intro P
    exact CategoryTheory.mate_identity (c P).equivalence _ _
      (o.operation (identity l P)).reduction (o.operation (identity l P)).reconstruction
      (o.reconstruction_mate (identity l P)) (o.integralId P) (ei P) (hei P)
  · intro P Q S a b
    exact CategoryTheory.mate_composition (c P).equivalence (c Q).equivalence
      (c S).equivalence _ _ _ _ _ _
      (o.operation a).reduction (o.operation b).reduction
      (o.operation (composite l a b)).reduction
      (o.operation a).reconstruction (o.operation b).reconstruction
      (o.operation (composite l a b)).reconstruction
      (o.reconstruction_mate a) (o.reconstruction_mate b)
      (o.reconstruction_mate (composite l a b))
      (o.integralComp a b) (ec P Q S a b) (hec P Q S a b)

end AlgebraicGeometry.ProEtale.CompletedLisse
