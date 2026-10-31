/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.Algebra.Homology.InternalHomLocalizationComparison

/-! # A normalized Hom comparison from scalar telescopes

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), telescope argument.
The scalar extension is arbitrary: its normalized telescope, rather than a chosen
presentation of a localized ring, is used in the proof.
(blueprint: lem-sfb-scalar-telescope-hom-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a v w b h
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem map_scalar_identity
    {A : Type*} [Category A] [Preadditive A]
    {B : Type*} [Category B] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (n : ℕ) (X : A) :
    F.map (n • 𝟙 X) = n • 𝟙 (F.obj X) := by
  rw [F.map_nsmul, F.map_id]

private theorem model_scalar_identity
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (G : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (H : DerivedCategory A ⥤ DerivedCategory A) [H.Additive]
    (e : G ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ H)
    (n : ℕ) (P : CochainComplex A ℤ) :
    DerivedCategory.Q.map (G.map (n • 𝟙 P)) =
      DerivedCategory.Q.map (n • 𝟙 (G.obj P)) := by
  apply (cancel_mono (e.hom.app P)).1
  have he := e.hom.naturality (n • 𝟙 P)
  change DerivedCategory.Q.map (G.map (n • 𝟙 P)) ≫ e.hom.app P =
    e.hom.app P ≫ H.map (DerivedCategory.Q.map (n • 𝟙 P)) at he
  rw [he, map_scalar_identity, map_scalar_identity, map_scalar_identity]
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
    Category.id_comp]
  erw [Category.comp_id]

/-- A scalar telescope commutes with an additive derived functor when its canonical
comparison for this telescope is invertible. Both sides are identified with the
specified localization unit.

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62;
Stacks, Tags 070I and 03DB.
(blueprint: lem-sfb-scalar-telescope-hom-comparison).

Proof. Compare the literal scalar tower on the Hom representative with the Hom
representative of the input tower. Naturality of its derived identification and
additivity identify their transitions after Q. The telescope triangles therefore
give an isomorphism of their derived colimits preserving every leg. Sequential
continuity identifies the second colimit with Hom of the input colimit. The two
specified unit-normalized telescope identifications finish the comparison; their
zeroth-leg equations and unit naturality give precisely the displayed equation. -/
theorem scalarTelescope_hom_comparison
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableCoproducts A] [HasFilteredColimitsOfSize.{0, 0} A]
    [AB5OfSize.{0, 0} A]
    {B : Type b} [Category.{h} B]
    (F : DerivedCategory A ⥤ B) (U : B ⥤ DerivedCategory A) (adj : F ⊣ U)
    (p : ℕ) (G : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (H : DerivedCategory A ⥤ DerivedCategory A) [H.Additive]
    (e : G ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ H)
    (β : ∀ P : CochainComplex A ℤ,
      DerivedCategory.Q.obj (colimit (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P))) ≅
        U.obj (F.obj (DerivedCategory.Q.obj P)))
    (hβ : ∀ P : CochainComplex A ℤ,
      DerivedCategory.Q.map
          (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P)) 0) ≫ (β P).hom =
        adj.unit.app (DerivedCategory.Q.obj P))
    (P : CochainComplex A ℤ)
    (hcont : IsIso (DerivedCategory.Q.map
      (colimit.post (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P)) G))) :
    ∃ t : U.obj (F.obj (H.obj (DerivedCategory.Q.obj P))) ≅
        H.obj (U.obj (F.obj (DerivedCategory.Q.obj P))),
      adj.unit.app (H.obj (DerivedCategory.Q.obj P)) ≫ t.hom =
        H.map (adj.unit.app (DerivedCategory.Q.obj P)) := by
  let Q := DerivedCategory.Q (C := A)
  let D := Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P)
  let T := Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 (G.obj P))
  let τ : T ⋙ Q ⟶ (D ⋙ G) ⋙ Q := NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by
    intro n
    simp only [T, D, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
    simp only [Category.id_comp, Category.comp_id]
    exact (model_scalar_identity G H e p P).symm)
  let eT : T ⋙ Q ≅ (D ⋙ G) ⋙ Q :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro n m f
      exact τ.naturality f)
  obtain ⟨t, ht⟩ := LocalizationHomProof.sequential_colimit_comparison
    T (D ⋙ G) (colimit.cocone T) (colimit.isColimit T)
      (colimit.cocone (D ⋙ G)) (colimit.isColimit (D ⋙ G)) eT
  let c := t ≪≫ asIso (Q.map (colimit.post D G)) ≪≫ e.app (colimit D)
  have hc : Q.map (colimit.ι T 0) ≫ c.hom =
      (e.app P).hom ≫ H.map (Q.map (colimit.ι D 0)) := by
    dsimp only [c, Iso.trans_hom, asIso_hom]
    rw [← Category.assoc, ← Category.assoc]
    erw [ht 0]
    have hzero : (eT.app 0).hom = 𝟙 (Q.obj (G.obj P)) := rfl
    rw [hzero]
    erw [Category.id_comp]
    rw [← Q.map_comp]
    erw [colimit.ι_post]
    exact e.hom.naturality (colimit.ι D 0)
  let UF := F ⋙ U
  let t' := (UF.mapIso (e.app P)).symm ≪≫ (β (G.obj P)).symm ≪≫ c ≪≫ H.mapIso (β P)
  refine ⟨t', ?_⟩
  have hη := adj.unit.naturality (e.app P).inv
  change (e.app P).inv ≫ adj.unit.app (Q.obj (G.obj P)) =
    adj.unit.app (H.obj (Q.obj P)) ≫ UF.map (e.app P).inv at hη
  have hz : adj.unit.app (Q.obj (G.obj P)) ≫ (β (G.obj P)).inv =
      Q.map (colimit.ι T 0) := by
    rw [← hβ]
    simp only [T, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  dsimp only [t', Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← hη]
  simp only [Category.assoc]
  rw [← Category.assoc (adj.unit.app (Q.obj (G.obj P))) (β (G.obj P)).inv, hz]
  rw [← Category.assoc (Q.map (colimit.ι T 0)) c.hom, hc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← H.map_comp, hβ]

private theorem normalized_transport
    {C : Type*} [Category C] (S H : C ⥤ C) (η : 𝟭 C ⟶ S)
    {P L : C} (e : P ≅ L) (t : S.obj (H.obj P) ≅ H.obj (S.obj P))
    (ht : η.app (H.obj P) ≫ t.hom = H.map (η.app P)) :
    ∃ b : S.obj (H.obj L) ≅ H.obj (S.obj L),
      η.app (H.obj L) ≫ b.hom = H.map (η.app L) := by
  let b := (S.mapIso (H.mapIso e)).symm ≪≫ t ≪≫ H.mapIso (S.mapIso e)
  refine ⟨b, ?_⟩
  dsimp only [b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
  have hn := η.naturality (H.map e.inv)
  change H.map e.inv ≫ η.app (H.obj P) =
    η.app (H.obj L) ≫ S.map (H.map e.inv) at hn
  calc
    _ = (η.app (H.obj L) ≫ S.map (H.map e.inv)) ≫
        t.hom ≫ H.map (S.map e.hom) := by simp only [Category.assoc]
    _ = (H.map e.inv ≫ η.app (H.obj P)) ≫
        t.hom ≫ H.map (S.map e.hom) := by rw [← hn]
    _ = H.map e.inv ≫ (η.app (H.obj P) ≫ t.hom) ≫
        H.map (S.map e.hom) := by simp only [Category.assoc]
    _ = H.map (e.inv ≫ η.app P ≫ S.map e.hom) := by
      rw [ht, H.map_comp, H.map_comp]
    _ = H.map (η.app L) := by
      rw [← η.naturality e.hom]
      simp only [Functor.id_map, Iso.inv_hom_id_assoc]

/-- A unit-normalized internal-Hom comparison is invertible once scalar telescopes
commute with its representative functor. The codomain lies in the reflective image.

Source: Bhatt--Scholze, Lemma 6.8.12 and Proposition 6.8.14(2), pp. 61--62.
(blueprint: lem-sfb-scalar-telescope-hom-comparison).

Proof. Choose a strictly bounded-below representative of L. The telescope comparison
above gives the required isomorphism for its image under Q. Transport along the
representative isomorphism by naturality of the unit. Fullness of restriction makes
precomposition with the unit injective on maps to a restricted object. Thus the
transported isomorphism equals the given unit-normalized comparison. -/
theorem scalarTelescope_normalized_comparison_isIso
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableCoproducts A] [HasFilteredColimitsOfSize.{0, 0} A]
    [AB5OfSize.{0, 0} A]
    {B : Type b} [Category.{h} B]
    (F : DerivedCategory A ⥤ B) (U : B ⥤ DerivedCategory A) (adj : F ⊣ U) [U.Full]
    (p : ℕ) (G : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (H : DerivedCategory A ⥤ DerivedCategory A) [H.Additive]
    (e : G ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ H)
    (β : ∀ P : CochainComplex A ℤ,
      DerivedCategory.Q.obj (colimit (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P))) ≅
        U.obj (F.obj (DerivedCategory.Q.obj P)))
    (hβ : ∀ P : CochainComplex A ℤ,
      DerivedCategory.Q.map
          (colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P)) 0) ≫ (β P).hom =
        adj.unit.app (DerivedCategory.Q.obj P))
    (hc : ∀ (P : CochainComplex A ℤ) (c : ℤ), P.IsStrictlyGE c →
      IsIso (DerivedCategory.Q.map
        (colimit.post (Functor.ofSequence (fun _ : ℕ ↦ p • 𝟙 P)) G)))
    (L : DerivedCategory A) (hL : ∃ c : ℤ, L.IsGE c)
    (V : B) (eV : H.obj (U.obj (F.obj L)) ≅ U.obj V)
    (ρ : U.obj (F.obj (H.obj L)) ⟶ H.obj (U.obj (F.obj L)))
    (hρ : adj.unit.app (H.obj L) ≫ ρ = H.map (adj.unit.app L)) : IsIso ρ := by
  obtain ⟨c, hcL⟩ := hL
  have := hcL
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE L c
  have := hc P c hP
  obtain ⟨t, ht⟩ := scalarTelescope_hom_comparison F U adj p G H e β hβ P (hc P c hP)
  obtain ⟨b, hb⟩ := normalized_transport (F ⋙ U) H adj.unit eP.symm t ht
  have he : b.hom = ρ := by
    apply (cancel_mono eV.hom).mp
    apply LocalizationHomProof.unit_precomp_injective adj (H.obj L) V
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ eV.hom) (hb.trans hρ.symm)
  rw [← he]
  infer_instance

end CategoryTheory
