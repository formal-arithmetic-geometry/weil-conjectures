/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedDerivedTensorComparison
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexModel

/-! # Complex presentations of condensed coefficient extension

This is the coefficient algebra step of derived Hom descent. It makes no
constructibility assumption on either the source or the target of a morphism.
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl

set_option maxHeartbeats 800000 in
-- Instantiating adjunction naturality in four derived module categories needs extra heartbeats.
/-- A bounded-below derived object over a finite coefficient field has a filtered presentation by
complexes over the finite subfields, compatible with the identification of the colimit. -/
theorem exists_condensed_coefficient_complex_presentation
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E F : FiniteIntermediateField ℓ)
    (L : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)))
    (hL : DerivedCategory.TStructure.t.plus L)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (H : I ⥤ FiniteIntermediateField ℓ) [H.Final]
    (he : ∀ i, E ≤ H.obj i) (hf : ∀ i, F ≤ H.obj i) :
    ∃ N : I ⥤ CochainComplex
        (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ,
      ∃ c : Cocone N, Nonempty (IsColimit c) ∧
      (∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r)) ∧
      ∃ eΩ : DerivedCategory.Q.obj c.pt ≅
          (finiteCoefficientDerivedFromAlgCl X ℓ E).obj
            ((derivedExtendScalarsToPadicAlgCl X ℓ F).obj L),
        ∃ ei : ∀ i : I, DerivedCategory.Q.obj (N.obj i) ≅
            (finiteCoefficientDerivedRestriction X ℓ (he i)).obj
              ((derivedExtendScalarsSubfield X ℓ (hf i)).obj L),
          ∀ (i : I) (K : DerivedCategory
              (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
            (g : K ⟶ DerivedCategory.Q.obj (N.obj i)),
            finiteCoefficientDerivedAlgClHomEquiv X ℓ E K _
              ((derivedExtendScalarsCompIso X ℓ (he i)).inv.app K ≫
                (derivedExtendScalarsToPadicAlgCl X ℓ (H.obj i)).map
                    ((finiteCoefficientDerivedHomEquiv X ℓ (he i) K _).symm
                        (g ≫ (ei i).hom)) ≫
                  (derivedExtendScalarsCompIso X ℓ (hf i)).hom.app L) =
              g ≫ DerivedCategory.Q.map (c.ι.app i) ≫ eΩ.hom := by
  obtain ⟨a, ha⟩ := hL
  have : L.IsGE a := ha
  obtain ⟨C, hC, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE L a
  obtain ⟨N, c, hc, hN, eΩ, ei, hcomp⟩ :=
    exists_condensed_coefficient_complex_model X ℓ E F C H he hf
  have hbound : ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r) := by
    intro i r hr
    rw [hN i]
    exact (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ (hf i))) ⋙
      Mod.comap (padicSubfieldRingObjMap X ℓ (he i)))).map_isZero
        (C.isZero_of_isStrictlyGE a r hr)
  let eΩ' := eΩ ≪≫ (finiteCoefficientDerivedFromAlgCl X ℓ E).mapIso
    ((derivedExtendScalarsToPadicAlgCl X ℓ F).mapIso e.symm)
  let ei' := fun i ↦ ei i ≪≫ (finiteCoefficientDerivedRestriction X ℓ (he i)).mapIso
    ((derivedExtendScalarsSubfield X ℓ (hf i)).mapIso e.symm)
  refine ⟨N, c, hc, ⟨a, hbound⟩, eΩ', ei', ?_⟩
  intro i K g
  -- Establish source and target naturality before instantiating the derived module categories.
  have transport {A B D T : Type _} [Category A] [Category B] [Category D] [Category T]
      {P : A ⥤ D} {UP : D ⥤ A} (ap : P ⊣ UP)
      {R : D ⥤ T} {S : A ⥤ T} {US : T ⥤ A} (aq : S ⊣ US)
      {V : B ⥤ D} {W : B ⥤ T} (α : P ⋙ R ≅ S) (β : V ⋙ R ≅ W)
      {L₀ L₁ : B} (f : L₀ ⟶ L₁) {K₀ K₁ : A}
      (k : K₁ ⟶ K₀) (g : K₀ ⟶ UP.obj (V.obj L₀)) :
      aq.homEquiv K₁ _
        (α.inv.app K₁ ≫ R.map ((ap.homEquiv K₁ _).symm
          ((k ≫ g) ≫ UP.map (V.map f))) ≫
          β.hom.app L₁) =
      k ≫ aq.homEquiv K₀ _ (α.inv.app K₀ ≫ R.map ((ap.homEquiv K₀ _).symm g) ≫
        β.hom.app L₀) ≫ US.map (W.map f) := by
    rw [ap.homEquiv_naturality_right_symm, ap.homEquiv_naturality_left_symm]
    simp only [R.map_comp, Category.assoc]
    have hb := β.hom.naturality f
    change R.map (V.map f) ≫ β.hom.app L₁ = β.hom.app L₀ ≫ W.map f at hb
    rw [hb]
    have ha := α.inv.naturality k
    change S.map k ≫ α.inv.app K₀ = α.inv.app K₁ ≫ R.map (P.map k) at ha
    rw [← reassoc_of% ha, aq.homEquiv_naturality_left]
    simpa only [Category.assoc] using congrArg (fun q ↦ k ≫ q)
      (aq.homEquiv_naturality_right
        (α.inv.app K₀ ≫ R.map ((ap.homEquiv K₀ _).symm g) ≫ β.hom.app L₀) (W.map f))
  have ht := transport (finiteCoefficientDerivedAdjunction X ℓ (he i))
    (finiteCoefficientDerivedAlgClAdjunction X ℓ E)
    (derivedExtendScalarsCompIso X ℓ (he i))
    (derivedExtendScalarsCompIso X ℓ (hf i)) e.inv g (ei i).hom
  have hcompat := hcomp i
  simp only [finiteCoefficientDerivedHomEquiv, finiteCoefficientDerivedAlgClHomEquiv] at hcompat
  simp only [Category.assoc] at ht
  simp only [ei', eΩ', Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    finiteCoefficientDerivedHomEquiv, finiteCoefficientDerivedAlgClHomEquiv]
  refine ht.trans ?_
  simpa only [Category.assoc] using congrArg
    (fun f ↦ g ≫ f ≫ (finiteCoefficientDerivedFromAlgCl X ℓ E).map
      ((derivedExtendScalarsToPadicAlgCl X ℓ F).map e.inv)) hcompat

end AlgebraicGeometry.ProEtale
