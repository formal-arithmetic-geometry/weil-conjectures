/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Mates of restricted adjunctions

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions, and let `L₁₀ ⊣ R₁₀`, `L₂₀ ⊣ R₂₀` be adjunctions
between categories mapping to the source and target categories by functors `iA`, `iB`, `iA'`,
`iB'` (typically inclusions of full subcategories), compatible with the original ones up to given
isomorphisms, as for `CategoryTheory.Adjunction.restrictFullyFaithful`. If a 2-square `α₀`
between the restricted functors is the restriction of a 2-square `α`, then the mate of `α₀` is
the restriction of the mate of `α`.

## Main results

- `CategoryTheory.map_mateEquiv_app_of_restrict`: the mate of a restricted 2-square is the
  restriction of the mate.
- `CategoryTheory.Adjunction.map_restrictFullyFaithful_ofNatIsoLeft_unit_app` and
  `CategoryTheory.Adjunction.map_restrictFullyFaithful_ofNatIsoLeft_counit_app`: the unit and the
  counit of a restriction of an adjunction transported along an isomorphism of left adjoints, in
  the form required by `CategoryTheory.map_mateEquiv_app_of_restrict`.
-/

@[expose] public section

namespace CategoryTheory

open Category

variable {𝒜 ℬ 𝒜' ℬ' 𝒜₀ ℬ₀ 𝒜'₀ ℬ'₀ : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒜']
  [Category* ℬ'] [Category* 𝒜₀] [Category* ℬ₀] [Category* 𝒜'₀] [Category* ℬ'₀]
  {iA : 𝒜₀ ⥤ 𝒜} {iB : ℬ₀ ⥤ ℬ} {iA' : 𝒜'₀ ⥤ 𝒜'} {iB' : ℬ'₀ ⥤ ℬ'}
  {L₁ : 𝒜 ⥤ ℬ} {R₁ : ℬ ⥤ 𝒜} {L₂ : 𝒜' ⥤ ℬ'} {R₂ : ℬ' ⥤ 𝒜'} {G : 𝒜 ⥤ 𝒜'} {H : ℬ ⥤ ℬ'}
  {L₁₀ : 𝒜₀ ⥤ ℬ₀} {R₁₀ : ℬ₀ ⥤ 𝒜₀} {L₂₀ : 𝒜'₀ ⥤ ℬ'₀} {R₂₀ : ℬ'₀ ⥤ 𝒜'₀} {G₀ : 𝒜₀ ⥤ 𝒜'₀}
  {H₀ : ℬ₀ ⥤ ℬ'₀}

/-- The components of the mate of a 2-square. -/
lemma mateEquiv_app_eq {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (Y : B) :
    (mateEquiv adj₁ adj₂ α).app Y = adj₂.unit.app (G.obj (R₁.obj Y)) ≫
      R₂.map (α.app (R₁.obj Y)) ≫ R₂.map (H.map (adj₁.counit.app Y)) := by
  simp [mateEquiv_apply]

/-- **The mate of a restricted 2-square is the restriction of the mate.** Let `L₁ ⊣ R₁` and
`L₂ ⊣ R₂` be adjunctions with restrictions `L₁₀ ⊣ R₁₀` and `L₂₀ ⊣ R₂₀` along functors `iA`, `iB`,
`iA'`, `iB'`, compatible with the given isomorphisms `eL₁`, `eR₁`, `eL₂`, `eR₂` (hypotheses `hε₁`
on the counit of the first adjunction and `hη₂` on the unit of the second one). If the 2-square
`α₀ : G₀ ⋙ L₂₀ ⟶ L₁₀ ⋙ H₀` is the restriction of `α : G ⋙ L₂ ⟶ L₁ ⋙ H` along isomorphisms
`eG`, `eH` (hypothesis `hα`), then the mate `R₁₀ ⋙ G₀ ⟶ H₀ ⋙ R₂₀` of `α₀` is the restriction of
the mate of `α`. -/
lemma map_mateEquiv_app_of_restrict (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁₀ : L₁₀ ⊣ R₁₀)
    (adj₂₀ : L₂₀ ⊣ R₂₀) (eL₁ : iA ⋙ L₁ ≅ L₁₀ ⋙ iB) (eR₁ : iB ⋙ R₁ ≅ R₁₀ ⋙ iA)
    (eL₂ : iA' ⋙ L₂ ≅ L₂₀ ⋙ iB') (eR₂ : iB' ⋙ R₂ ≅ R₂₀ ⋙ iA') (eG : iA ⋙ G ≅ G₀ ⋙ iA')
    (eH : iB ⋙ H ≅ H₀ ⋙ iB')
    (hε₁ : ∀ Y, iB.map (adj₁₀.counit.app Y) =
      eL₁.inv.app (R₁₀.obj Y) ≫ L₁.map (eR₁.inv.app Y) ≫ adj₁.counit.app (iB.obj Y))
    (hη₂ : ∀ X, iA'.map (adj₂₀.unit.app X) =
      adj₂.unit.app (iA'.obj X) ≫ R₂.map (eL₂.hom.app X) ≫ eR₂.hom.app (L₂₀.obj X))
    (α : TwoSquare G L₁ L₂ H) (α₀ : TwoSquare G₀ L₁₀ L₂₀ H₀)
    (hα : ∀ X, iB'.map (α₀.app X) = eL₂.inv.app (G₀.obj X) ≫ L₂.map (eG.inv.app X) ≫
      α.app (iA.obj X) ≫ H.map (eL₁.hom.app X) ≫ eH.hom.app (L₁₀.obj X))
    (Y : ℬ₀) :
    iA'.map ((mateEquiv adj₁₀ adj₂₀ α₀).app Y) =
      eG.inv.app (R₁₀.obj Y) ≫ G.map (eR₁.inv.app Y) ≫ (mateEquiv adj₁ adj₂ α).app (iB.obj Y) ≫
        R₂.map (eH.hom.app Y) ≫ eR₂.hom.app (H₀.obj Y) := by
  have hR₂ {Z Z' : ℬ'₀} (φ : Z ⟶ Z') :
      iA'.map (R₂₀.map φ) = eR₂.inv.app Z ≫ R₂.map (iB'.map φ) ≫ eR₂.hom.app Z' := by
    rw [← cancel_epi (eR₂.hom.app Z), Iso.hom_inv_id_app_assoc]
    simpa using (eR₂.hom.naturality φ).symm
  have hH {Z Z' : ℬ₀} (φ : Z ⟶ Z') :
      iB'.map (H₀.map φ) = eH.inv.app Z ≫ H.map (iB.map φ) ≫ eH.hom.app Z' := by
    rw [← cancel_epi (eH.hom.app Z), Iso.hom_inv_id_app_assoc]
    simpa using (eH.hom.naturality φ).symm
  rw [mateEquiv_app_eq, mateEquiv_app_eq]
  have hu := adj₂.unit.naturality (eG.inv.app (R₁₀.obj Y) ≫ G.map (eR₁.inv.app Y))
  have hα' := α.naturality (eR₁.inv.app Y)
  simp only [Functor.id_map, Functor.comp_map, Functor.map_comp, Functor.comp_obj, assoc] at hu hα'
  simp only [Functor.map_comp, hη₂, hR₂, hα, hH, hε₁, assoc, Iso.hom_inv_id_app_assoc,
    reassoc_of% hu]
  simp only [← Functor.map_comp_assoc]
  congr 2
  simp only [Iso.hom_inv_id_app_assoc, Functor.map_comp, assoc, reassoc_of% hα']
  simp only [Iso.hom_inv_id_app_assoc, Functor.id_obj, ← Functor.map_comp_assoc,
    ← Functor.map_comp]

namespace Adjunction

variable {C D C₀ D₀ : Type*} [Category* C] [Category* D] [Category* C₀] [Category* D₀]
  {iC : C₀ ⥤ C} {iD : D₀ ⥤ D} {L L' : C ⥤ D} {R : D ⥤ C} {L₀ : C₀ ⥤ D₀} {R₀ : D₀ ⥤ C₀}

/-- The unit of the restriction of an adjunction transported along an isomorphism `e : L ≅ L'` of
left adjoints. -/
lemma map_restrictFullyFaithful_ofNatIsoLeft_unit_app (adj : L ⊣ R) (e : L ≅ L')
    (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful) (comm1 : iC ⋙ L' ≅ L₀ ⋙ iD)
    (comm2 : iD ⋙ R ≅ R₀ ⋙ iC) (X : C₀) :
    iC.map (((adj.ofNatIsoLeft e).restrictFullyFaithful hiC hiD comm1 comm2).unit.app X) =
      adj.unit.app (iC.obj X) ≫ R.map ((Functor.isoWhiskerLeft iC e ≪≫ comm1).hom.app X) ≫
        comm2.hom.app (L₀.obj X) := by
  simp

/-- The counit of the restriction of an adjunction transported along an isomorphism `e : L ≅ L'`
of left adjoints. -/
lemma map_restrictFullyFaithful_ofNatIsoLeft_counit_app (adj : L ⊣ R) (e : L ≅ L')
    (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful) (comm1 : iC ⋙ L' ≅ L₀ ⋙ iD)
    (comm2 : iD ⋙ R ≅ R₀ ⋙ iC) (Y : D₀) :
    iD.map (((adj.ofNatIsoLeft e).restrictFullyFaithful hiC hiD comm1 comm2).counit.app Y) =
      (Functor.isoWhiskerLeft iC e ≪≫ comm1).inv.app (R₀.obj Y) ≫ L.map (comm2.inv.app Y) ≫
        adj.counit.app (iD.obj Y) := by
  simp

end Adjunction

end CategoryTheory
