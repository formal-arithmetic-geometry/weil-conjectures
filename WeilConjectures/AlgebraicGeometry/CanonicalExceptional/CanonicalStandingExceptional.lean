/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import
  WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek

/-! # Exceptional Hom correspondence with the canonical compact-support comparison

The proof follows the bounded-origin argument of ConstructibleUpperShriek, retaining
its exceptional functor and replacing only the chosen proper comparison by its counit mate.
Source: latest blueprint sec-six-functors-basics/sk-thm-existence,
def-weil-exceptional-inverse-image.md, comparison-class adjunction paragraph.
(blueprint: lem-pur-canonical-standing-exceptional).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Abelian Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry
open Scheme
namespace ProEtale.CanonicalExceptional

attribute [local implicit_reducible] ProEtale.rightDerivedLowerShriek
  Etale.rightDerivedLowerShriek ProEtale.rightDerivedUpperShriek

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
  [CompactSpace Y]

/-- The exceptional counit formed using the canonical proper/open comparison. -/
noncomputable def rightDerivedUpperShriekCounit
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.TStructure.t.plus L) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj ((R(f)^![Λ]).obj L) ⟶ L :=
  ((compactSupportSiteComparison Λ (HasCompactification.compactification f)).app
      ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL⟩).hom ≫
    D(ν^*(Y)[ModuleCat.{u + 1} Λ]).map ((Etale.rightDerivedUpperShriekAdjunction Λ f).counit.app _)
        ≫
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).counit.app L

/-- The key computation behind `rightDerivedUpperShriekHomEquiv`: for `K'` bounded below,
`g ↦ Rf_! g ≫ ε_L` sends `ν^* h`, for `h : K' ⟶ f^× Rν_* L`, to the image of `h` under the chain
of adjunction bijections, read through the compact-support comparison at `K'`. -/
lemma rightDerivedLowerShriek_map_mapDerivedCategory_map_comp_counit
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK' : DerivedCategory.TStructure.t.plus K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L)
    (h : K' ⟶ (Etale.rightDerivedUpperShriek Λ f).obj (R(ν_*(Y)[ModuleCat.{u + 1} Λ]).obj L)) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map (D(ν^*(X)[ModuleCat.{u + 1}
        Λ]).map h) ≫
        rightDerivedUpperShriekCounit f L hL =
      ((compactSupportSiteComparison Λ (HasCompactification.compactification f)).app
        ⟨K', hK'⟩).hom ≫
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _).symm
          (((Etale.rightDerivedUpperShriekAdjunction Λ f).homEquiv _ _).symm h) := by
  have hn := (compactSupportSiteComparison Λ
    (HasCompactification.compactification f)).hom.naturality
    (X := ⟨K', hK'⟩) (Y := ⟨_, plus_etaleRightDerivedUpperShriek_obj f hL⟩)
    (ObjectProperty.homMk h)
  dsimp at hn
  change (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).map h) ≫ _ =
    _ ≫ D(ν^*(Y)[ModuleCat.{u + 1} Λ]).map
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map h) at hn
  simp only [rightDerivedUpperShriekCounit, Adjunction.homEquiv_counit, Functor.map_comp,
    Category.assoc, Iso.app_hom]
  rw [reassoc_of% hn]

/-- For `K'` bounded below and `L` bounded below, `g ↦ Rf_! g ≫ ε_L` is a bijection
`Hom(ν^* K', Rf^! L) ≃ Hom(Rf_! ν^* K', L)`. -/
lemma bijective_rightDerivedLowerShriek_map_comp_counit_of_plus
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK' : DerivedCategory.TStructure.t.plus K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) :
    Function.Bijective (fun g : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K' ⟶ (R(f)^![Λ]).obj L ↦
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map g ≫
          rightDerivedUpperShriekCounit f L hL) := by
  let E := (((Etale.rightDerivedUpperShriekAdjunction Λ f).homEquiv K' _).symm.trans
    ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).symm).trans
      (((compactSupportSiteComparison Λ (HasCompactification.compactification f)).app ⟨K',
          hK'⟩).symm.homFromEquiv (Z := L))
  have hcomp : (fun g : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K' ⟶ (R(f)^![Λ]).obj L ↦
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map g ≫
          rightDerivedUpperShriekCounit f L hL) ∘
        (fun h ↦ D(ν^*(X)[ModuleCat.{u + 1} Λ]).map h) = ⇑E := by
    ext h
    exact rightDerivedLowerShriek_map_mapDerivedCategory_map_comp_counit f hK' hL h
  have hν := bijective_comparisonUpperStar_mapDerivedCategory_map K' _
    (plus_etaleRightDerivedUpperShriek_obj f hL)
  refine (Function.Bijective.of_comp_iff _ hν).1 ?_
  rw [hcomp]
  exact E.bijective

/-- For `K` bounded below of étale origin and `L` bounded below, `g ↦ Rf_! g ≫ ε_L` is a
bijection `Hom(K, Rf^! L) ≃ Hom(Rf_! K, L)`. -/
lemma bijective_rightDerivedLowerShriek_map_comp_counit
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) :
    Function.Bijective (fun g : K ⟶ (R(f)^![Λ]).obj L ↦
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map g ≫
          rightDerivedUpperShriekCounit f L hL) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := hK
  have h : (fun g : K ⟶ (R(f)^![Λ]).obj L ↦
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map g ≫
          rightDerivedUpperShriekCounit f L hL) =
      ⇑((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).mapIso e).homFromEquiv ∘
        (fun g : D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K' ⟶ (R(f)^![Λ]).obj L ↦
          (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map g ≫
              rightDerivedUpperShriekCounit f L hL) ∘
        ⇑e.symm.homFromEquiv := by
    ext g
    simp only [Function.comp_apply, Iso.homFromEquiv_apply, Iso.symm_inv, Functor.mapIso_inv,
      Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  rw [h]
  exact ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).mapIso
      e).homFromEquiv.bijective.comp
    ((bijective_rightDerivedLowerShriek_map_comp_counit_of_plus f hK' hL).comp
      e.symm.homFromEquiv.bijective)

/-- The exceptional Hom correspondence with the canonical compact-support counit.
Source: comparison-class adjunction in def-weil-exceptional-inverse-image.md
(blueprint: lem-pur-canonical-standing-exceptional).
Proof: on a compared bounded ordinary source, inverse transposition is the chain of
ordinary exceptional and site adjunctions after the compact-support comparison.
Full faithfulness of comparison makes this a bijection. Transport along an origin
isomorphism gives the bijection for every bounded-below object of etale origin. -/
noncomputable def rightDerivedUpperShriekHomEquiv
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) :
    ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K ⟶ L) ≃ (K ⟶ (R(f)^![Λ]).obj L)
        :=
  (Equiv.ofBijective _ (bijective_rightDerivedLowerShriek_map_comp_counit f hK hL)).symm

@[simp]
lemma rightDerivedUpperShriekHomEquiv_symm_apply
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) (g : K ⟶ (R(f)^![Λ]).obj L) :
    (rightDerivedUpperShriekHomEquiv f hK hL).symm g =
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map g ≫
          rightDerivedUpperShriekCounit f L hL :=
  rfl

/-- Naturality of the exceptional adjunction in the source. -/
lemma rightDerivedUpperShriekHomEquiv_naturality_left_symm
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K) (hK' :
        DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) (φ : K ⟶ K') (g : K' ⟶ (R(f)^![Λ]).obj L) :
    (rightDerivedUpperShriekHomEquiv f hK hL).symm (φ ≫ g) =
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map φ ≫
        (rightDerivedUpperShriekHomEquiv f hK' hL).symm g := by
  simp

/-- Naturality of the canonical exceptional Hom correspondence in its source. -/
lemma rightDerivedUpperShriekHomEquiv_naturality_left
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    (hK' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K')
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L) (φ : K ⟶ K')
    (g : (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K' ⟶ L) :
    rightDerivedUpperShriekHomEquiv f hK hL
        ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map φ ≫ g) =
      φ ≫ rightDerivedUpperShriekHomEquiv f hK' hL g := by
  rw [← Equiv.eq_symm_apply, rightDerivedUpperShriekHomEquiv_naturality_left_symm f hK hK',
    Equiv.symm_apply_apply]

/-- On a compared bounded ordinary source, the canonical inverse-counit bijection is
exactly the two-adjunction Hom chain. -/
theorem homEquiv_on_comparison
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : DerivedCategory.TStructure.t.plus M)
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.TStructure.t.plus L)
    (z : (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
      (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj M) ⟶ L) :
    rightDerivedUpperShriekHomEquiv f
        (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hM) hL z =
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).map
        ((Etale.rightDerivedUpperShriekAdjunction Λ f).homEquiv _ _
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _
            ((compactSupportSiteComparison Λ
              (HasCompactification.compactification f)).inv.app ⟨M, hM⟩ ≫ z))) := by
  apply (rightDerivedUpperShriekHomEquiv f
    (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hM) hL).symm.injective
  rw [Equiv.symm_apply_apply, rightDerivedUpperShriekHomEquiv_symm_apply,
    rightDerivedLowerShriek_map_mapDerivedCategory_map_comp_counit f hM hL]
  simp only [DerivedCategory.Plus.ι, ObjectProperty.ι_obj,
    Etale.rightDerivedLowerShriek, Equiv.symm_apply_apply, Iso.app_hom,
    Iso.hom_inv_id_app_assoc]

/-- Realizing an ordinary map and then taking the canonical transpose gives its
ordinary adjunct followed by the image of the comparison-adjunction unit. -/
theorem homEquiv_compare_map
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : DerivedCategory.TStructure.t.plus M)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.TStructure.t.plus (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj K))
    (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj M ⟶ K) :
    rightDerivedUpperShriekHomEquiv f
      (DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj hM) hK
      ((compactSupportSiteComparison Λ (HasCompactification.compactification f)).hom.app
        ⟨M, hM⟩ ≫ D(ν^*(Y)[ModuleCat.{u + 1} Λ]).map t) =
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).map
        ((Etale.rightDerivedUpperShriekAdjunction Λ f).homEquiv _ _ t) ≫
      D(ν^*(X)[ModuleCat.{u + 1} Λ]).map
        ((Etale.rightDerivedUpperShriek Λ f).map
          ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app K)) := by
  rw [homEquiv_on_comparison f M hM]
  simp only [Iso.inv_hom_id_app_assoc, DerivedCategory.Plus.ι, ObjectProperty.ι_obj]
  have he : (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ _
      (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).map t) =
      t ≫ (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.app K := by
    rw [Adjunction.homEquiv_unit]
    exact ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).unit.naturality t).symm
  rw [he, Adjunction.homEquiv_naturality_right, Functor.map_comp]

/-- The unique change from the canonical counit to the standing counit.
Source: uniqueness of the comparison-class adjunction
(blueprint: lem-pur-canonical-standing-exceptional).
Proof: transpose each counit with the other Hom correspondence. Inverse
transposition and functoriality show that the resulting two endomorphisms compose
to the identity: both have the same inverse transpose as the identity. -/
def comparisonIso
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : DerivedCategory.TStructure.t.plus L) :
    (ProEtale.rightDerivedUpperShriek Λ f).obj L ≅
      (ProEtale.rightDerivedUpperShriek Λ f).obj L := by
  let hR := plusEtaleOrigin_rightDerivedUpperShriek_obj f hL
  let h := ProEtale.rightDerivedUpperShriekHomEquiv f hR hL
    (rightDerivedUpperShriekCounit f L hL)
  let i := rightDerivedUpperShriekHomEquiv f hR hL
    (ProEtale.rightDerivedUpperShriekCounit f L hL)
  have hh := (ProEtale.rightDerivedUpperShriekHomEquiv f hR hL).symm_apply_apply
    (rightDerivedUpperShriekCounit f L hL)
  have hi := (rightDerivedUpperShriekHomEquiv f hR hL).symm_apply_apply
    (ProEtale.rightDerivedUpperShriekCounit f L hL)
  change (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map h ≫
    ProEtale.rightDerivedUpperShriekCounit f L hL =
      rightDerivedUpperShriekCounit f L hL at hh
  change (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map i ≫
    rightDerivedUpperShriekCounit f L hL =
      ProEtale.rightDerivedUpperShriekCounit f L hL at hi
  refine ⟨h, i, ?_, ?_⟩
  · apply (rightDerivedUpperShriekHomEquiv f hR hL).symm.injective
    change (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map (h ≫ i) ≫
      rightDerivedUpperShriekCounit f L hL =
        (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map (𝟙 _) ≫
          rightDerivedUpperShriekCounit f L hL
    rw [Functor.map_comp, Category.assoc, hi, hh,
      CategoryTheory.Functor.map_id, Category.id_comp]
  · apply (ProEtale.rightDerivedUpperShriekHomEquiv f hR hL).symm.injective
    change (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map (i ≫ h) ≫
      ProEtale.rightDerivedUpperShriekCounit f L hL =
        (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map (𝟙 _) ≫
          ProEtale.rightDerivedUpperShriekCounit f L hL
    rw [Functor.map_comp, Category.assoc, hh, hi,
      CategoryTheory.Functor.map_id, Category.id_comp]

/-- Postcomposition by the inverse counit comparison normalizes every standing transpose.
Source: comparison-class adjunction, def-weil-exceptional-inverse-image.md
(blueprint: lem-pur-canonical-standing-exceptional).
Proof: inverse transposition with the standing counit identifies the canonical
transpose followed by the comparison with the standing transpose. Cancel that
comparison using its proved inverse identity. -/
theorem homEquiv_comparison
    {M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X M)
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.TStructure.t.plus L)
    (z : (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj M ⟶ L) :
    ProEtale.rightDerivedUpperShriekHomEquiv f hM hL z ≫ (comparisonIso f L hL).inv =
      rightDerivedUpperShriekHomEquiv f hM hL z := by
  have hh := (ProEtale.rightDerivedUpperShriekHomEquiv f
    (plusEtaleOrigin_rightDerivedUpperShriek_obj f hL) hL).symm_apply_apply
      (rightDerivedUpperShriekCounit f L hL)
  change (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
    (comparisonIso f L hL).hom ≫ ProEtale.rightDerivedUpperShriekCounit f L hL =
      rightDerivedUpperShriekCounit f L hL at hh
  have he : rightDerivedUpperShriekHomEquiv f hM hL z ≫
      (comparisonIso f L hL).hom = ProEtale.rightDerivedUpperShriekHomEquiv f hM hL z := by
    apply (ProEtale.rightDerivedUpperShriekHomEquiv f hM hL).symm.injective
    change (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
      (rightDerivedUpperShriekHomEquiv f hM hL z ≫ (comparisonIso f L hL).hom) ≫
      ProEtale.rightDerivedUpperShriekCounit f L hL = _
    rw [Functor.map_comp, Category.assoc, hh]
    exact (rightDerivedUpperShriekHomEquiv f hM hL).symm_apply_apply z
      |>.trans ((ProEtale.rightDerivedUpperShriekHomEquiv f hM hL).symm_apply_apply z).symm
  rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end ProEtale.CanonicalExceptional
end AlgebraicGeometry
