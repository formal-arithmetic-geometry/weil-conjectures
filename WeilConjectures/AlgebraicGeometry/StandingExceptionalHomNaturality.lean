/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition

/-! # Naturality of the specified exceptional Hom bijection

Source: blueprint thm-sf-ambient-adjoint-class, the four natural Hom identifications
(blueprint: lem-pur-standing-exceptional-hom-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [CompactSpace Y]

private def representativeHom
    (M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : _root_.DerivedCategory.TStructure.t.plus L) :=
  ((fixedCompactSupportComparisonIso Λ
    (HasCompactification.compactification f)).app M).homFromEquiv.trans
    (((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv _ L).trans
      (((Etale.rightDerivedUpperShriekAdjunction Λ f).homEquiv M.obj _).trans
        (Equiv.ofBijective
          (fun a ↦ (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a)
          (bijective_comparisonUpperStar_mapDerivedCategory_map _ _
            (plus_etaleRightDerivedUpperShriek_obj f hL)))))

private theorem representativeHom_left
    (M M' : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : _root_.DerivedCategory.TStructure.t.plus L) (a : M ⟶ M')
    (b : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj M'.obj) ⟶ L) :
    representativeHom Λ f M L hL
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a.hom) ≫ b) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a.hom ≫
        representativeHom Λ f M' L hL b := by
  have h := (fixedCompactSupportComparisonIso Λ
    (HasCompactification.compactification f)).inv.naturality_assoc a b
  change (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategory.map
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map a.hom) ≫
      (fixedCompactSupportComparisonIso Λ
        (HasCompactification.compactification f)).inv.app M' ≫ b =
    (fixedCompactSupportComparisonIso Λ
      (HasCompactification.compactification f)).inv.app M ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.map a.hom) ≫ b at h
  simp only [representativeHom, Equiv.trans_apply, Equiv.ofBijective_apply]
  dsimp only [Iso.homFromEquiv, Equiv.coe_fn_mk]
  erw [← h]
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Functor.map_comp]
  rfl

private theorem representativeHom_right
    (M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L L' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)))
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hL' : _root_.DerivedCategory.TStructure.t.plus L')
    (a : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj M.obj) ⟶ L)
    (b : L ⟶ L') :
    representativeHom Λ f M L' hL' (a ≫ b) =
      representativeHom Λ f M L hL a ≫ (rightDerivedUpperShriek Λ f).map b := by
  simp only [representativeHom, Equiv.trans_apply, Equiv.ofBijective_apply]
  dsimp only [Iso.homFromEquiv, Equiv.coe_fn_mk]
  erw [← Category.assoc]
  erw [(derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y).homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right, Functor.map_comp]
  rfl

/-- The specified exceptional Hom bijection is natural in its etale-origin source.
Source: blueprint thm-sf-ambient-adjoint-class, four natural Hom identifications
(blueprint: lem-pur-standing-exceptional-hom-naturality).

Proof: choose the two bounded-below etale representatives retained by the definition.
Full faithfulness lifts the source arrow conjugated by their witness isomorphisms.
The fixed compact-support comparison and both adjunction Hom bijections are natural
on those representatives. Apply that naturality to the lifted arrow, then cancel
both witness isomorphisms. This proves the assertion for every ambient source arrow,
independently of the choices of witnesses. No ambient exceptional adjoint is used. -/
theorem standingExceptionalHomEquiv_naturality_left
    {K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    (hK' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K')
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L) (a : K ⟶ K')
    (b : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K' ⟶ L) :
    standingExceptionalHomEquiv Λ f hK hL
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map a ≫ b) =
      a ≫ standingExceptionalHomEquiv Λ f hK' hL b := by
  let A := ModuleCat.{u + 1} Λ
  let ν := (comparisonUpperStar A X).mapDerivedCategory
  let F := rightDerivedLowerShriek A f
  let M := Classical.choose hK
  let hM := (Classical.choose_spec hK).1
  let e := Classical.choice (Classical.choose_spec hK).2
  let M' := Classical.choose hK'
  let hM' := (Classical.choose_spec hK').1
  let e' := Classical.choice (Classical.choose_spec hK').2
  obtain ⟨a₀, ha₀⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map M M' hM').2
    (e.hom ≫ a ≫ e'.inv)
  have ha : F.map e.hom ≫ F.map a ≫ b =
      F.map (ν.map a₀) ≫ F.map e'.hom ≫ b := by
    change ν.map a₀ = _ at ha₀
    erw [ha₀]
    simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  change e.inv ≫ representativeHom Λ f ⟨M, hM⟩ L hL (F.map e.hom ≫ F.map a ≫ b) =
    a ≫ e'.inv ≫ representativeHom Λ f ⟨M', hM'⟩ L hL (F.map e'.hom ≫ b)
  rw [ha]
  erw [representativeHom_left Λ f ⟨M, hM⟩ ⟨M', hM'⟩ L hL
    (ObjectProperty.homMk a₀)]
  change ν.map a₀ = _ at ha₀
  erw [ha₀]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The specified exceptional Hom bijection is natural in its bounded-below target.
Source: blueprint thm-sf-ambient-adjoint-class, four natural Hom identifications
(blueprint: lem-pur-standing-exceptional-hom-naturality).

Proof: use the retained etale representative of the fixed source. The fixed
compact-support comparison does not depend on the target; the comparison and etale
adjunction bijections are covariantly natural in the target. Comparison pullback
preserves composition, and conjugating back by the same source witness proves the
formula. The target witnesses enter only as proof arguments. -/
theorem standingExceptionalHomEquiv_naturality_right
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    {L L' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L)
    (hL' : _root_.DerivedCategory.TStructure.t.plus L')
    (a : (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).obj K ⟶ L) (b : L ⟶ L') :
    standingExceptionalHomEquiv Λ f hK hL' (a ≫ b) =
      standingExceptionalHomEquiv Λ f hK hL a ≫ (rightDerivedUpperShriek Λ f).map b := by
  let M := Classical.choose hK
  let hM := (Classical.choose_spec hK).1
  let e := Classical.choice (Classical.choose_spec hK).2
  change e.inv ≫ representativeHom Λ f ⟨M, hM⟩ L' hL'
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map e.hom ≫ a ≫ b) =
    (e.inv ≫ representativeHom Λ f ⟨M, hM⟩ L hL
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map e.hom ≫ a)) ≫ _
  rw [← Category.assoc ((rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map e.hom),
    representativeHom_right]
  exact (Category.assoc _ _ _).symm

/-- Contravariant naturality of the inverse specified Hom bijection.
Source: the natural Hom chain, blueprint thm-sf-ambient-adjoint-class
(blueprint: lem-pur-standing-exceptional-hom-naturality).
Proof: apply the forward bijection, use its source naturality, and cancel the
forward and inverse bijections on both sides. -/
theorem standingExceptionalHomEquiv_naturality_left_symm
    {K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K)
    (hK' : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} Λ) X K')
    {L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.TStructure.t.plus L) (a : K ⟶ K')
    (b : K' ⟶ (rightDerivedUpperShriek Λ f).obj L) :
    (standingExceptionalHomEquiv Λ f hK hL).symm (a ≫ b) =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) f).map a ≫
        (standingExceptionalHomEquiv Λ f hK' hL).symm b := by
  apply (standingExceptionalHomEquiv Λ f hK hL).injective
  rw [Equiv.apply_symm_apply,
    standingExceptionalHomEquiv_naturality_left Λ f hK hK' hL, Equiv.apply_symm_apply]

end AlgebraicGeometry.ProEtale
