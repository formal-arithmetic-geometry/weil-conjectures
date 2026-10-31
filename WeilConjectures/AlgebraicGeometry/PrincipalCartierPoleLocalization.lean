/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerLocalizationSpliceDefs
public import WeilConjectures.AlgebraicGeometry.CartierReductionDataSupplement
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.PrincipalCartierTorsorFrame

/-! # The sign of the pole extension on a principal Cartier chart
Source: Stacks Tags 01WQ, 03AJ and 0A45.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private theorem supported_one_restrict {D Z : Scheme.{u}} (i : D ⟶ Z)
    (U : Z.Etaleᵒᵖ) :
    ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
      ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z).from U.unop).op
      ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 Z)))
        (supportedIntegralOne Z)) =
    (supportedIntegralUnit i).hom.app U ((toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩) := by
  let v := ((MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Z).from U.unop).op
  have hq := ConcreteCategory.congr_hom ((supportedIntegralUnit i).hom.naturality v)
    (supportedIntegralOne Z)
  have h1 := ConcreteCategory.congr_hom
    ((toSheafify Z.smallEtaleTopology
      ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality v)
    (ULift.up 1)
  simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at hq h1
  exact hq.symm.trans (congrArg ((supportedIntegralUnit i).hom.app U) h1.symm)


set_option maxHeartbeats 1600000 in
-- The extension-class comparison unfolds several nested sheaf adjunctions.
/-- The pole extension of a principal Cartier divisor is minus the integral
localization boundary of its equation.
Source: Stacks Tags 01WQ, 03AJ and 0A45; principal chart of the Cartier formula.
(blueprint: lem-pur-principal-cartier-pole-localization).
Proof: trivialize the invertible principal ideal by its generating equation, and
use the dual frame of O(D). On the complement, the canonical section is the equation
times this frame. The normalized pole extension kills this complementary section.
Transport its quotient by the canonical inverse-image comparison on integral
constants. The framed torsor Yoneda formula identifies the transported extension
with localization pushed out by minus the equation. Naturality of extension classes
under the quotient comparison and additivity restore the supported constant source
and give the displayed negative boundary. -/
theorem principalCartierPoleLocalization (T : Scheme.{u}) (f : Γ(T, ⊤))
    (hI : (T.zeroLocusSubschemeι {f}).ker.IsInvertible)
    (C : PrincipalTorsorComparisons.{u}) (hF : C.Formula)
    (h : Set.range (T.zeroLocusSubschemeι {f}).base =
      (Set.range (T.basicOpen f).ι.base)ᶜ) :
    cartierPoleBoundary (T.zeroLocusSubschemeι {f}) hI =
      -integralLocalizationBoundary C (T.zeroLocusSubschemeι {f}) (T.basicOpen f) h
        ⟨Additive.ofMul (T.basicOpenUnit f)⟩ := by
  let k := T.zeroLocusSubschemeι {f}
  let W := T.basicOpen f
  let := hI.isInvertible_dual_toModules
  let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual k.ker.toModules)
  let P := Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual k.ker.toModules)
  have hβ : CartierPoleBoundarySpec k hI (cartierPoleBoundary k hI) :=
    (Classical.choose_spec (cartierPoleBoundary_existsUnique k hI)).1
  have hW : (W : Set T) = (Set.range k.base)ᶜ := by
    rw [h, compl_compl, Scheme.Opens.range_ι]
  obtain ⟨τ, E, a, b, hab, hE, F, hτ, hFa, hFb, hFτ, hβE⟩ := hβ W hW
  obtain ⟨e, he⟩ := principalCartierTorsorFrame T f hI
  have hτe := he τ hτ
  let c := (lowerStar AddCommGrpCat.{u + 1} k).mapIso
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).symm
  have hab' : a ≫ b ≫ c.hom = 0 := by rw [← Category.assoc, hab, zero_comp]
  let E' := ShortComplex.mk a (b ≫ c.hom) hab'
  let eE : ShortComplex.mk a b hab ≅ E' :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) c
  have hE' : E'.ShortExact := ShortComplex.shortExact_of_iso eE hE
  have hunit : supportedIntegralUnit k ≫ c.hom =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} k).unit.app
        (supportedIntegralConstant T) := by
    unfold supportedIntegralUnit
    rw [Adjunction.homEquiv_unit]
    simp only [c, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  obtain ⟨⟨hL, hclass⟩, _⟩ := hF T _ k W h T.gmSheaf P e τ
    ⟨Additive.ofMul (T.basicOpenUnit f)⟩ hτe E a (b ≫ c.hom) hab' hE' F.hom
    (fun U x p => (hFa U x p).trans (add_comm _ _)) (by
      intro U p
      change c.hom.hom.app U (b.hom.app U (F.hom.app U p)) = _
      rw [hFb, supported_one_restrict]
      exact ConcreteCategory.congr_hom (congrArg (fun z => z.hom.app U) hunit)
        (torsorExtensionOne T U.unop)) hFτ
  have hn := hE.extClass_naturality hE' eE.hom
  change hE.extClass.comp (Ext.mk₀ (𝟙 _)) (add_zero 1) =
    (Ext.mk₀ c.hom).comp hE'.extClass (zero_add 1) at hn
  rw [Ext.comp_mk₀_id] at hn
  rw [hβE, hn, hclass]
  simp only [map_neg, Ext.mk₀_neg, Ext.comp_neg]
  rfl

end AlgebraicGeometry.Etale
