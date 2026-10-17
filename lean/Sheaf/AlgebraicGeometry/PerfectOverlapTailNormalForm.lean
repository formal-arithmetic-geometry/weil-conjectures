/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageTail
public import Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle
public import Sheaf.AlgebraicGeometry.PerfectOverlapTailRestrictedComposite
public import Sheaf.AlgebraicGeometry.PerfectOverlapTailStageProjection
import Sheaf.AlgebraicGeometry.PerfectHomCompositionPrism
import Sheaf.AlgebraicGeometry.PerfectOverlapStageObjectTail
import all Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport

/-! # The tail after the composite stage-map counit -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom
  Scheme.Modules.instCategory
attribute [local implicit_reducible] TopologicalSpace.Opens.map OrderHomClass.toOrderHom
  TopCat.Hom.frameHom Monotone.functor
attribute [local implicit_reducible] SetLike.coe DFunLike.coe Set.inter
attribute [local implicit_reducible] perfectOverlapStageEquivalence
  overlapSchemeIsoDerivedEquivalence CategoryTheory.Equivalence.mk
attribute [local irreducible] CategoryTheory.IsPullback.isoPullback
attribute [local irreducible] derivedPullback perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

set_option maxHeartbeats 1000000 in
-- The restriction component involves several dependent derived-pullback functors.
/-- Component equation of the canonical tail constructor.
Source: Stacks Project, Tags 08DW and 0D5S, restriction and composition coherence.

Proof: Expand the constructed composite tail as the cartesian pullback of the
nested-square inverse followed by pullback of the local composition, then the
g-stage object comparison. Factor that comparison into the inverse inclusion
comparison and its cartesian projection tail. Expand the nested square inverse.
Naturality of the X-inclusion comparison moves the local composition across it;
the adjacent inclusion comparison and its inverse cancel. The remaining X-side
composition inverse cancels the first factor of the g-stage projection tail.

Write jX and jK for the nested inclusions and rL for the restriction of gk to L.
The restricted square says r followed by jK equals jX followed by rL, and
restricted composition says rL followed by f restricted to L equals g restricted
to L. Apply compositionTo_prism to this square and this composite. Identify its
local composition with perfectOverlapCompositeLocalIso by the existing local
composition equation; reflexive named comparisons reduce to perfectHomComposition.
This replaces the nested-square and local-composition factors by the K-inclusion
inverse, the composition of jK with f restricted to L, and compositionTo r p t.
Map these equations by the cartesian pullback and use functoriality of composition.
The three remaining cartesian projection factors are precisely the expanded
stage-object tail, with its projection equality replaced using proof irrelevance.
No boundedness, invertibility of restriction arrows, or nonempty-open assumption
is used; in particular the calculation applies to empty and equal opens.
(blueprint: lem-pc-perfect-overlap-tail-normal-form). -/
theorem perfectOverlapCompositeStageTailAt_eq_factors
    {X Y K C S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pY : Y ⟶ S) (b : C ⟶ S)
    (hg : IsPullback g pX pY b) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (A : schemeDerivedCategory L.toScheme) :
  let W := U ⊓ V
  let hP : g ⁻¹ᵁ L ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ L) := by
    rw [← Scheme.Hom.comp_preimage, hgf]
  let hT : g ⁻¹ᵁ W ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hgf]
  let iX : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
  let iK : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
  let _ξ := perfectOverlapNestedPullbackSquare gk iK iX hP hT
  let _κ := perfectOverlapCompositeLocalIso f gk g hgf L
  let r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) hT
  let jX := X.homOfLE (leOfHom iX)
  let jK := K.homOfLE (leOfHom iK)
  let p := jK ≫ (f ∣_ L)
  let t := jX ≫ (g ∣_ L)
  let e : (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme ≅ pullback (W.ι ≫ pY) b :=
    ((isPullback_morphismRestrict g W).paste_vert hg).isoPullback
  let a := Y.homOfLE hWL
  let hr : r ≫ p = t := perfectOverlapTailRestrictedComposite f gk g hgf U V L hWL
  let ht : e.inv ≫ t = pullback.fst (W.ι ≫ pY) b ≫ a :=
    perfectOverlapTailStageProjection g pX pY b hg U V L hWL
  let R := derivedPullback e.inv
  perfectOverlapCompositeStageTailAt f gk g hgf pX pY b hg U V L hWL A =
    R.map ((derivedPullback r).map
      ((overlapOpenInclusionPullbackIso K iK).inv.app ((derivedPullback (f ∣_ L)).obj A))) ≫
    R.map ((derivedPullback r).map ((perfectHomComposition jK (f ∣_ L)).hom.app A)) ≫
    R.map ((compositionTo r p t hr).hom.app A) ≫
    (perfectHomComposition e.inv t).hom.app A ≫
    (eqToIso (congrArg (fun k ↦ derivedPullback k) ht)).hom.app A ≫
    (perfectHomComposition (pullback.fst (W.ι ≫ pY) b) a).inv.app A := by
  intro W hP hT iX iK ξ κ r jX jK p t e a hr ht R
  let rL := gk.resLE (f ⁻¹ᵁ L) (g ⁻¹ᵁ L) hP
  have hs : r ≫ jK = jX ≫ rL :=
    perfectOverlapNestedRestrictedMaps gk iK iX hP hT
  have hj : rL ≫ (f ∣_ L) = g ∣_ L := by
    apply (cancel_mono L.ι).1
    simp only [Category.assoc, morphismRestrict_ι]
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hgf]
  have H := compositionTo_prism r jK (f ∣_ L) jX rL p (g ∣_ L) t
    rfl hj hr rfl hs A
  have h₀ : compositionTo jK (f ∣_ L) p rfl = perfectHomComposition jK (f ∣_ L) := by
    simp only [compositionTo, eqToIso_refl, Iso.trans_refl]
  have h₁ : compositionTo jX rL (jX ≫ rL) rfl = perfectHomComposition jX rL := by
    simp only [compositionTo, eqToIso_refl, Iso.trans_refl]
  have h₂ : compositionTo jX (g ∣_ L) t rfl = perfectHomComposition jX (g ∣_ L) := by
    simp only [compositionTo, eqToIso_refl, Iso.trans_refl]
  have Hhom := congrArg Iso.hom H
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] at Hhom
  conv at Hhom => lhs; lhs; rw [h₀]
  conv at Hhom => rhs; lhs; rhs; rw [h₁]
  conv at Hhom => rhs; rhs; rhs; rw [h₂]
  have hκ : κ = compositionTo rL (f ∣_ L) (g ∣_ L) hj := by
    unfold κ perfectOverlapCompositeLocalIso compositionTo
    rfl
  have hn := (overlapOpenInclusionPullbackIso X iX).inv.naturality (κ.hom.app A)
  have hlocal : ξ.inv.app ((derivedPullback (f ∣_ L)).obj A) ≫
      (schemeOpenOverlapRestriction X iX).mapDerivedCategory.map (κ.hom.app A) ≫
      (overlapOpenInclusionPullbackIso X iX).inv.app ((derivedPullback (g ∣_ L)).obj A) ≫
      (perfectHomComposition jX (g ∣_ L)).hom.app A =
    (derivedPullback r).map
      ((overlapOpenInclusionPullbackIso K iK).inv.app ((derivedPullback (f ∣_ L)).obj A)) ≫
    (derivedPullback r).map ((perfectHomComposition jK (f ∣_ L)).hom.app A) ≫
    (compositionTo r p t hr).hom.app A := by
    unfold ξ perfectOverlapNestedPullbackSquare
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Iso.symm_inv, Category.assoc]
    rw [reassoc_of% hn]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [hκ]
    have Hp := congrArg (fun z ↦ (derivedPullback r).map
      ((overlapOpenInclusionPullbackIso K iK).inv.app
        ((derivedPullback (f ∣_ L)).obj A)) ≫ z) Hhom.symm
    rw [compositionTo] at Hp
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.app_hom, Iso.app_inv,
      eqToIso.hom, eqToIso.inv, Category.assoc] at Hp ⊢
    exact Hp
  unfold perfectOverlapCompositeStageTailAt
  dsimp only
  simp only [← Iso.app_hom]
  rw [perfectOverlapStageObjectIso_hom_factor,
    perfectOverlapStageObjectTail_hom_app]
  simp only [perfectOverlapStageEquivalence_map_eq, Iso.app_hom,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.map_comp, Category.assoc]
  change R.map (ξ.inv.app ((derivedPullback (f ∣_ L)).obj A)) ≫
    R.map ((schemeOpenOverlapRestriction X iX).mapDerivedCategory.map (κ.hom.app A)) ≫
    R.map ((overlapOpenInclusionPullbackIso X iX).inv.app ((derivedPullback (g ∣_ L)).obj A)) ≫
    R.map ((perfectHomComposition jX (g ∣_ L)).hom.app A) ≫
    (perfectHomComposition e.inv t).hom.app A ≫
    (eqToIso (congrArg (fun k ↦ derivedPullback k) ht)).hom.app A ≫
    (perfectHomComposition (pullback.fst (W.ι ≫ pY) b) a).inv.app A = _
  simp only [← R.map_comp_assoc]
  rw [hlocal]

end AlgebraicGeometry
