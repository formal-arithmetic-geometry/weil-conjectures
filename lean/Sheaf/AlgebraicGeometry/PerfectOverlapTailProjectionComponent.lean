/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapCompositeStageTail
public import Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport
import Sheaf.AlgebraicGeometry.PerfectOverlapStageSchemeIso
import Sheaf.AlgebraicGeometry.PerfectHomCompositionPrism
import Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositeAbstract
import Sheaf.AlgebraicGeometry.PerfectOverlapRestrictedComposition
import Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare
import Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence

/-! # A component of composite overlap compatibility
Source: Stacks Project, Tags 08DW and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
-- These open-set proof terms must also type-check during restricted tactic reduction.
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] TopologicalSpace.Opens.map OrderHomClass.toOrderHom
  Monotone.functor
  TopCat.Hom.frameHom TopologicalSpace.Opens.instCompleteLattice
  TopologicalSpace.Opens.instFrame
  CompleteLattice.toConditionallyCompleteLattice ConditionallyCompleteLattice.toLattice
  Lattice.toSemilatticeInf SemilatticeInf.toMin min SemilatticeInf.inf Lattice.inf Set.inter
  perfectOverlapStageEquivalence overlapSchemeIsoDerivedEquivalence CategoryTheory.Equivalence.mk

attribute [local irreducible] derivedPullback perfectHomComposition
  perfectOverlapDerivedPullbackTransport perfectOverlapStageObjectIso
  compositionTo perfectHomComparison Scheme.Hom.resLE
  Scheme.homOfLE morphismRestrict
  Functor.mapDerivedCategory IsPullback.isoPullback Scheme.Opens.toScheme
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 700000 in
-- The two cartesian projection prisms require several dependent component comparisons.
set_option linter.unusedVariables false in
/-- Projection compatibility for the tail, before insertion of the site counit.
Source: Stacks Project, Tags 08DW and 0D5S, composition comparisons in Tag 09RE.

Proof: First rewrite the endpoint stage functors by their proved equations,
so the stage transport is the fixed derived transport. Fix either Boolean branch,
with its open L and local object M. Expand
only the constructed tail and factor the g-stage object comparison using
`perfectOverlapStageObjectIso_hom_app`. Expand the nested pullback square.
Naturality of the inclusion-pullback isomorphism moves the local composition
through the first inclusion, cancelling the adjacent inverse-forward pair.
Put jX and jK for the nested open inclusions, rL for the restricted gk, and
fL and gL for the restrictions to L. Cancellation of L's open immersion gives
r followed by jK equal to jX followed by rL, and restricted composition gives
rL followed by fL equal to gL. Apply `compositionTo_prism` to these arrows.
Its three reflexive named composites reduce to the fixed composition family,
and the remaining local named composite is kappa by
`perfectOverlapCompositeLocalIso_eq_compositionTo`. Apply the cartesian
projection prism `perfectOverlapProjectionCompositeAbstract` to the resulting
composite, using `perfectOverlapStageSchemeIso_inv_projection` for its two
projection equations. Finally use naturality of the derived transport for
the K-inclusion comparison and for the composition of jK with fL. Expanding
the f-stage object comparison and associating the factors identifies the
right side with transport followed by pullback of sigma. This argument uses
only isomorphisms, so includes empty or equal opens and unbounded M.
(blueprint: lem-pc-perfect-overlap-tail-projection-component). -/
theorem perfectOverlapTailProjectionComponent
    {X Y K C T S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (l : Over.mk b ⟶ Over.mk q)
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
  let W := U ⊓ V
  let s := W.ι ≫ pY
  let r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, hgf])
  let m := baseChangeMap s l
  let eY := ((isPullback_morphismRestrict g W).paste_vert hg).isoPullback
  let eK := ((isPullback_morphismRestrict f W).paste_vert hf).isoPullback
  ∀ hmap : eY.inv ≫ r = m ≫ eK.inv,
  let data := transportDataOfComposite f gk g hgf U V A B E φU φV
  let F : Bool → schemeDerivedCategory (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme := fun a ↦
    if a then
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_right : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ V)).obj B)
    else
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ U)).obj A)
  let apex := perfectOverlapApexEquivalence g pX pY b hg U V
  let η := perfectOverlapNaturalComparisonOfSquare g f pX pK pY b q hg hf U V r m hmap
  let σ : ∀ a : Bool,
      (perfectOverlapStageEquivalence f pK pY q hf U V).functor.obj (F a) ≅
        (derivedPullback (pullback.fst s q)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := fun a ↦
    Bool.casesOn a
      ((perfectOverlapStageObjectIso f pK pY q hf U V U inf_le_left).app A)
      ((perfectOverlapStageObjectIso f pK pY q hf U V V inf_le_right).app B)
  let D : ∀ a : Bool,
      (perfectOverlapStageEquivalence g pX pY b hg U V).functor.obj
          ((derivedPullback r).obj (F a)) ⟶
        (derivedPullback (pullback.fst s b)).obj
          (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
          else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := fun a ↦
    Bool.casesOn a
      (perfectOverlapCompositeStageTailAt f gk g hgf pX pY b hg U V U inf_le_left A)
      (perfectOverlapCompositeStageTailAt f gk g hgf pX pY b hg U V V inf_le_right B)
  ∀ a : Bool,
    D a ≫ (perfectHomComparison s l).hom.app
        (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
        else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) =
      (perfectOverlapStageTransport g f pX pK pY b q hg hf U V r m hmap).hom.app (F a) ≫
        (derivedPullback m).map (σ a).hom
    := by
  intro W s r m eY eK hmap data F apex η σ D a
  clear data apex η φU φV E
  have H (L : Y.Opens) (hWL : U ⊓ V ≤ L)
      (M : schemeDerivedCategory L.toScheme) :
      perfectOverlapCompositeStageTailAt f gk g hgf pX pY b hg U V L hWL M ≫
          (perfectHomComparison ((U ⊓ V).ι ≫ pY) l).hom.app
            ((derivedPullback (Y.homOfLE hWL)).obj M) =
        (perfectOverlapStageTransport g f pX pK pY b q hg hf U V r m hmap).hom.app
            ((schemeOpenOverlapRestriction K
              (homOfLE (show f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ L from
                fun _ hx ↦ hWL hx))).mapDerivedCategory.obj ((derivedPullback (f ∣_ L)).obj M)) ≫
          (derivedPullback (baseChangeMap ((U ⊓ V).ι ≫ pY) l)).map
            ((perfectOverlapStageObjectIso f pK pY q hf U V L hWL).hom.app M) := by
    clear σ D F a A B
    let hP : g ⁻¹ᵁ L ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ L) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let hT : g ⁻¹ᵁ W ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let iX : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
    let iK : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
    let jX := X.homOfLE (leOfHom iX)
    let jK := K.homOfLE (leOfHom iK)
    let rL := gk.resLE (f ⁻¹ᵁ L) (g ⁻¹ᵁ L) hP
    let r : (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme ⟶
        (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme :=
      gk.resLE (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V) hT
    let m : pullback s b ⟶ pullback s q := baseChangeMap s l
    let eX : (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme ≅ pullback s b := eY
    let eF : (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme ≅ pullback s q := eK
    have hmapI : eX.inv ≫ r = m ≫ eF.inv := hmap
    let a := Y.homOfLE hWL
    let p := jK ≫ (f ∣_ L)
    let t := jX ≫ (g ∣_ L)
    have hs : r ≫ jK = jX ≫ rL :=
      perfectOverlapNestedRestrictedMaps gk iK iX hP hT
    have hc : rL ≫ (f ∣_ L) = g ∣_ L :=
      perfectOverlapRestrictedComposite f gk g hgf L
    have hr : r ≫ p = t := by
      dsimp only [p, t]
      rw [← Category.assoc, hs, Category.assoc, hc]
    have ht : eX.inv ≫ t = pullback.fst s b ≫ a := by
      simpa only [perfectOverlapStageSchemeIso_eq_raw, eX, eY, t, jX, iX,
        W, s, a, Scheme.Hom.preimage_inf] using
        perfectOverlapStageSchemeIso_inv_projection g pX pY b hg U V L hWL
    have hp : eF.inv ≫ p = pullback.fst s q ≫ a := by
      simpa only [perfectOverlapStageSchemeIso_eq_raw, eF, p, jK, iK,
        W, s, a, Scheme.Hom.preimage_inf] using
        perfectOverlapStageSchemeIso_inv_projection f pK pY q hf U V L hWL
    have prism := compositionTo_prism r jK (f ∣_ L) jX rL p (g ∣_ L) t
      rfl hc hr rfl hs M
    have projection := perfectOverlapProjectionCompositeAbstract s l r eX eF hmapI
      p t hr a ht hp M
    let ξ := perfectOverlapNestedPullbackSquare gk iK iX hP hT
    let κ := perfectOverlapCompositeLocalIso f gk g hgf L
    let SX := (schemeOpenOverlapRestriction X iX).mapDerivedCategory
    let SK := (schemeOpenOverlapRestriction K iK).mapDerivedCategory
    let z := (derivedPullback (f ∣_ L)).obj M
    let τ := perfectOverlapDerivedPullbackTransport r eX eF m hmapI
    let αX := overlapOpenInclusionPullbackIso X iX
    let αK := overlapOpenInclusionPullbackIso K iK
    let cX := (perfectHomComposition jX (g ∣_ L)).hom.app M
    let cK := (perfectHomComposition jK (f ∣_ L)).hom.app M
    let dX := (perfectHomComposition eX.inv t).hom.app M ≫
      (eqToIso (congrArg (fun k ↦ derivedPullback k) ht)).hom.app M ≫
        (perfectHomComposition (pullback.fst s b) a).inv.app M
    let dK := (perfectHomComposition eF.inv p).hom.app M ≫
      (eqToIso (congrArg (fun k ↦ derivedPullback k) hp)).hom.app M ≫
        (perfectHomComposition (pullback.fst s q) a).inv.app M
    have square : ξ.inv.app z =
        (derivedPullback r).map (αK.inv.app z) ≫
          (compositionTo r jK (jX ≫ rL) hs).hom.app z ≫
            (perfectHomComposition jX rL).inv.app z ≫
              αX.hom.app ((derivedPullback rL).obj z) := by
      dsimp only [ξ]
      unfold perfectOverlapNestedPullbackSquare
      simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
        Functor.whiskerRight_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
        Iso.symm_inv, compositionTo, Iso.trans_hom, Category.assoc,
        eqToIso.inv, eqToIso.hom]
      rfl
    have prismHom := congrArg Iso.hom prism
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.app_inv] at prismHom
    have localIso : κ = compositionTo rL (f ∣_ L) (g ∣_ L) hc :=
      perfectOverlapCompositeLocalIso_eq_compositionTo g gk f hgf L
    rw [← localIso] at prismHom
    have reflK : compositionTo jK (f ∣_ L) p rfl = perfectHomComposition jK (f ∣_ L) := by
      simp only [compositionTo, eqToIso_refl, Iso.trans_refl]
    have reflX : compositionTo jX (g ∣_ L) t rfl = perfectHomComposition jX (g ∣_ L) := by
      simp only [compositionTo, eqToIso_refl, Iso.trans_refl]
    have reflSquare : compositionTo jX rL (jX ≫ rL) rfl = perfectHomComposition jX rL := by
      simp only [compositionTo, eqToIso_refl, Iso.trans_refl]
    rw [reflK, reflX, reflSquare] at prismHom
    simp only [Category.assoc] at prismHom
    let R := derivedPullback eX.inv
    let RK := derivedPullback eF.inv
    let Q : schemeDerivedCategory (pullback s q) ⥤
        schemeDerivedCategory (pullback s b) := derivedPullback m
    have projection' : R.map ((compositionTo r p t hr).hom.app M) ≫ dX ≫
          (perfectHomComparison s l).hom.app ((derivedPullback a).obj M) =
        τ.hom.app ((derivedPullback p).obj M) ≫ Q.map dK := by
      dsimp only [R, Q, dX, dK, τ, m]
      simpa only [Over.mk_hom, Category.assoc, Functor.map_comp] using projection
    have flatX : (perfectOverlapStageObjectIso g pX pY b hg U V L hWL).hom.app M =
        R.map (αX.inv.app ((derivedPullback (g ∣_ L)).obj M) ≫ cX) ≫ dX := by
      have flat := perfectOverlapStageObjectIso_hom_app g pX pY b hg U V L hWL M
      simpa only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
        R, αX, cX, dX, eX, eY, t, jX, iX, a, s, W,
        Over.mk_hom, Category.assoc] using flat
    have flatK : (perfectOverlapStageObjectIso f pK pY q hf U V L hWL).hom.app M =
        RK.map (αK.inv.app z ≫ cK) ≫ dK := by
      have flat := perfectOverlapStageObjectIso_hom_app f pK pY q hf U V L hWL M
      simpa only [Iso.app_hom, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
        RK, αK, z, cK, dK, eF, p, jK, iK, a, s, W,
        Over.mk_hom, Category.assoc] using flat
    have tailFlat :
        perfectOverlapCompositeStageTailAt f gk g hgf pX pY b hg U V L hWL M =
          R.map (ξ.inv.app z ≫ SX.map (κ.hom.app M) ≫
            αX.inv.app ((derivedPullback (g ∣_ L)).obj M) ≫ cX) ≫ dX := by
      unfold perfectOverlapCompositeStageTailAt
      dsimp only
      have mapped := congrArg (fun k ↦
        R.map (ξ.inv.app z ≫ SX.map (κ.hom.app M)) ≫ k) flatX
      simpa only [perfectOverlapStageEquivalence_map_eq, Category.assoc,
        Functor.map_comp] using mapped
    have first := congrArg (fun k ↦ k ≫
      (perfectHomComparison s l).hom.app ((derivedPullback a).obj M)) tailFlat
    simp only [Category.assoc] at first
    have last :
        τ.hom.app (SK.obj z) ≫ Q.map (RK.map (αK.inv.app z ≫ cK) ≫ dK) =
          (perfectOverlapStageTransport g f pX pK pY b q hg hf U V r m hmapI).hom.app
              (SK.obj z) ≫
            Q.map ((perfectOverlapStageObjectIso f pK pY q hf U V L hWL).hom.app M) := by
      unfold perfectOverlapStageTransport
      exact congrArg (fun k ↦ τ.hom.app (SK.obj z) ≫ Q.map k) flatK.symm
    -- Use the component equations above, keeping the constructed isomorphisms abstract.
    clear_value ξ κ αX αK dX dK τ
    have inside : ξ.inv.app z ≫ SX.map (κ.hom.app M) ≫
          αX.inv.app ((derivedPullback (g ∣_ L)).obj M) ≫ cX =
        (derivedPullback r).map (αK.inv.app z ≫ cK) ≫
          (compositionTo r p t hr).hom.app M := by
      have hprefix := congrArg (fun k ↦ k ≫ SX.map (κ.hom.app M) ≫
        αX.inv.app ((derivedPullback (g ∣_ L)).obj M) ≫ cX) square
      refine hprefix.trans ?_
      simp only [Category.assoc]
      have naturalX : SX.map (κ.hom.app M) ≫
            αX.inv.app ((derivedPullback (g ∣_ L)).obj M) =
          αX.inv.app ((derivedPullback rL).obj z) ≫
            (derivedPullback jX).map (κ.hom.app M) :=
        αX.inv.naturality (κ.hom.app M)
      simp only [reassoc_of% naturalX]
      simp only [Iso.hom_inv_id_app_assoc]
      have glued := congrArg (fun k ↦ (derivedPullback r).map (αK.inv.app z) ≫ k)
        prismHom.symm
      simpa only [cX, cK, z, Category.assoc, Functor.map_comp] using glued
    have core :
        R.map (ξ.inv.app z ≫ SX.map (κ.hom.app M) ≫
            αX.inv.app ((derivedPullback (g ∣_ L)).obj M) ≫ cX) ≫ dX ≫
          (perfectHomComparison s l).hom.app ((derivedPullback a).obj M) =
        τ.hom.app (SK.obj z) ≫ Q.map (RK.map (αK.inv.app z ≫ cK) ≫ dK) := by
      calc
        _ = R.map ((derivedPullback r).map (αK.inv.app z ≫ cK) ≫
            (compositionTo r p t hr).hom.app M) ≫ dX ≫
              (perfectHomComparison s l).hom.app ((derivedPullback a).obj M) :=
          congrArg (fun k ↦ R.map k ≫ dX ≫
            (perfectHomComparison s l).hom.app ((derivedPullback a).obj M)) inside
        _ = R.map ((derivedPullback r).map (αK.inv.app z ≫ cK)) ≫
            (R.map ((compositionTo r p t hr).hom.app M) ≫ dX ≫
              (perfectHomComparison s l).hom.app ((derivedPullback a).obj M)) := by
          simp only [Functor.map_comp, Category.assoc]
        _ = R.map ((derivedPullback r).map (αK.inv.app z ≫ cK)) ≫
            (τ.hom.app ((derivedPullback p).obj M) ≫ Q.map dK) :=
          congrArg (fun k ↦ R.map ((derivedPullback r).map (αK.inv.app z ≫ cK)) ≫ k)
            projection'
        _ = _ := by
          have natural := τ.hom.naturality (αK.inv.app z ≫ cK)
          simpa only [R, RK, Q, Functor.comp_map, Category.assoc, Functor.map_comp] using
            congrArg (fun k ↦ k ≫ Q.map dK) natural
    exact first.trans (core.trans last)
  cases a with
  | false =>
    dsimp only [D, F, σ]
    simp only [Iso.app_hom]
    exact H U inf_le_left A
  | true =>
    dsimp only [D, F, σ]
    simp only [Iso.app_hom]
    exact H V inf_le_right B

end AlgebraicGeometry
