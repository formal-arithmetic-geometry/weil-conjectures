/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapProjectionSchemeSquare
public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenLiftComponents
public import Sheaf.AlgebraicGeometry.PerfectOverlapNestedOpenSquarePasting
public import Sheaf.AlgebraicGeometry.PerfectOverlapSquarePrismAbstract

/-! # The canonical first-open pullback prism before cartesian transport -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits schemeOpenOverlapRestriction_additive
  schemeOpenOverlapRestriction_preservesFiniteLimits
  schemeOpenOverlapRestriction_preservesFiniteColimits

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

set_option maxHeartbeats 8000000 in
/-- The five local maps from the canonical global lift equal the pinned
comparison of the two composites from the overlap to the first open.
Source: Stacks Project, Tags 08DW and 0D5S.

Proof: Replace the lift isomorphism by its pinned open-pullback square
component. Expand the canonical local map into the inverse first-open square,
the lifted component, and the restricted-composite comparison. Apply the
open-pullback cube to the first open and its overlap restriction. Naturality of
the nested-open restriction comparison moves the lift through the first-open
inclusion; its inverse and forward components cancel. The square of scheme
maps is `perfectOverlapRestrictionCompositeU`. The remaining three fixed
composition comparisons are exactly `compositionTo` for that square, preceded
and followed by the pinned open-inclusion comparisons. -/
theorem perfectOverlapCanonicalOpenPrismU
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (U V : Y.Opens)
    (M : schemeDerivedCategory Y) :
    let A := (schemeOpenRestriction Y U).mapDerivedCategory.obj M
    let F := (derivedPullback f).obj M
    let e := perfectOverlapOpenLiftBeta f U M
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let hPU : P ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let hPV : Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hgf]
    let hPW : P ⊓ Q ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) :=
      fun _ hx ↦ ⟨hPU hx.1, hPV hx.2⟩
    let r := gk.resLE (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) hPW
    let iK : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ U := homOfLE inf_le_left
    let iX : P ⊓ Q ⟶ P := homOfLE inf_le_left
    let SU := (schemeOpenOverlapRestriction K iK).mapDerivedCategory
    let SX := (schemeOpenOverlapRestriction X iX).mapDerivedCategory
    let square := singleComplexOpenPullbackSquareIso gk
      (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) (P ⊓ Q) r (Scheme.Hom.resLE_comp_ι gk hPW)
    let a := (derivedPullback r).map (SU.map e.inv)
    let z := (derivedPullback r).map
      ((schemeDerivedOpenRestrictionCompIso K iK).hom.app F)
    let c := square.hom.app F
    let d := (schemeDerivedOpenRestrictionCompIso X iX).inv.app
      ((derivedPullback gk).obj F)
    let t := SX.map (perfectOverlapCompositeLocalMap g gk f hgf U A F e)
    let p := K.homOfLE (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) ≫
      (f ∣_ U)
    let q := X.homOfLE (inf_le_left : P ⊓ Q ≤ P) ≫ (g ∣_ U)
    let hr : r ≫ p = q := perfectOverlapRestrictionCompositeU g gk f hgf U V
    let αK := overlapOpenInclusionPullbackIso K iK
    let αX := overlapOpenInclusionPullbackIso X iX
    a ≫ z ≫ c ≫ d ≫ t =
      (derivedPullback r).map (αK.inv.app ((derivedPullback (f ∣_ U)).obj A)) ≫
      (derivedPullback r).map
        ((perfectHomComposition (K.homOfLE (inf_le_left : _ ≤ f ⁻¹ᵁ U))
          (f ∣_ U)).hom.app A) ≫
      (compositionTo r p q hr).hom.app A ≫
      (perfectHomComposition
        (X.homOfLE (inf_le_left : P ⊓ Q ≤ P)) (g ∣_ U)).inv.app A ≫
      αX.hom.app ((derivedPullback (g ∣_ U)).obj A) := by
  intro A F e P Q hPU hPV hPW r iK iX SU SX square a z c d t p q hr αK αX
  have ht := perfectOverlapCompositeLocalMap_eq g gk f hgf U A F e
  dsimp only [t]
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]
  have hnest := perfectOverlapNestedOpenSquarePastingOfData gk
    (f ⁻¹ᵁ U) (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V)
    (g ⁻¹ᵁ U) (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)
    inf_le_left hPU hPW inf_le_left F
  rw [reassoc_of% hnest]
  let j := gk.resLE (f ⁻¹ᵁ U) P hPU
  have hs := perfectOverlapRestrictionSquareU g gk f hgf U V
  let q0 := singleComplexOpenSquareComparison j r
    (K.homOfLE (inf_le_left : _ ≤ f ⁻¹ᵁ U))
    (X.homOfLE (inf_le_left : P ⊓ Q ≤ P)) hs.symm
  let κ := perfectOverlapCompositeLocalIso f gk g hgf U
  have hαK := αK.inv.naturality e.inv
  have hq := q0.naturality e.inv
  have hαX := αX.hom.naturality ((derivedPullback j).map e.hom)
  have hαK' := congrArg (derivedPullback r).map hαK
  simp only [Functor.map_comp] at hαK'
  simp only [Functor.comp_map] at hq
  dsimp only [a]
  rw [reassoc_of% hαK']
  rw [reassoc_of% hq]
  rw [← reassoc_of% hαX]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp]
  rw [e.inv_hom_id, (derivedPullback j).map_id,
    (derivedPullback (X.homOfLE (inf_le_left : P ⊓ Q ≤ P))).map_id]
  simp only [Category.id_comp]
  have hακ := αX.hom.naturality (κ.hom.app A)
  simp only [Functor.comp_obj] at hακ
  dsimp only [κ, SX] at hακ
  rw [← hακ]
  have hκ := perfectOverlapCompositeLocalIso_eq_compositionTo g gk f hgf U
  have hg : j ≫ (f ∣_ U) = (g ∣_ U) :=
    perfectOverlapRestrictedComposite f gk g hgf U
  have hprism := perfectOverlapSquarePrismAbstract r
    (K.homOfLE (inf_le_left : _ ≤ f ⁻¹ᵁ U)) (f ∣_ U)
    (X.homOfLE (inf_le_left : P ⊓ Q ≤ P)) j (g ∣_ U)
    p q rfl hg hr rfl hs A
  have H := congrArg (fun z =>
    (derivedPullback r).map (αK.inv.app ((derivedPullback (f ∣_ U)).obj A)) ≫
      z ≫ αX.hom.app ((derivedPullback (g ∣_ U)).obj A)) hprism.symm
  simpa only [hκ, q0, κ, compositionTo, eqToIso_refl,
    Iso.trans_refl, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, Category.id_comp,
    Category.comp_id] using H

end AlgebraicGeometry
