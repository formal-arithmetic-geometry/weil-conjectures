/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenSquareCube
public import Sheaf.AlgebraicGeometry.PerfectOverlapOpenLiftComponents

/-! # The pinned local cube for a canonical global coefficient -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The global open-pullback cube followed by the canonical local map reduces
to the restricted-composite comparison. Source: Stacks Project, Tag 0D5S.

Proof: Replace beta by the inverse pinned open square. The pinned cube moves
the global square to the restricted square. The two open-square components
then cancel in opposite order, leaving the restricted-composite comparison. -/
theorem perfectOverlapCanonicalLocalCubeU
    {X K Y : Scheme.{u}} (g : X ⟶ Y) (gk : X ⟶ K) (f : K ⟶ Y)
    (hgf : gk ≫ f = g) (U : Y.Opens) (M : schemeDerivedCategory Y) :
    let hP : g ⁻¹ᵁ U ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ U) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let h : gk ≫ f = g ≫ 𝟙 Y := by simpa using hgf
    let hW : U ≤ (𝟙 Y) ⁻¹ᵁ U := by simp
    let j := gk.resLE (f ⁻¹ᵁ U) (g ⁻¹ᵁ U) hP
    let hj := Scheme.Hom.resLE_comp_ι gk hP
    let h0 : j ≫ (f ∣_ U) = (g ∣_ U) ≫ Scheme.Hom.resLE (𝟙 Y) U U hW := by
      have hid : Scheme.Hom.resLE (𝟙 Y) U U hW = 𝟙 U.toScheme := by
        rw [Scheme.Hom.resLE_id]
        exact Scheme.homOfLE_rfl Y U
      rw [hid, Category.comp_id]
      exact perfectOverlapRestrictedComposite f gk g hgf U
    let q := singleComplexOpenSquareComparison f g (𝟙 Y) gk h
    let q0 := singleComplexOpenSquareComparison (f ∣_ U) (g ∣_ U)
      (Scheme.Hom.resLE (𝟙 Y) U U hW) j h0
    let RS := (schemeOpenRestriction Y U).mapDerivedCategory
    let RX := (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory
    let d := singleComplexOpenPullbackSquareIso f U (f ⁻¹ᵁ U) (f ∣_ U)
      (morphismRestrict_ι f U)
    let d' := singleComplexOpenPullbackSquareIso g U (g ⁻¹ᵁ U) (g ∣_ U)
      (morphismRestrict_ι g U)
    let e := singleComplexOpenPullbackSquareIso (𝟙 Y) U U
      (Scheme.Hom.resLE (𝟙 Y) U U hW)
      (Scheme.Hom.resLE_comp_ι (𝟙 Y) hW)
    let e' := singleComplexOpenPullbackSquareIso gk (f ⁻¹ᵁ U) (g ⁻¹ᵁ U) j hj
    let κ := perfectOverlapCompositeLocalIso f gk g hgf U
    let t := perfectOverlapCompositeLocalMap g gk f hgf U
      (RS.obj M) ((derivedPullback f).obj M) (perfectOverlapOpenLiftBeta f U M)
    (derivedPullback (g ∣_ U)).map (e.hom.app M) ≫
        d'.hom.app ((derivedPullback (𝟙 Y)).obj M) ≫ RX.map (q.app M) ≫ t =
      q0.app (RS.obj M) ≫ κ.hom.app (RS.obj M) := by
  intro hP h hW j hj h0 q q0 RS RX d d' e e' κ t
  have hc := perfectOverlapCompositeOpenCube g gk f hgf U M
  have ht := perfectOverlapCompositeLocalMap_eq g gk f hgf U
    (RS.obj M) ((derivedPullback f).obj M) (perfectOverlapOpenLiftBeta f U M)
  have hβ := perfectOverlapOpenLiftBeta_hom_square f U M
  have hc' : q0.app (RS.obj M) ≫ (derivedPullback j).map (d.hom.app M) ≫
        e'.hom.app ((derivedPullback f).obj M) =
      (derivedPullback (g ∣_ U)).map (e.hom.app M) ≫
        d'.hom.app ((derivedPullback (𝟙 Y)).obj M) ≫ RX.map (q.app M) := by
    exact hc
  dsimp only [t]
  rw [ht, hβ]
  rw [← reassoc_of% hc']
  change q0.app (RS.obj M) ≫ (derivedPullback j).map (d.hom.app M) ≫
      e'.hom.app ((derivedPullback f).obj M) ≫
        e'.inv.app ((derivedPullback f).obj M) ≫
          (derivedPullback j).map (d.inv.app M) ≫
            κ.hom.app (RS.obj M) = q0.app (RS.obj M) ≫ κ.hom.app (RS.obj M)
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  have hid : (derivedPullback j).map
      (𝟙 ((derivedPullback (f ∣_ U)).obj (RS.obj M))) = 𝟙 _ := by
    exact (derivedPullback j).map_id _
  simp only [Functor.comp_obj]
  rw [hid, Category.id_comp]

end AlgebraicGeometry
