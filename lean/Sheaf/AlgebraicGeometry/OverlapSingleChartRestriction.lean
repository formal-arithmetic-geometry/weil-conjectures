/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.OverlapPairCanonicalComparisons

/-! # A canonical restriction equation for a single chart
Source: Stacks Project, Tag 01ZR (2), first proof, and Tag 0095.
(blueprint: lem-pc-overlap-single-chart-restriction). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The part of the iterated comparison preceding the component isomorphism.
Source: Stacks Project, Tag 0095.
(blueprint: lem-pc-overlap-single-chart-restriction). -/
def overlapCanonicalChartComparison {X Y Z : Scheme.{u}} (U : X.OpenCover.{u})
    (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀) :
    (Scheme.Modules.pullback (Scheme.Cover.pullbackHom (U.pullback₁ q) p d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapIteratedChartHom U q p t h d)).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) :=
by
  let V : Y.OpenCover.{u} := U.pullback₁ q
  let d' := overlapIteratedChartHom U q p t h d
  have hdq : d' ≫ U.pullbackHom t d = V.pullbackHom p d ≫ U.pullbackHom q d :=
    pullback.lift_snd _ _ _
  exact (Scheme.Modules.pullbackComp (V.pullbackHom p d) (U.pullbackHom q d)).app
      (N d) ≪≫
    (Scheme.Modules.pullbackCongr hdq.symm).app (N d) ≪≫
    ((Scheme.Modules.pullbackComp d' (U.pullbackHom t d)).app (N d)).symm

/-- Canonical restriction comparison with abstract chart schemes.
Source: Stacks Project, Tag 0095, composition of inverse images.
(blueprint: lem-pc-overlap-single-chart-restriction). -/
def overlapRestrictionIso {B W K H : Scheme.{u}}
    (d : W ⟶ B) (z : K ⟶ H) (ha : H ⟶ B) (r : K ⟶ W)
    (hz : z ≫ ha = r ≫ d) (A : B.Modules) (L : W.Modules) (S : H.Modules)
    (C : L ≅ (Scheme.Modules.pullback d).obj A)
    (τ : S ≅ (Scheme.Modules.pullback ha).obj A) :
    (Scheme.Modules.pullback z).obj S ≅ (Scheme.Modules.pullback r).obj L :=
  (Scheme.Modules.pullback z).mapIso τ ≪≫
    pullbackCompOfEq z ha (r ≫ d) hz A ≪≫
    (pullbackCompOfEq r d (r ≫ d) rfl A).symm ≪≫
    (Scheme.Modules.pullback r).mapIso C.symm

/-- A single chart comparison commutes with restriction to an arbitrary scheme.
Source: Stacks Project, Tag 01ZR (2), first proof, and Tag 0095.
(blueprint: lem-pc-overlap-single-chart-restriction).

Proof: Factor the iterated comparison into C, the pullback of e, and the
composition comparison along the direct chart structure map. Expand xi and
cancel the pullback of C inverse against the pullback of C. Naturality of the
composition comparison moves the pullback of e through the inverse comparison
along r and the chart map. The inverse-image associativity pentagon identifies
this composite with the comparison along r followed by the iterated structure
map. On the other side use naturality to move e through the comparison along
z and hd, then use the same pentagon along z, hd and the direct structure map.
The relations hz, hnu and hzk identify the composite maps in this pentagon.
Cancel the remaining inverse composition comparison. Functoriality expands
the pullback of the three-factor alpha hom, yielding exactly the displayed
identity. This argument uses only naturality and invertibility and applies to
empty charts, repeated charts, zero modules and identity maps. -/
theorem overlap_single_chart_restriction {X Y Z H K : Scheme.{u}}
    (U : X.OpenCover.{u}) (q : Y ⟶ X) (p : Z ⟶ Y) (t : Z ⟶ X) (h : p ≫ q = t)
    (N : (d : U.I₀) → (U.X d).Modules) (M : Z.Modules)
    (e : ∀ d, (Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ t).f d)).obj M)
    (d : U.I₀) (ν : H ⟶ Z) (hd : H ⟶ (U.pullback₁ t).X d)
    (hν : hd ≫ (U.pullback₁ t).f d = ν)
    (r : K ⟶ ((U.pullback₁ q).pullback₁ p).X d) (z : K ⟶ H) (k : K ⟶ Z)
    (hr : r ≫ ((U.pullback₁ q).pullback₁ p).f d = k)
    (hz : z ≫ hd = r ≫ overlapIteratedChartHom U q p t h d)
    (hzk : z ≫ ν = k) (S : H.Modules)
    (τ : S ≅ (Scheme.Modules.pullback hd).obj
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d))) :
    let ξ := overlapRestrictionIso (overlapIteratedChartHom U q p t h d) z hd r hz
      ((Scheme.Modules.pullback (U.pullbackHom t d)).obj (N d)) _ S
      (overlapCanonicalChartComparison U q p t h N d) τ
    ξ.hom ≫ (Scheme.Modules.pullback r).map
        (overlapIteratedComparison U q p t h N M e d).hom ≫
        (pullbackCompOfEq r (((U.pullback₁ q).pullback₁ p).f d) k hr M).hom =
      (Scheme.Modules.pullback z).map
        (τ ≪≫ (Scheme.Modules.pullback hd).mapIso (e d) ≪≫
          pullbackCompOfEq hd ((U.pullback₁ t).f d) ν hν M).hom ≫
        (pullbackCompOfEq z ν k hzk M).hom := by sorry

end
end AlgebraicGeometry
