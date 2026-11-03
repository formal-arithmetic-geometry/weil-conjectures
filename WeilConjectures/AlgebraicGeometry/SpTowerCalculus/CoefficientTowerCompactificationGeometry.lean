/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.ProperOpenCalculus
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Compactification.NagataCompactification

/-! # Compactification geometry on Noetherian schemes

Source: Stacks 0F7J and 0F7K, common refinements and three-map staircases.
(blueprint: lem-sp-noetherian-compactification-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

/-- The ambient schemes needed for the finite-type-over-a-field calculus.
Source: Stacks 0F7J (blueprint: lem-sp-noetherian-compactification-geometry). -/
def NoetherianAmbient (X : Scheme.{u}) : Prop := IsLocallyNoetherian X ∧ CompactSpace X

theorem ambient_compactification {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hY : NoetherianAmbient Y) (c : Compactification f) :
    NoetherianAmbient c.Z := by
  let := hY.1
  let := hY.2
  exact ⟨LocallyOfFiniteType.isLocallyNoetherian c.g,
    QuasiCompact.compactSpace_of_compactSpace c.g⟩

private theorem ambient_triangle {X Y Z : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hY : NoetherianAmbient Y) (hZ : NoetherianAmbient Z)
    (T : Compactification.Triangle f g) :
    ProperOpenCalculus.TriangleObjects (A := NoetherianAmbient) T :=
  ⟨ambient_compactification hY T.cf, ambient_compactification hZ T.cg,
    ambient_compactification hZ T.cfg⟩

/-- The supplied compactification geometry is available on Noetherian ambient schemes.
Source: Stacks 0F7J and 0F7K
(blueprint: lem-sp-noetherian-compactification-geometry).

Proof: Nagata gives compactifications over each quasi-compact locally Noetherian
base. Properness makes every compactification ambient scheme Noetherian. The graph
common refinement and dense equalizing refinement stay in this class. Apply the
supplied compatible-tower theorem to obtain binary towers and their common refinements.
Finally use the existing three-map tower built from compactifications of the last
map and the two composites; all its ambient schemes are proper over a Noetherian base.
The argument includes empty schemes and the identity arrows. -/
theorem noetherian_compactification_geometry :
    ProperOpenCalculus.Geometry NoetherianAmbient.{u} := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y f _ _ _
    let := Y.property.1
    let := Y.property.2
    let c := NagataCompactification f
    exact ⟨c, ambient_compactification Y.property c⟩
  · intro X Y f _ _ _ c d _ _
    exact ⟨c.inf d, ambient_compactification Y.property _,
      ⟨c.infFst d⟩, ⟨c.infSnd d⟩⟩
  · intro X Y f _ _ _ c d _ _ r s
    obtain ⟨e, he, ⟨t⟩, _⟩ :=
      Compactification.exists_common_refinement_isSchemeTheoreticallyDominant c c
    let := he
    exact ⟨e, ambient_compactification Y.property e, t,
      Subsingleton.elim (α := e.Refinement d) _ _⟩
  · intro X Y Z f g _ _ _ _ _ _ d c _ _
    obtain ⟨e, v, hv, hvi, hvg, _⟩ :=
      (exists_compactifiable_compatible_tower f g d c).1
    let T := Compactification.Triangle.ofRestrict d e
    refine ⟨T, ambient_triangle Y.property Z.property T, rfl, ⟨v, ?_, ?_⟩⟩
    · change e.i ≫ v = c.i
      exact hvi
    · change v ≫ c.g = e.g ≫ d.g
      exact hvg
  · intro X Y Z f g _ _ _ _ _ _ T S _ _
    obtain ⟨R, hR⟩ := (exists_compactifiable_compatible_tower f g T.cg T.cfg).2.2
      (fun n ↦ if n = 0 then T else S)
    obtain ⟨vT, uT, wT, hvT, huT, hwT, hiT, hjT, hkT, hqT, hpT, hfT, hgT⟩ := hR 0
    obtain ⟨vS, uS, wS, hvS, huS, hwS, hiS, hjS, hkS, hqS, hpS, hfS, hgS⟩ := hR 1
    change vT ≫ T.p = R.p ≫ uT at hpT
    change uT ≫ T.cg.g = R.cg.g at hgT
    change vS ≫ S.p = R.p ≫ uS at hpS
    change uS ≫ S.cg.g = R.cg.g at hgS
    refine ⟨R, ambient_triangle Y.property Z.property R,
      ⟨⟨⟨wT, hkT, hfT⟩, ⟨uT, hjT, hgT⟩, ⟨vT, hiT, ?_⟩, hqT, hpT⟩⟩,
      ⟨⟨⟨wS, hkS, hfS⟩, ⟨uS, hjS, hgS⟩, ⟨vS, hiS, ?_⟩, hqS, hpS⟩⟩⟩
    · rw [← T.p_g, ← Category.assoc, hpT, Category.assoc, hgT, R.p_g]
    · rw [← S.p_g, ← Category.assoc, hpS, Category.assoc, hgS, R.p_g]
  · intro X Y Z W f g h _ _ _ _ _ _ _ _ _
    let := W.property.1
    let := W.property.2
    let : HasCompactification h := (NagataCompactification h).hasCompactification
    let : HasCompactification (g ≫ h) :=
      (NagataCompactification (g ≫ h)).hasCompactification
    let : HasCompactification (f ≫ g ≫ h) :=
      (NagataCompactification (f ≫ g ≫ h)).hasCompactification
    let T := Compactification.Tower.ofHasCompactification f g h
    exact ⟨T, ambient_compactification Y.property T.cf,
      ambient_compactification Z.property T.cg, ambient_compactification W.property T.ch,
      ambient_compactification Z.property T.cfg, ambient_compactification W.property T.cgh,
      ambient_compactification W.property T.cfgh⟩

end AlgebraicGeometry.ProEtale.SpTowerCalculus
