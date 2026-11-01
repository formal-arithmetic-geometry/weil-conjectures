/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTwisting
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences

/-! # Invertibility of the specified Tate-line projection mate

Source: blueprint latest, smooth-purity tower classes proof, clause (4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The prescribed counit mate for positive Tate twisting is invertible.

Source: latest blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clause (4);
step 15 of `lem-sp-prescribed-projective-class-package`.
(blueprint: lem-sp-tower-class-projection-invertible).

Proof: localizing the exact ordinary tensor/Hom equivalences gives equivalences
on the ordinary unbounded derived categories. The normalized positive pullback
is an invertible square between these equivalences. Its right mate under the
specified geometric adjunction is invertible. Applying the inverse hom-set
adjunction to a component identifies this mate with the specified projection:
both become the pullback comparison followed by the twist of the counit.
No general projection formula or finite-level faithfulness is used. -/
theorem projection_isIso
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {cY : Chern l E Y} {cX : Chern l E X}
    {tY : Twisting l E cY} {tX : Twisting l E cX}
    {p : LinePullback l E f g cY cX} (v : PositivePullback l E f g tY tX p)
    (M : D X (Arings l E X)) : IsIso (projection l E g v M) := by
  have : (tY.T l E).IsEquivalence := by
    dsimp only [Twisting.T]
    infer_instance
  have : (tX.T l E).IsEquivalence := by
    dsimp only [Twisting.T]
    infer_instance
  let a := SpTowerShriek.adjunction l E b g
  have := isIso_mateEquiv_of_isEquivalence_of_fullyFaithful a a
    (tY.T l E) (tX.T l E) (v.derivedIso l E)
  have he : (mateEquiv a a (v.derivedIso l E).hom).natTrans.app M =
      projection l E g v M := by
    apply (a.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit]
    erw [mateEquiv_counit]
    exact (a.homEquiv _ _).symm_apply_apply _ |>.symm
  rw [← he]
  infer_instance

end AlgebraicGeometry.ProEtale.SpTowerClasses
