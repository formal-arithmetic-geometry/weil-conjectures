/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.AlgebraicGeometry.StructureSheafCohomologyPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.PicardH1ProductInjective

/-!
# Joint H¹ injectivity of the two product slices after residue-field base change

Source: Stacks Project, Tag 0BF3, Kunneth input in the proof.
(blueprint: lem-sc-product-residue-h1-injective).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The residue-field base changes of the two section slices jointly detect H¹.
Source: Stacks Project, Tag 0BF3, first sentence of its proof, using Tag 0BED.
(blueprint: lem-sc-product-residue-h1-injective).

Proof: set k = κ(s). Universal structure pushforward evaluated at Spec k identifies
H⁰(X_s, O) and H⁰(Y_s, O) with k, through the canonical scalar maps. Base change of
σ and τ gives k-rational points of these proper k-schemes. Apply
picard_h1_product_injective to X_s and Y_s. Pullback pasting identifies
(X ×_S Y)_s with X_s ×_k Y_s, and identifies the two base-changed slice morphisms
with the rational-point slices in that theorem. Functoriality of structure-sheaf
cohomology transports the injectivity along this scheme isomorphism. Thus equality
of both slice images forces equality of the source classes. Neither a line bundle
nor its trivializations enter this assertion. -/
theorem product_residue_h1_injective
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsProper f] [IsProper g]
    (σ : S ⟶ X) (τ : S ⟶ Y)
    (hσ : σ ≫ f = 𝟙 S) (hτ : τ ≫ g = 𝟙 S)
    (hX : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hY : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd g t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (s : S) :
    let p := pullback.fst f g ≫ f
    let iX := pullback.lift (𝟙 X) (f ≫ τ) (by simp [hτ])
    let iY := pullback.lift (g ≫ σ) (𝟙 Y) (by simp [hσ])
    let hiX : iX ≫ p = f := by
      dsimp only [p]
      rw [← Category.assoc, pullback.lift_fst, Category.id_comp]
    let hiY : iY ≫ p = g := by
      dsimp only [p]
      rw [← Category.assoc, pullback.lift_fst, Category.assoc, hσ, Category.comp_id]
    Function.Injective (fun x :
        Sheaf.H (structureSheafAb (pullback p (S.fromSpecResidueField s))) 1 ↦
      (structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk f) (V := Over.mk p) iX hiX)).left) 1 x,
       structureSheafCohomologyPullback
        (((Over.pullback (S.fromSpecResidueField s)).map
          (Over.homMk (U := Over.mk g) (V := Over.mk p) iY hiY)).left) 1 x)) := by
  sorry

end AlgebraicGeometry.Scheme
