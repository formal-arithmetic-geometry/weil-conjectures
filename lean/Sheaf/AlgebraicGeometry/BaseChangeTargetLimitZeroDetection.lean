/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition

/-! # Finite-stage detection of zero in target stalks

Source: Stacks Project Tag 09Z1 and the limit step of Tag 0F07.
(blueprint: lem-sbc-target-limit-zero-detection)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} [IsAffine S]
variable (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over T)
variable [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
variable [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]

/-- A target-stalk element that dies at the limit dies after a transition in the diagram.

Source: Stacks Tag 09Z1, applied to the target side in Tag 0F07 condition (2).
(blueprint: lem-sbc-target-limit-zero-detection)

Proof: Base change the cone of schemes along p. The resulting cone is a limit cone,
and its transition maps are affine. The structure maps to X are base changes of the
qcqs stage maps to the affine S, so they and the limit structure map are qcqs. On the
resulting system pull back the fixed sheaf F from Y = T ×_S X. The inverse-image
composition isomorphisms identify these coefficients with e_i^* (π_i^* F), and identify
the restriction maps with baseChangeTargetStalkMap. Higher-direct-image continuity
therefore expresses the limit target sheaf as the filtered colimit of the stage target
sheaves. Taking the geometric stalk preserves this colimit. The elementwise zero
criterion for a filtered colimit of modules says that a representative whose image is
zero is already zero at some later stage. In negative degree the target sheaves are
zero and one can take j = i and the identity. This is the asserted criterion.
-/
theorem baseChange_target_limit_zero_detection (c : Cone D)
    (hc : IsLimit ((Over.forget T).mapCone c)) (i : I)
    (ζ : baseChangeTargetStalk Λ p g q F x (D.obj i))
    (hζ : (baseChangeTargetStalkMap Λ p g q F x (c.π.app i)).hom ζ = 0) :
    ∃ (j : I) (f : j ⟶ i),
      (baseChangeTargetStalkMap Λ p g q F x (D.map f)).hom ζ = 0 := by sorry

end AlgebraicGeometry.Etale
