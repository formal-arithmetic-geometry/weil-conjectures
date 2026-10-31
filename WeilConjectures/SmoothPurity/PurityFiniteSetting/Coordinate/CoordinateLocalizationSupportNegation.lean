/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData

/-! # Negation through supported Gysin evaluation

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
finite etale-origin transport paragraph
(blueprint: lem-pur-coordinate-localization-support-negation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

namespace WeilConjectures.PurityFiniteSetting

/-- The normalized supported evaluation is additive in the derived morphism.
Source: current blueprint, finite etale-origin transport paragraph
(blueprint: lem-pur-coordinate-localization-support-negation).

Proof: expand gysinHomToSections and gysinEvaluate. The homology functor, comparison
adjunction hom-equivalences, evaluation on the constant unit, and the support
isomorphism are additive. The canonical morphism negation therefore passes through
all factors and is evaluated as the additive inverse in the coefficient module.
-/
theorem gysinSupportEvaluation_neg (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (m : P.derivedSheaf h T false ⟶ P.gysinValue h T)
    (D : OrientationSupportData P h T) :
    D.support.hom (P.gysinHomToSections h T (-m)) =
      -D.support.hom (P.gysinHomToSections h T m) := by
  have hneg : P.gysinHomToSections h T (-m) =
      -P.gysinHomToSections h T m := by
    simp only [gysinHomToSections, Functor.map_neg, Preadditive.comp_neg]
    rfl
  rw [hneg, map_neg]

end WeilConjectures.PurityFiniteSetting
