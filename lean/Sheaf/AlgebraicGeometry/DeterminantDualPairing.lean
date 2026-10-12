/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Construction of the exterior dual pairing
Source: Stacks Project, Tag 0BRT, determinant inversion.
(blueprint: lem-sc-exterior-dual-pairing-construction).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- The determinant of evaluation defines a morphism of exterior sheaves, in every degree
and without any local freeness assumption.
Source: Stacks Project, Tag 0BRT, determinant pairing; Mathlib
`exteriorPower.pairingDual_ιMulti_ιMulti`.
(blueprint: lem-sc-exterior-dual-pairing-construction).

Proof: for an open U and a tuple of internal dual sections, on each V contained in U
apply the determinant of their evaluations to tuples of M(V). This is alternating
and multilinear in both tuples, so the universal property of exterior powers gives
an exterior-power functional on every V. Evaluation is natural under restriction;
ring homomorphisms preserve the determinant. Thus these functionals form a morphism
from the exterior presheaf restricted to U to the structure sheaf restricted to U.
The sheafification adjunction extends it uniquely to the exterior sheaf. The same
uniqueness proves compatibility when U shrinks. Alternation in the dual tuple then
gives a map from the exterior presheaf of the internal dual to the internal dual of
the exterior sheaf, which is a sheaf. Sheafify again to obtain f. Both adjunction
units give exactly the displayed formula. Empty tuples give the determinant 1, and
all constructions work over the zero ring and on the empty open. -/
theorem exterior_dual_pairing_exists (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    ∃ f :
    (Scheme.Modules.exteriorSheaf (Scheme.Modules.dual M) n) ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n),
    ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U))
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
      (f.val.app (op U) (Scheme.Modules.exteriorSheafSection
        (Scheme.Modules.dual M) n U φ)).app (op (Over.mk (𝟙 U)))
        (Scheme.Modules.exteriorSheafSection M n U a) =
      (Matrix.of fun i j ↦
        (show X.presheaf.obj (op U) from
          (φ j).app (op (Over.mk (𝟙 U))) (a i))).det := by sorry

end AlgebraicGeometry
