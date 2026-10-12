/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # An internal determinant functional for a fixed tuple
Source: Stacks Project, Tags 0BRT and 03CY.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- A tuple of dual sections determines a unique internal functional on the exterior sheaf.
Source: Stacks Project, Tag 0BRT, determinant pairing; Tag 03CY, module sheafification.
(blueprint: lem-sc-exterior-dual-pairing-functional).

Proof: on each subopen V of U, evaluate the given dual sections on M(V) and
apply Mathlib's exterior-power determinant pairing. This gives a linear map
from the exterior power of M(V) to O(V). Naturality holds on pure wedges,
because the dual sections commute with restrictions and ring maps preserve
the determinant polynomial; pure wedges span, so it holds everywhere.
These maps form a morphism of module presheaves on Over U. Restrict the
exterior sheafification unit to this open site. It is locally bijective,
since its underlying abelian-presheaf map is the sheafification unit and
open restriction preserves local bijectivity. The structure sheaf restricted
to Over U is a sheaf. Thus the presheaf morphism extends uniquely across
the unit, giving q and the claimed formula. Uniqueness follows by agreement
on spanning pure wedges before extension. This construction works for n = 0,
empty opens and zero rings. -/
theorem exterior_dual_pairing_functional (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)) :
    ∃! q : (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op U),
      ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)),
        q.app (op (Over.mk g)) (Scheme.Modules.exteriorSheafSection M n V a) =
          (Matrix.of fun i j ↦ (show X.presheaf.obj (op V) from
            (φ j).app (op (Over.mk g)) (a i))).det := by sorry

end AlgebraicGeometry
