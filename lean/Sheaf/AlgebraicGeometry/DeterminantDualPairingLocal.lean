/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Local perfection of the exterior dual pairing
Source: Stacks Project, Tag 0BRT, determinant inversion.
(blueprint: lem-sc-exterior-dual-pairing-local-bijective).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- A determinant-formula morphism is bijective on sections below an open on which M
is finite free, in every exterior degree.
Source: Stacks Project, Tag 0BRT, determinant pairing; Mathlib
`exteriorPower.basis_coord` and the finite dual basis.
(blueprint: lem-sc-exterior-dual-pairing-local-bijective).

Proof: restrict the given trivialization to each V contained in U. Sections of the
finite free sheaf and its internal dual become the free section module and its
ring-linear dual; the inverse to evaluation reconstructs a natural sheaf map by
basis coordinates. The wedge bases identify the exterior sheaves on these opens
with the sectionwise exterior powers: the latter are finite free sheaves, and
sheafification restricted to the open is characterized by the same adjunction.
Under these identifications the assumed formula identifies f on pure wedges with
Mathlib's pairingDual. Pure wedges span the sectionwise exterior powers, so the
maps agree everywhere. The wedge of each dual basis vector maps to the
corresponding coordinate functional (`exteriorPower.basis_coord`). Since the wedge
basis is finite, these functionals form its dual basis, proving bijectivity.
When n exceeds the rank, both exterior modules are zero;
when n=0 both are the ring. Zero rings and empty opens are allowed. -/
theorem exterior_dual_pairing_app_bijective (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (f : Scheme.Modules.exteriorSheaf (Scheme.Modules.dual M) n ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n))
    (hf : ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U))
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
      (f.val.app (op U) (Scheme.Modules.exteriorSheafSection
        (Scheme.Modules.dual M) n U φ)).app (op (Over.mk (𝟙 U)))
        (Scheme.Modules.exteriorSheafSection M n U a) =
      (Matrix.of fun i j ↦
        (show X.presheaf.obj (op U) from
          (φ j).app (op (Over.mk (𝟙 U))) (a i))).det)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    (V : X.Opens) (g : V ⟶ U) :
    Function.Bijective (f.val.app (op V)) := by sorry

end AlgebraicGeometry
