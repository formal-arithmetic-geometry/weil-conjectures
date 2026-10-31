/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.IntegralLatticeCubicalDefs

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

import WeilConjectures.AlgebraicTopology.CubicalBoundaryCoordinateProjections
import WeilConjectures.AlgebraicTopology.CubicalSignedCoordinateHomotopy
import Mathlib.Tactic.Abel

/-!
# Integral cubical chains of a lattice

Source: Stacks Project, more-algebra.tex, Tags 0623 and 062F, for the algebraic
Koszul ingredients; the signed-coordinate contraction is the agent-written construction
in the DAG proof (blueprint: lem-sfb-integral-lattice-cubical-contraction).

The terms are free modules on lattice points and subsets of coordinates. Integer degrees
include the zero extension outside degrees zero through the rank. The final theorem states
all chain, contraction, exactness, translation, and finite free-orbit assertions together.
-/

@[expose] public section

set_option autoImplicit false

namespace IntegralLatticeCubical

private noncomputable def listProjection (r : ℕ) (l : List (Fin r)) (a : ℤ) :
    Chains r a →ₗ[ℤ] Chains r a :=
  l.foldr (fun i P ↦ (coordinateProjection r a i).comp P) LinearMap.id

private noncomputable def listHomotopy (r : ℕ) (l : List (Fin r)) (a : ℤ) :
    Chains r a →ₗ[ℤ] Chains r (a + 1) :=
  l.foldr (fun i H ↦ coordinateHomotopy r i a +
    (coordinateProjection r (a + 1) i).comp H) 0

private theorem projection_cast (r : ℕ) (i : Fin r) (a b : ℤ) (h : a = b)
    (x : Chains r a) :
    LinearEquiv.cast (R := ℤ) (M := Chains r) h (coordinateProjection r a i x) =
      coordinateProjection r b i (LinearEquiv.cast (R := ℤ) (M := Chains r) h x) := by
  subst b
  rfl

private theorem projection_incoming (r : ℕ) (i : Fin r) (a : ℤ)
    (x : Chains r (a + 1)) :
    incomingBoundary r a (coordinateProjection r (a + 1) i x) =
      coordinateProjection r a i (incomingBoundary r a x) := by
  have hp := (boundary_coordinate_projections r).2.2.2.2.2.1 i (a + 1)
  have he := LinearMap.congr_fun hp x
  simpa only [incomingBoundary, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    projection_cast] using congrArg
      (LinearEquiv.cast (R := ℤ) (M := Chains r) (add_sub_cancel_right a 1)) he

private theorem list_identity (r : ℕ) (l : List (Fin r)) (a : ℤ)
    (x : Chains r a) :
    incomingBoundary r a (listHomotopy r l a x) +
      LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
        (listHomotopy r l (a - 1) (boundary r a x)) =
      x - listProjection r l a x := by
  induction l with
  | nil =>
    simp only [listHomotopy, listProjection, List.foldr_nil, LinearMap.zero_apply,
      map_zero, LinearMap.id_apply, sub_self, add_zero]
  | cons i l ih =>
    have hi := LinearMap.congr_fun
      ((signedCoordinateHomotopy.{0} r).2.2.2.2.2.2.1 i a) x
    have hp : pathCoordinateProjection r i a = coordinateProjection r a i := rfl
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.sub_apply, LinearMap.id_apply, hp] at hi
    simp only [listHomotopy, List.foldr_cons, LinearMap.add_apply, LinearMap.comp_apply,
      map_add, projection_incoming, projection_cast]
    change incomingBoundary r a (coordinateHomotopy r i a x) +
        coordinateProjection r a i (incomingBoundary r a (listHomotopy r l a x)) +
        (LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
          (coordinateHomotopy r i (a - 1) (boundary r a x)) +
        coordinateProjection r a i
          (LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
            (listHomotopy r l (a - 1) (boundary r a x)))) =
      x - coordinateProjection r a i (listProjection r l a x)
    rw [show ∀ u v w z : Chains r a, u + v + (w + z) = (u + w) + (v + z)
      from fun u v w z ↦ by abel, hi, ← map_add, ih, map_sub]
    abel

private theorem origin_zero (r : ℕ) :
    originProjection r 0 = (sectionMap r).comp (augmentation r) := by
  apply Finsupp.lhom_ext
  rintro ⟨v, I⟩ n
  simp [originProjection, sectionMap, augmentation]

private theorem origin_other (r : ℕ) (a : ℤ) (ha : a ≠ 0) :
    originProjection r a = 0 := by
  apply Finsupp.lhom_ext
  intro c n
  simp [originProjection, cell, Ne.symm ha]

private theorem full_projection (r : ℕ) (a : ℤ) :
    listProjection r (List.finRange r) a = originProjection r a := by
  have he : listProjection r (List.finRange r) a = coordinateProduct r a r := by
    have ht : (List.finRange r).take r = List.finRange r :=
      List.take_of_length_le (by simp)
    simp only [listProjection, coordinateProduct, ht]
  rw [he]
  by_cases ha : a = 0
  · subst a
    exact (boundary_coordinate_projections r).2.2.2.2.2.2.2.1.trans (origin_zero r).symm
  · rw [(boundary_coordinate_projections r).2.2.2.2.2.2.2.2.1 a ha, origin_other r a ha]

private theorem incoming_squared (r : ℕ) (a : ℤ) (x : Chains r (a + 1)) :
    boundary r a (incomingBoundary r a x) = 0 := by
  have h := LinearMap.congr_fun ((boundary_coordinate_projections r).2.2.2.1 (a + 1)) x
  have transport (b c : ℤ) (hbc : b = c) (y : Chains r b) :
      boundary r c (LinearEquiv.cast (R := ℤ) (M := Chains r) hbc y) =
        LinearEquiv.cast (R := ℤ) (M := Chains r)
          (congrArg (fun n : ℤ ↦ n - 1) hbc) (boundary r b y) := by
    subst c
    rfl
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  simp only [incomingBoundary, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    transport, h, map_zero]

/-- Integral cubical chains retract onto the augmentation, with their stated translation
and free-orbit structure. Kernel equals image states exactness of the augmented complex
in the explicit module sense used by `ShortComplex.moduleCatLeftHomologyData`.

Source: the agent-written eight-step proof of the DAG node; Stacks Tags 0623 and 062F
supply only the comparison with Koszul complexes, not the nonequivariant contraction.
(blueprint: lem-sfb-integral-lattice-cubical-contraction).

Proof plan:
1. Extend finite basis sums by the free-module universal property. Pair the two orders of
removing distinct directions: their signs are opposite and the translations commute.
This gives boundary squared zero. The augmentation of an edge boundary is `1 - 1`.
2. Reset coordinate `i` to zero on cells not containing `i`, killing the others, to get
commuting chain maps `p_i`. All non-`i` faces commute with resetting, and the `i` face cancels.
3. For every integer `n`, sum edges from zero to `n`, using the negative of the sum from
`n` to zero for `n < 0`. Consecutive differences telescope, also at `n = -1` and `n = 0`.
For `i` absent from the directions, insert it with sign given by the number of smaller
directions and take this signed path in coordinate `i`; otherwise put `H_i = 0`.
4. On a cell not containing `i`, the `i` face telescopes to the cell minus its reset.
The other faces cancel with `H_i` applied to the boundary, since the two exponents differ
by one, both for directions smaller and for directions greater than `i`.
5. On a cell containing `i`, only its `i` face survives after `H_i`. The two signs multiply
to one and the difference of consecutive path sums is the original cell. Thus
`boundary H_i + H_i boundary = 1 - p_i` in every degree, including the top one.
6. With `P_i = p_1 ... p_i`, sum `P_(i-1) H_i` over the coordinates. The contraction identity
telescopes to `1 - P_r`. The product kills positive-dimensional cells and sends each vertex
to the origin, so it is `e`. The augmentation of the origin is one.
7. A cycle in positive degree is the boundary of its homotopy; a vertex chain of augmentation
zero is likewise a boundary. The section proves augmentation surjectivity. This is exactly
kernel equals image, hence vanishing augmented homology, for the module-chain-complex
notion of def-weil-pbc-module-chain-complex-homology. When `r = 0`, all positive terms and
all homotopies vanish, and identify the unique vertex's free group with the integers.
8. Translation commutes termwise with the differential and the augmentation. Partition the
free basis by its finite set of directions, obtaining one regular translation module per
subset. No equivariance is imposed on the homotopy or section (the latter already fails
translation invariance in rank one). Both steps use def-weil-pbc-free-module. -/
theorem contraction (r : ℕ) :
    (∀ a : ℤ, (boundary r (a - 1)).comp (boundary r a) = 0) ∧
    (augmentation r).comp (boundary r 1) = 0 ∧
    (augmentation r).comp (sectionMap r) = LinearMap.id ∧
    originProjection r 0 = (sectionMap r).comp (augmentation r) ∧
    (∀ a : ℤ, a ≠ 0 → originProjection r a = 0) ∧
    (∀ a : ℤ, a < 0 ∨ (r : ℤ) < a → Subsingleton (Chains r a)) ∧
    (∀ a : ℤ, Module.Free ℤ (Chains r a)) ∧
    (∃ h : (a : ℤ) → Chains r a →ₗ[ℤ] Chains r (a + 1),
      (∀ (a : ℤ) (_ : 0 ≤ a) (x : Chains r a),
        incomingBoundary r a (h a x) +
          LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
            (h (a - 1) (boundary r a x)) =
          x - originProjection r a x) ∧
      (∀ x : Chains r 0, h (-1) (boundary r 0 x) = 0) ∧
      (r = 0 → ∀ a : ℤ, h a = 0)) ∧
    (∀ a : ℤ, 0 < a →
      LinearMap.range (incomingBoundary r a) = LinearMap.ker (boundary r a)) ∧
    LinearMap.range (boundary r 1) = LinearMap.ker (augmentation r) ∧
    Function.Surjective (augmentation r) ∧
    (∀ (a : ℤ) (w : Fin r → ℤ),
      (boundary r a).comp (translate r a w) =
        (translate r (a - 1) w).comp (boundary r a)) ∧
    (∀ w : Fin r → ℤ, (augmentation r).comp (translate r 0 w) = augmentation r) ∧
    (∀ a : ℤ, Finite (Directions r a)) ∧
    (∀ a : ℤ, ∃ e : Chains r a ≃ₗ[ℤ] (Directions r a →₀ ((Fin r → ℤ) →₀ ℤ)),
      (∀ (v : Fin r → ℤ) (I : Directions r a),
        e (Finsupp.single (v, I) 1) = Finsupp.single I (Finsupp.single v 1)) ∧
      (∀ (w : Fin r → ℤ) (x : Chains r a) (I : Directions r a),
        e (translate r a w x) I = Finsupp.mapDomain (fun v ↦ v + w) (e x I))) ∧
    (r = 0 → ∃ e : Chains r 0 ≃ₗ[ℤ] ℤ,
      e.toLinearMap = augmentation r ∧ e.symm.toLinearMap = sectionMap r) := by
  classical
  obtain ⟨hfree, hout, hnonpos, hsq, haug, hp, hcomm, hprod, hprodother,
    htrans, haugtrans, hfinite, horbit, hrank⟩ := boundary_coordinate_projections r
  have hs : (augmentation r).comp (sectionMap r) = LinearMap.id := by
    ext
    simp [sectionMap, augmentation, cell]
  let h := listHomotopy r (List.finRange r)
  have hidentity (a : ℤ) (x : Chains r a) :
      incomingBoundary r a (h a x) +
        LinearEquiv.cast (R := ℤ) (M := Chains r) (sub_add_cancel a 1)
          (h (a - 1) (boundary r a x)) = x - originProjection r a x := by
    simpa only [h, full_projection] using list_identity r (List.finRange r) a x
  have hexact (a : ℤ) (ha : 0 < a) :
      LinearMap.range (incomingBoundary r a) = LinearMap.ker (boundary r a) := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact incoming_squared r a y
    · intro x hx
      refine ⟨h a x, ?_⟩
      have he := hidentity a x
      have hz : boundary r a x = 0 := hx
      simpa only [hz, map_zero, add_zero, origin_other r a (ne_of_gt ha),
        LinearMap.zero_apply, sub_zero] using he
  have hexact0 : LinearMap.range (boundary r 1) = LinearMap.ker (augmentation r) := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact LinearMap.congr_fun haug y
    · intro x hx
      refine ⟨h 0 x, ?_⟩
      have he := hidentity 0 x
      have hz : augmentation r x = 0 := hx
      have hb : boundary r 0 x = 0 := by rw [hnonpos 0 (by omega)]; rfl
      change incomingBoundary r 0 (h 0 x) = x
      simpa only [hb, map_zero, add_zero, origin_zero, LinearMap.comp_apply,
        hz, sub_zero] using he
  refine ⟨hsq, haug, hs, origin_zero r, origin_other r, hout, hfree,
    ⟨h, fun a _ x ↦ hidentity a x, ?_, ?_⟩, hexact, hexact0, ?_,
    fun a w ↦ htrans w a, haugtrans, hfinite, horbit, hrank⟩
  · intro x
    rw [hnonpos 0 (by omega), LinearMap.zero_apply]
    exact (h (-1)).map_zero
  · intro hr a
    subst r
    simp [h, listHomotopy]
  · intro z
    refine ⟨sectionMap r z, ?_⟩
    exact LinearMap.congr_fun hs z

end IntegralLatticeCubical
