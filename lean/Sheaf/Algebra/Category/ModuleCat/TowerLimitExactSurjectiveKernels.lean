/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Exact.Basic

import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Sheaf.Algebra.Category.ModuleCat.TowerLimitInducedMaps
import Sheaf.Algebra.Category.ModuleCat.TowerLimitExactCoordinateMaps

/-!
# Inverse limits of towers and exact sequences

Source: Stacks Project, Algebra Lemma 03CA and Homology Lemma 02N1
(blueprint: lem-weil-pbc-tower-limit-exact-surjective-kernels).

## Main statements

* `tower_limit_projection_surjective`: every projection of a surjective tower is surjective.
* `tower_limit_exact_surjective_kernels`: left exactness and the surjective-kernel conclusion.

The natural index `n` denotes the paper's positive index `n + 1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v w t

/-- Every projection from the limit of a tower with surjective transitions is surjective.
Source: Stacks Project, Algebra Lemma 0597, used in Cohomology of Schemes Lemma 087W
(blueprint: lem-weil-pbc-tower-limit-exact-surjective-kernels).

Proof, step (a): fix a coordinate `m` and an element there. At indices below `m`, use
its images under the transition composites (def-weil-inverse-system). At indices above `m`,
recursively choose preimages under the surjective successor maps. The resulting compatible
sequence belongs to the limit and projects to the given element. -/
theorem tower_limit_projection_surjective
    (R : Type u) [CommRing R] (K : ℕ → ModuleCat.{v} R)
    (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
    (hsurj : ∀ n : ℕ, Function.Surjective (f n)) :
    ∀ m : ℕ, Function.Surjective (limit.π (Functor.ofOpSequence f) (Opposite.op m)) := by
  intro m
  let shift : ℕ ⥤ ℕ := (show Monotone (fun n : ℕ ↦ m + n) from
    fun _ _ h ↦ Nat.add_le_add_left h m).functor
  have hfinal : shift.Final := by
    apply (Monotone.final_functor_iff _).2
    intro n
    exact ⟨n, Nat.le_add_left n m⟩
  have hc := (Functor.Initial.isLimitWhiskerEquiv shift.op
    (limit.cone (Functor.ofOpSequence f))).symm (limit.isLimit _)
  have hs : ∀ n, Function.Surjective
      ((shift.op ⋙ Functor.ofOpSequence f).map (homOfLE (Nat.le_succ n)).op) := by
    intro n
    change Function.Surjective ((Functor.ofOpSequence f).map
      (homOfLE (Nat.le_succ (m + n))).op)
    convert hsurj (m + n) using 1
    all_goals simp [Functor.ofOpSequence_map_homOfLE_succ]
    all_goals rfl
  exact Concrete.surjective_π_app_zero_of_surjective_map hc hs

/-- The limit of a short exact sequence of towers is left exact, and short exact when the
kernel transitions are surjective. Source: Stacks Project, Algebra Lemma 03CA and
Homology Lemma 02N1 (blueprint: lem-weil-pbc-tower-limit-exact-surjective-kernels).

The induced linear maps are characterized by their coordinate projections, allowing the
three towers to have independent universes.

Proof, steps (b): (1) Naturality (`hα`, `hβ`) makes componentwise application of the two maps
preserve
compatible sequences; their composite is zero by pointwise exactness
(def-weil-inverse-system, def-weil-pbc-exact-sequence).
(2) The first induced map is injective since every component is injective.
(3) A compatible sequence in the kernel of the second map has unique preimages under the
first maps; naturality and injectivity force these preimages to be compatible. This proves
exactness in the middle.
(4) Under surjective kernel transitions, lift a quotient sequence recursively. Having chosen
`b_n`, choose any lift `b'` of the next quotient coordinate. Its transition minus `b_n` is in
the kernel; write it as `u_n(k)` and lift `k` to `k'` at the next index. Replace `b'` by
`b' - u_{n+1}(k')`. This corrects its transition without changing its quotient coordinate.
(5) Recursive choice gives a compatible lift of the entire quotient sequence, proving
surjectivity. Together with (2) and (3), this gives short exactness
(def-weil-pbc-exact-sequence), as in Algebra Lemma 0598 specialized to surjective kernels. -/
theorem tower_limit_exact_surjective_kernels
    (R : Type u) [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (G : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (H : ℕᵒᵖ ⥤ ModuleCat.{t} R)
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (β : ∀ n : ℕ, G.obj (Opposite.op n) →ₗ[R] H.obj (Opposite.op n))
    (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))),
      G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) =
        α n (F.map (homOfLE (Nat.le_add_right n 1)).op x))
    (hβ : ∀ (n : ℕ) (x : G.obj (Opposite.op (n + 1))),
      H.map (homOfLE (Nat.le_add_right n 1)).op (β (n + 1) x) =
        β n (G.map (homOfLE (Nat.le_add_right n 1)).op x))
    (hshort : ∀ n : ℕ, Function.Injective (α n) ∧ Function.Exact (α n) (β n) ∧
      Function.Surjective (β n)) :
    ∃ (U : ↑(limit F) →ₗ[R] ↑(limit G)) (V : ↑(limit G) →ₗ[R] ↑(limit H)),
      (∀ (n : ℕ) (x : ↑(limit F)),
        limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x)) ∧
      (∀ (n : ℕ) (x : ↑(limit G)),
        limit.π H (Opposite.op n) (V x) = β n (limit.π G (Opposite.op n) x)) ∧
      Function.Injective U ∧ Function.Exact U V ∧
      ((∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_add_right n 1)).op)) →
        Function.Surjective V) := by
  obtain ⟨U, V, hU, hV⟩ := tower_limit_induced_maps R F G H α β hα hβ
  obtain ⟨hUi, hEx, hVs⟩ := tower_limit_exact_of_coordinate_maps
    R F G H α β hshort U V hU hV
  exact ⟨U, V, hU, hV, hUi, hEx, hVs⟩

end CategoryTheory
