/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Topology.ProfiniteCechTuples
import Sheaf.Topology.FiniteCoefficientCechPrimitiveLift

/-!
# Continuous inverse-limit Cech primitives with prescribed first reduction

Source: Bhatt–Scholze, The pro-etale topology for schemes, Lemma 4.3.9(2),(4), p. 33,
expanded into the pointwise Cech assertion in the DAG
(blueprint: lem-sfb-inverse-limit-cech-primitive).

The limit is the explicit compatible-sequence subtype with the product/subspace topology.
Both differential equations are written coordinatewise. The index `m` denotes level `m + 1`
of the node, and `n` denotes one less than its positive cochain degree.
-/

@[expose] public section

universe u v

namespace Profinite

/-- A continuous inverse-limit-valued positive Cech cocycle has a continuous primitive
with any prescribed primitive at its first finite level.

Source: Bhatt–Scholze, Lemma 4.3.9(2),(4), printed p. 33; the explicit pointwise statement
is agent-formulated in the DAG (blueprint: lem-sfb-inverse-limit-cech-primitive).

Proof: (1) Project the cocycle to each finite level. The projections are continuous,
commute with finite signed sums, and satisfy the transition equations of the limit.
(2) Apply lem-sfb-finite-coefficient-cech-primitive-lift to each surjective transition,
starting at the prescribed first primitive. Choose successive lifts recursively. The
invariant says that each entry is a primitive, successive entries reduce to the preceding
one, and the first entry is the prescribed one. (3) The compatible primitives define a
map into the displayed subtype. Its inverse image of any finite-coordinate open cylinder
is a finite intersection of open inverse images, proving continuity for the actual
product/subspace topology. (4) The differential agrees with the cocycle in every
coordinate, hence in the limit. The first coordinate is unchanged. Conversely, reductions
of a limit primitive satisfy the transition equations by membership in the subtype, and
the finite-level differential equations by additivity of projections. For empty spaces
all positive-length tuple domains are empty; zero groups introduce no exception. -/
theorem exists_inverseLimit_cech_primitive
    (S T : Profinite.{v}) (q : C(T, S)) (hq : Function.Surjective q)
    (A : ℕ → Type u) [∀ m : ℕ, AddCommGroup (A m)]
    [∀ m : ℕ, Finite (A m)] [∀ m : ℕ, TopologicalSpace (A m)]
    [∀ m : ℕ, DiscreteTopology (A m)]
    (p : ∀ m : ℕ, A (m + 1) →+ A m) (hp : ∀ m : ℕ, Function.Surjective (p m))
    (n : ℕ)
    (f : C(scalarCechTuples q (n + 2),
      {a : (m : ℕ) → A m // ∀ m : ℕ, p m (a (m + 1)) = a m}))
    (hf : ∀ (m : ℕ) (x : scalarCechTuples q (n + 3)),
      ∑ j : Fin (n + 3), (-1 : ℤ) ^ j.val • (f (scalarCechDelete q (n + 2) j x)).val m = 0)
    (u₁ : C(scalarCechTuples q (n + 1), A 0))
    (hu₁ : ∀ x : scalarCechTuples q (n + 2),
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • u₁ (scalarCechDelete q (n + 1) j x) =
        (f x).val 0) :
    ∃ u : C(scalarCechTuples q (n + 1),
        {a : (m : ℕ) → A m // ∀ m : ℕ, p m (a (m + 1)) = a m}),
      (∀ (m : ℕ) (x : scalarCechTuples q (n + 2)),
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
          (u (scalarCechDelete q (n + 1) j x)).val m = (f x).val m) ∧
      (∀ x : scalarCechTuples q (n + 1), (u x).val 0 = u₁ x) := by
  classical
  -- Record a primitive and its differential equation at each finite level.
  let fₘ (m : ℕ) : C(scalarCechTuples q (n + 2), A m) :=
    ⟨fun x ↦ (f x).val m,
      (continuous_apply m).comp (continuous_subtype_val.comp f.continuous)⟩
  let X (m : ℕ) := {w : C(scalarCechTuples q (n + 1), A m) //
    ∀ x : scalarCechTuples q (n + 2),
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val • w (scalarCechDelete q (n + 1) j x) =
        fₘ m x}
  have step (m : ℕ) (w : X m) :
      ∃ v : X (m + 1), ∀ x, p m (v.val x) = w.val x := by
    obtain ⟨v, hv, hd⟩ := finite_coefficient_cech_primitive_lift
      S T q hq (A m) (A (m + 1)) (p m) (hp m) (n + 1) (Nat.le_add_left 1 n)
      (fₘ (m + 1)) (hf (m + 1)) w.val
      (fun x ↦ (w.property x).trans ((f x).property m).symm)
    exact ⟨⟨v, hd⟩, hv⟩
  -- Choice selects a successor; recursion retains the prescribed zeroth entry.
  let w : (m : ℕ) → X m :=
    Nat.rec ⟨u₁, hu₁⟩ (fun m v ↦ (step m v).choose)
  have compat (m : ℕ) (x : scalarCechTuples q (n + 1)) :
      p m ((w (m + 1)).val x) = (w m).val x :=
    (step m (w m)).choose_spec x
  refine ⟨⟨fun x ↦ ⟨fun m ↦ (w m).val x, fun m ↦ compat m x⟩,
    (continuous_pi fun m ↦ (w m).val.continuous).subtype_mk _⟩, ?_, ?_⟩
  · exact fun m x ↦ (w m).property x
  · exact fun _ ↦ rfl

end Profinite
