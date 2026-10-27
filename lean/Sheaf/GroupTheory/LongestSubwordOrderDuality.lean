module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Longest-element duality for reduced subword containment

Source: Brion--Kumar, *Frobenius Splitting Methods in Geometry and Representation Theory*,
Section 2.1, printed pp.61--63; Björner--Brenti, *Combinatorics of Coxeter Groups*,
Proposition 2.3.4 and Corollary 2.3.3, printed p.37.
(blueprint: lem-sfb-longest-subword-order-duality)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Subgroup

/-- Left multiplication by a longest element reverses reduced subword containment.
The family `s` is specified on every vector by the reflection formula `hs`; `Φplus`
is specified by `hΦplus`. Thus neither is an arbitrary action or positive-root set.
The two existential statements spell out the relation using `List.Sublist` and `IsLeast`.

Source: Brion--Kumar, Section 2.1, printed pp.61--63 (subword order and opposite cells);
Björner--Brenti, Proposition 2.3.4 and Corollary 2.3.3, printed p.37.
(blueprint: lem-sfb-longest-subword-order-duality)

Proof: (1) By `lem-sfb-simple-root-reflection-generation`, the root-reflection subgroup
equals the simple-reflection subgroup. Put N equal to the number of positive roots.
By `lem-sfb-root-length-inversion-count`, length counts the positive roots sent negative.
Both w₀ and its inverse swap the two signs. Complementing the inversion sets therefore
gives length(w₀w) = N - length(w) and length(w₀⁻¹w) = N - length(w).
(2) By `lem-sfb-root-subword-reflection-chains`, a subword inclusion gives an increasing
right-root-reflection chain from a to b. Reverse the chain and multiply on the left by w₀.
Each reflection squares to one, so the reversed edges are still right-reflection edges;
the complementary-length formula makes them increasing. The same chain criterion gives
the inclusion from w₀b to w₀a. (3) Conversely reverse a chain from w₀b to w₀a and multiply
on the left by w₀⁻¹. The identical calculation gives an increasing chain from a to b.
This does not require first proving w₀² = 1. (4) Equal endpoints use a chain of length zero.
In rank zero the root set and base are empty, the closure is the identity subgroup, and
the empty word is reduced. All arguments therefore include the asserted rank-zero case.
-/
theorem longest_subword_order_duality
    (V : Type u) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hBsymm : B.IsSymm)
    (hBpos : ∀ x : V, x ≠ 0 → 0 < B x x)
    (Φ : Finset V) (hΦzero : ∀ α ∈ Φ, α ≠ 0)
    (hΦspan : Submodule.span ℝ (Φ : Set V) = ⊤)
    (hΦline : ∀ α : Φ,
      (Φ : Set V) ∩ {x : V | ∃ t : ℝ, t • (α : V) = x} = {(α : V), -(α : V)})
    (s : Φ → LinearMap.GeneralLinearGroup ℝ V)
    (hs : ∀ (α : Φ) (x : V),
      (s α).toLinearEquiv x = x - (2 * B x α / B α α) • (α : V))
    (hΦreflect : ∀ α : Φ, Set.BijOn (s α) (Φ : Set V) (Φ : Set V))
    (hΦint : ∀ α β : Φ, ∃ z : ℤ, 2 * B β α / B α α = (z : ℝ))
    (Δ : Set Φ) (basis : Module.Basis Δ ℝ V)
    (hbasis : ∀ i : Δ, basis i = (i.val : V))
    (hcoords : ∀ α : Φ, (∀ i : Δ, ∃ z : ℤ, basis.coord i α = (z : ℝ)) ∧
      ((∀ i : Δ, 0 ≤ basis.coord i α) ∨ (∀ i : Δ, basis.coord i α ≤ 0)))
    (Φplus : Set V)
    (hΦplus : Φplus = {x : V | x ∈ Φ ∧ ∀ i : Δ, 0 ≤ basis.coord i x})
    (w₀ a b : Subgroup.closure (Set.range s))
    (hw₀ : w₀.val.toLinearEquiv '' Φplus = (fun x : V ↦ -x) '' Φplus) :
    (∃ v t : List Δ,
      (v.map (fun i ↦ s i.val)).prod = b.val ∧
      IsLeast {n : ℕ | ∃ l : List Δ,
        (l.map (fun i ↦ s i.val)).prod = b.val ∧ l.length = n} v.length ∧
      t.Sublist v ∧ (t.map (fun i ↦ s i.val)).prod = a.val ∧
      IsLeast {n : ℕ | ∃ l : List Δ,
        (l.map (fun i ↦ s i.val)).prod = a.val ∧ l.length = n} t.length) ↔
    (∃ v t : List Δ,
      (v.map (fun i ↦ s i.val)).prod = (w₀ * a).val ∧
      IsLeast {n : ℕ | ∃ l : List Δ,
        (l.map (fun i ↦ s i.val)).prod = (w₀ * a).val ∧ l.length = n} v.length ∧
      t.Sublist v ∧ (t.map (fun i ↦ s i.val)).prod = (w₀ * b).val ∧
      IsLeast {n : ℕ | ∃ l : List Δ,
        (l.map (fun i ↦ s i.val)).prod = (w₀ * b).val ∧ l.length = n} t.length) := by
  sorry

end Subgroup
