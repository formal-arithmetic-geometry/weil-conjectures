module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

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

/-- Coordinate subsets in degree `a`; empty outside the range from zero to `r`.
Source: the displayed basis in the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
def Directions (r : ℕ) (a : ℤ) := {I : Finset (Fin r) // (I.card : ℤ) = a}

/-- The free abelian group on the cubical cells in degree `a`.
Source: the basis clause of the DAG statement; freeness is Mathlib's `Module.Free`.
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
abbrev Chains (r : ℕ) (a : ℤ) := ((Fin r → ℤ) × Directions r a) →₀ ℤ

/-- The symbol `[v,I]`, with value zero when `I` has the wrong cardinality.
Source: the zero-extension convention in the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def cell (r : ℕ) (a : ℤ) (v : Fin r → ℤ) (I : Finset (Fin r)) : Chains r a :=
  if h : (I.card : ℤ) = a then Finsupp.single (v, ⟨I, h⟩) 1 else 0

/-- The standard basis vector `u_i` of the lattice.
Source: the first sentence of the DAG statement
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
def unitVector (r : ℕ) (i : Fin r) : Fin r → ℤ := Pi.single i 1

/-- The integral alternating cubical differential, extended linearly from the given basis.
Source: DAG displayed differential, compared with Stacks Tag 0623's alternating differential
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def boundary (r : ℕ) (a : ℤ) : Chains r a →ₗ[ℤ] Chains r (a - 1) :=
  Finsupp.linearCombination ℤ fun c ↦
    ∑ i ∈ c.2.val, (-1 : ℤ) ^ (c.2.val.filter (fun j ↦ j < i)).card •
      (cell r (a - 1) (c.1 + unitVector r i) (c.2.val.erase i) -
        cell r (a - 1) c.1 (c.2.val.erase i))

/-- The same boundary from degree `a + 1` into degree `a`, with canonical degree transport.
Source: the indices in the DAG contraction and exactness clauses
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def incomingBoundary (r : ℕ) (a : ℤ) :
    Chains r (a + 1) →ₗ[ℤ] Chains r a :=
  (LinearEquiv.cast (R := ℤ) (M := Chains r) (add_sub_cancel_right a 1)).toLinearMap.comp
    (boundary r (a + 1))

/-- The augmentation taking each vertex to one.
Source: DAG augmentation clause
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def augmentation (r : ℕ) : Chains r 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ fun _ ↦ 1

/-- The section taking one to the vertex at the origin, with actual specified data.
Source: DAG section clause
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def sectionMap (r : ℕ) : ℤ →ₗ[ℤ] Chains r 0 :=
  LinearMap.toSpanSingleton ℤ (Chains r 0) (cell r 0 0 ∅)

/-- The endomorphism `e`, equal to section times augmentation in degree zero and zero
elsewhere: the cell constructor makes the displayed empty direction zero in other degrees.
Source: DAG definition of `e`
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def originProjection (r : ℕ) (a : ℤ) : Chains r a →ₗ[ℤ] Chains r a :=
  Finsupp.linearCombination ℤ fun _ ↦ cell r a 0 ∅

/-- Translation by a lattice vector on cubical chains, leaving directions unchanged.
Source: DAG translation formula
(blueprint: lem-sfb-integral-lattice-cubical-contraction). -/
noncomputable def translate (r : ℕ) (a : ℤ) (w : Fin r → ℤ) :
    Chains r a →ₗ[ℤ] Chains r a :=
  Finsupp.linearCombination ℤ fun c ↦ cell r a (c.1 + w) c.2.val

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
  sorry

end IntegralLatticeCubical
