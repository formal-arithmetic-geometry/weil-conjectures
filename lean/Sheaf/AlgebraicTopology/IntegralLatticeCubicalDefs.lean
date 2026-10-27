module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Integral cubical chains of a lattice

Source: Stacks Project, more-algebra.tex, Tags 0623 and 062F, for the algebraic
Koszul ingredients; the signed-coordinate contraction is the agent-written construction
in the DAG proof (blueprint: def-sfb-integral-lattice-cubical-chains).

The terms are free modules on lattice points and subsets of coordinates. Integer degrees
include the zero extension outside degrees zero through the rank. These definitions are
shared by the two coordinate calculations and the total contraction theorem.
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

end IntegralLatticeCubical
