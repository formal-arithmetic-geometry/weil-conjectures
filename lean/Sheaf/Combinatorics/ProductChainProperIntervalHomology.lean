module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.Fin.Basic

import Mathlib.Algebra.Homology.HomologySequence

/-! # Homology of proper intervals in products of finite chains

Source: main-20261015, six-functors basics, direct-images proof paragraph (3),
finite combinatorial input below the rational polynomial-bar calculation
(blueprint: lem-sfb-product-chain-proper-interval-homology).

This is the agent-formulated combinatorial input recorded in the DAG, not an
assertion quoted from the blueprint. The complex is constructed explicitly on
strict-chain bases, including the empty chain. Only proofs are postponed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace ProductChainProperInterval

/-- The coordinatewise interval with its bottom and top removed.
Source: the definition of T_m in the finite combinatorial input below
main-20261015 direct-images paragraph (3)
(blueprint: lem-sfb-product-chain-proper-interval-homology). -/
abbrev ProperInterval {r : ℕ} (m : Fin r → ℕ) :=
  {v : Fin r → ℕ // v ≤ m ∧ v ≠ 0 ∧ v ≠ m}

/-- Strict chains with n vertices; n = 0 gives the unique empty chain.
Source: the basis description of A(m) in the same combinatorial input
(blueprint: lem-sfb-product-chain-proper-interval-homology). -/
abbrev ChainBasis {r : ℕ} (m : Fin r → ℕ) (n : ℕ) :=
  Fin n ↪o ProperInterval m

/-- The rational free module on chains with n vertices, placed in degree n - 1.
Source: the basis and augmentation description of A(m) in the same input
(blueprint: lem-sfb-product-chain-proper-interval-homology). -/
abbrev Chains {r : ℕ} (m : Fin r → ℕ) (n : ℕ) := ChainBasis m n →₀ ℚ

/-- Alternating deletion of a vertex. For n = 0 this sends each vertex to the
empty-chain basis vector with coefficient 1.
Source: the displayed differential of A(m) in the same combinatorial input
(blueprint: lem-sfb-product-chain-proper-interval-homology). -/
def boundary {r : ℕ} (m : Fin r → ℕ) (n : ℕ) :
    Chains m (n + 1) →ₗ[ℚ] Chains m n :=
  Finsupp.linearCombination ℚ fun c ↦
    ∑ a : Fin (n + 1), Finsupp.single (a.succAboveOrderEmb.trans c) ((-1 : ℚ) ^ a.val)

/-- Alternating vertex deletion squares to zero, including the augmentation.
Source: proof step 1 of the finite combinatorial input below
main-20261015 direct-images paragraph (3)
(blueprint: lem-sfb-product-chain-proper-interval-homology).

Proof: expand both boundaries on each strict-chain basis vector. For a < b,
deleting a then the original b and deleting b then a give the same remaining
chain. Their coefficients are (-1)^(a+b-1) and (-1)^(a+b), which cancel.
For a chain with two vertices this is cancellation of the two augmentations.
Linearity extends the calculation to all chains. -/
theorem boundary_squared {r : ℕ} (m : Fin r → ℕ) (n : ℕ) :
    (boundary m n).comp (boundary m (n + 1)) = 0 := by
  sorry

/-- The augmented complex indexed by number of vertices, before shifting indices.
Source: the construction of A(m) in the same combinatorial input
(blueprint: lem-sfb-product-chain-proper-interval-homology). -/
def complexNat {r : ℕ} (m : Fin r → ℕ) : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of ℚ (Chains m n))
    (fun n ↦ ModuleCat.ofHom (boundary m n))
    (fun n ↦ congrArg ModuleCat.ofHom (boundary_squared m n))

/-- Number of vertices n corresponds to homological degree n - 1.
Source: the degree convention of A(m) in the same combinatorial input
(blueprint: lem-sfb-product-chain-proper-interval-homology). -/
def augmentedDegreeEmbedding :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) where
  f n := (n : ℤ) - 1
  injective_f := by
    intro a b h
    change (a : ℤ) - 1 = (b : ℤ) - 1 at h
    omega
  rel := by
    intro a b h
    simp only [ComplexShape.down_Rel] at h ⊢
    omega

/-- A(m), extended by zero below degree -1. Its degree -1 module is free on the
unique empty chain, hence canonically Q. Its degree k >= 0 module is free on
strict chains of k + 1 vertices, and its differential is alternating deletion.
Source: the entire definition of A(m) in the same combinatorial input
(blueprint: lem-sfb-product-chain-proper-interval-homology). -/
def complex {r : ℕ} (m : Fin r → ℕ) : ChainComplex (ModuleCat ℚ) ℤ :=
  (complexNat m).extend augmentedDegreeEmbedding

/-- Reduced rational homology of the proper part of a product of finite chains.
Source: main-20261015 direct-images paragraph (3), finite combinatorial input,
proof steps 1–7 (blueprint: lem-sfb-product-chain-proper-interval-homology).

Proof: alternating deletion squares to zero as above. The strict-chain prism
of lem-sfb-poset-augmented-chain-prism identifies the homology maps of comparable
monotone maps. A constant map factors through a singleton, whose augmented
complex is Q -> Q by the identity and is acyclic, including in degree -1.

If m_j >= 2, the map u(v)_j = max(v_j,1), unchanged in other coordinates,
stays in the proper interval: u(v) = m would force v = m. Both the identity
and the constant map at the j-th unit vector are pointwise below u. The prism
therefore makes the identity on homology zero in every integer degree.

If every coordinate is zero or one, delete zero coordinates to identify the
interval with the nonempty proper subsets of the active set E. Induct on
s = |E| >= 1. For s = 1 the interval is empty and only degree -1 remains.
For s >= 2 choose a in E and delete the coatom v = E minus {a}. The remaining
poset D is acyclic by comparing the identity and the constant {a} with union
with {a}, again using the prism. The quotient of the full augmented complex
by C(D) is the augmented proper-subset complex for v shifted up one degree:
a quotient basis chain ends in v; deleting v vanishes, and other signs agree.
The degree -1 quotient is zero because the augmentation inclusion is the
identity. The long exact homology sequence (lem-weil-pbc-complex-ses-homology-long-exact,
Stacks 0117, with integer grading reversed) identifies the full homology with
that quotient. Induction shifts the unique one-dimensional group from s-3
to s-2. Degrees below -1 vanish by extension by zero. -/
theorem homology {r : ℕ} (m : Fin r → ℕ) (hr : 1 ≤ r) (hm : m ≠ 0) :
    ((∃ i : Fin r, 2 ≤ m i) → ∀ k : ℤ, IsZero ((complex m).homology k)) ∧
    ((∀ i : Fin r, m i = 0 ∨ m i = 1) →
      (∀ k : ℤ, k ≠ ((Finset.univ.filter (fun i : Fin r ↦ m i = 1)).card : ℤ) - 2 →
        IsZero ((complex m).homology k)) ∧
      Module.finrank ℚ ((complex m).homology
        (((Finset.univ.filter (fun i : Fin r ↦ m i = 1)).card : ℤ) - 2)) = 1) := by
  sorry

end ProductChainProperInterval
