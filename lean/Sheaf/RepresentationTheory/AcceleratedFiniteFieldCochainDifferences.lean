/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.RepresentationTheory.ContinuousCochainFiniteIndexTransfer
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Sheaf.NumberTheory.Padics.NormOneFiniteSubfieldProjection
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Compactness.Compact

/-! # Accelerated finite-field cochain differences

Source: latest Weil blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated scalar analytic input, formerly steps 7--10 of parameter-cochain
completion-boundary descent; exact literature reference WANTED
(blueprint: lem-sfb-accelerated-finite-field-cochain-differences).

The degree `n + 2` covers exactly the degrees at least two. All coefficient inclusions
are the actual intermediate-field and completion inclusions. The displayed cochains
are existentially bound together with equations uniquely specifying their values.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

open scoped BigOperators
open Filter UniformSpace

namespace ContinuousCohomology

/-- The existing inhomogeneous differential specialized to the trivial scalar action.
This is an abbreviation, including the zero differential in degree zero.
Source: latest blueprint, direct-images proof (3), scalar analytic input
(blueprint: lem-sfb-accelerated-finite-field-cochain-differences). -/
abbrev acceleratedTrivialD (E : Type u) [NormedField E]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (r : ℕ) :=
  continuousInhomogeneousD (TopRep.of (ContRepresentation.trivial E G E))
    continuous_snd r

/-- View a continuous cochain in the actual norm completion by its canonical inclusion.
Source: latest blueprint, direct-images proof (3), scalar analytic input
(blueprint: lem-sfb-accelerated-finite-field-cochain-differences). -/
def acceleratedCompletionCochain {X : Type x} [TopologicalSpace X]
    {Ω : Type u} [NormedField Ω] (h : C(X, Ω)) : C(X, Completion Ω) :=
  ⟨fun a ↦ (h a : Completion Ω), (Completion.continuous_coe Ω).comp h.continuous⟩

/-- View a finite-field-valued continuous cochain in the ambient algebraic closure.
Source: latest blueprint, direct-images proof (3), scalar analytic input
(blueprint: lem-sfb-accelerated-finite-field-cochain-differences). -/
def acceleratedFieldCochain {l : ℕ} [Fact l.Prime]
    {Ω : Type u} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
    {X : Type x} [TopologicalSpace X] (F : IntermediateField ℚ_[l] Ω)
    (h : C(X, F)) : C(X, Ω) :=
  ⟨fun a ↦ (h a : Ω), continuous_subtype_val.comp h.continuous⟩

/-- The finite maximum `D_t = max(1,C_1,...,C_t)`; index zero of `C` is unused.
Source: latest blueprint, direct-images proof (3), scalar analytic input
(blueprint: lem-sfb-accelerated-finite-field-cochain-differences). -/
def acceleratedLoss (C : ℕ+ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => max (acceleratedLoss C t) (C ⟨t + 1, Nat.succ_pos t⟩)

/-- The prescribed positive approximation tolerance `2⁻ⁱ / D_(i+1)`.
Source: latest blueprint, direct-images proof (3), scalar analytic input
(blueprint: lem-sfb-accelerated-finite-field-cochain-differences). -/
noncomputable def acceleratedTolerance (C : ℕ+ → ℝ) (i : ℕ) : ℝ :=
  (2 : ℝ)⁻¹ ^ i / acceleratedLoss C (i + 1)

/-- Contractive projections admit simultaneous accelerated approximation of an algebraic
cocycle and its completed primitive, with pointwise finite cocycle differences.
Source: latest blueprint, direct-images proof (3), agent scalar analytic expansion,
formerly parameter-cochain completion-boundary descent steps 7--10; reference WANTED
(blueprint: lem-sfb-accelerated-finite-field-cochain-differences).

Proof:
1. Apply lem-sfb-norm-one-finite-subfield-projection to each F_N. Its norm extends that
   of Q_l, and finite dimensionality gives completeness by
   lem-weil-l-adic-extension-complete. The isometric inclusion of Omega has dense image
   in its completion B (lem-sfb-normed-field-completion). Multiplicativity gives the
   normed Q_l-vector-space structures on B and F_N. Apply
   lem-sfb-dense-subspace-contractive-extension to extend each projection to Q_N on B.
   It still fixes F_N. Pass the ultrametric inequality from Omega to B by density.
2. The domains S times G^r are compact by
   lem-weil-pbc-tychonoff-product-quasi-compact. For either cochain and epsilon > 0,
   cover its compact domain by inverse images of epsilon-balls centered in Omega.
   A finite subcover has all centers in one F_M. For N >= M, contractivity and fixing
   the centers give |Q_N h(x)-h(x)| <= |h(x)-a| < epsilon. The same finite cover bounds
   the suprema, and the larger of the two indices works for both z and b.
3. D_t >= 1, so delta_i > 0. Recursively choose L_0 above the first approximation
   threshold and N_1, and L_i above its threshold, L_(i-1)+1, i and N_1,...,N_(i+1).
   These choices give strict increase, domination and both error bounds.
4. Differences lie in F_(L_i) by monotonicity of the fields and are continuous.
   The differential is a finite sum of signed evaluations, so it commutes with the
   Q_l-linear coefficient maps. Thus de_i = 0 and dc_i = e_i by dz = 0 and db = z.
5. For i >= 1, write each difference as the difference of its two approximation
   errors. Ultrametricity bounds its norm by max(delta_i,delta_(i-1)), bounded by
   2^(-(i-1))/D_i. Finite telescoping gives sum_(h<=i) e_h = P_i z. Since delta_i
   <= 2^(-i) tends to zero, these partial sums converge uniformly in Omega.
6. A fixed z(s,y) belongs to some F_M. For i >= M+1, both consecutive projections
   fix it, proving eventual vanishing. If j <= i and a homogeneous value is in F_(N_j),
   both L_(i-1) and L_i dominate N_j, so both projections fix that value on any given
   subset R. Their difference is zero there. This does not apply to b outside Omega:
   no eventual vanishing of c_i and no retraction B to Omega is asserted.
-/
theorem exists_acceleratedFiniteFieldCochainDifferences
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] [IsUltrametricDist Ω]
    (F : ℕ → IntermediateField ℚ_[l] Ω) (hF : Monotone F)
    [∀ N : ℕ, FiniteDimensional ℚ_[l] (F N)] (hcover : ∀ a : Ω, ∃ N, a ∈ F N)
    (S : Type w) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [TotallyDisconnectedSpace S] [Nonempty S]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (n : ℕ) (z : C(S × (Fin (n + 2) → G), Ω))
    (hz : ∀ s : S, acceleratedTrivialD Ω G (n + 2) (z.curry s) = 0)
    (b : C(S × (Fin (n + 1) → G), Completion Ω))
    (hb : ∀ (s : S) (g : Fin (n + 2) → G),
      acceleratedTrivialD (Completion Ω) G (n + 1) (b.curry s) g =
        (z (s, g) : Completion Ω))
    (N : ℕ+ → ℕ) (C : ℕ+ → ℝ) (hC : ∀ j : ℕ+, 1 ≤ C j) :
    ∃ (Q : ∀ k : ℕ, Completion Ω →L[ℚ_[l]] F k) (L : ℕ → ℕ)
      (pz : ∀ i : ℕ, C(S × (Fin (n + 2) → G), F (L i)))
      (pb : ∀ i : ℕ, C(S × (Fin (n + 1) → G), F (L i)))
      (e : ∀ i : ℕ, C(S × (Fin (n + 2) → G), F (L i)))
      (c : ∀ i : ℕ, C(S × (Fin (n + 1) → G), F (L i))),
      (∀ (k : ℕ) (a : F k), Q k ((a : Ω) : Completion Ω) = a) ∧
      (∀ (k : ℕ) (a : Completion Ω), ‖Q k a‖ ≤ ‖a‖) ∧
      StrictMono L ∧ (∀ i : ℕ, i ≤ L i) ∧
      (∀ (i : ℕ) (j : ℕ+), (j : ℕ) ≤ i + 1 → N j ≤ L i) ∧
      (∀ (i : ℕ) (a : S × (Fin (n + 2) → G)),
        pz i a = Q (L i) (z a : Completion Ω)) ∧
      (∀ (i : ℕ) (a : S × (Fin (n + 1) → G)), pb i a = Q (L i) (b a)) ∧
      (∀ i : ℕ, ‖acceleratedFieldCochain (F (L i)) (pz i) - z‖ ≤
        acceleratedTolerance C i) ∧
      (∀ i : ℕ, ‖acceleratedCompletionCochain (acceleratedFieldCochain (F (L i))
        (pb i)) - b‖ ≤ acceleratedTolerance C i) ∧
      (∀ (i : ℕ) (a : S × (Fin (n + 2) → G)),
        (e i a : Ω) = (pz i a : Ω) - if i = 0 then 0 else (pz (i - 1) a : Ω)) ∧
      (∀ (i : ℕ) (a : S × (Fin (n + 1) → G)),
        ((c i a : Ω) : Completion Ω) = ((pb i a : Ω) : Completion Ω) -
          if i = 0 then 0 else ((pb (i - 1) a : Ω) : Completion Ω)) ∧
      (∀ (i : ℕ) (s : S), acceleratedTrivialD (F (L i)) G (n + 2)
        ((e i).curry s) = 0) ∧
      (∀ (i : ℕ) (s : S), acceleratedTrivialD (F (L i)) G (n + 1)
        ((c i).curry s) = (e i).curry s) ∧
      (∀ (i : ℕ) (a : S × (Fin (n + 2) → G)),
        (∑ k ∈ Finset.range (i + 1), (e k a : Ω)) = (pz i a : Ω)) ∧
      TendstoUniformly (fun i a ↦ ∑ k ∈ Finset.range (i + 1), (e k a : Ω)) z atTop ∧
      (∀ i : ℕ, 1 ≤ i →
        ‖e i‖ ≤ max (acceleratedTolerance C i) (acceleratedTolerance C (i - 1)) ∧
        ‖c i‖ ≤ max (acceleratedTolerance C i) (acceleratedTolerance C (i - 1)) ∧
        max (acceleratedTolerance C i) (acceleratedTolerance C (i - 1)) ≤
          (2 : ℝ)⁻¹ ^ (i - 1) / acceleratedLoss C i) ∧
      (∀ a : S × (Fin (n + 2) → G), ∀ᶠ i : ℕ in atTop, e i a = 0) ∧
      ∀ (i : ℕ) (j : ℕ+) (s : S) (R : Set (Fin (n + 3) → G)), (j : ℕ) ≤ i →
        (∀ g ∈ R, z (s, fun q ↦ (g q.castSucc)⁻¹ * g q.succ) ∈ F (N j)) →
        ∀ g ∈ R, e i (s, fun q ↦ (g q.castSucc)⁻¹ * g q.succ) = 0 := by
  sorry

end ContinuousCohomology
