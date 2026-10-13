module
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# Detecting nonzero differentials by derivations

Source: Stacks Project, More on Algebra, Tag 07PH (`lemma-find-D`).
(blueprint: lem-weil-pbc-nonzero-differential-to-derivation).
-/

@[expose] public section
set_option autoImplicit false
universe u
/-- A nonzero differential over the prime field is detected by an absolute derivation.
Source: Stacks Project, More on Algebra, Tag 07PH (`lemma-find-D`),
the differential-functional step.
(blueprint: lem-weil-pbc-nonzero-differential-to-derivation).
Proof: the differentials form an M-vector space. By
lem-weil-pbc-vector-space-dual-separates choose an M-linear functional φ
with φ(df) ≠ 0. Compose φ with the universal ZMod p-derivation d;
M-linearity preserves additivity and the Leibniz rule. Restrict this
derivation's scalars from ZMod p to ℤ. Its value at f is still φ(df),
which is nonzero. -/
theorem exists_derivation_of_nonzero_kahler_differential
    (p : ℕ) [Fact p.Prime] (M : Type u) [Field M] [CharP M p] [Algebra (ZMod p) M]
    (f : M) (h : KaehlerDifferential.D (ZMod p) M f ≠ 0) :
    ∃ D : Derivation ℤ M M, D f ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero M h
  exact ⟨(φ.compDer (KaehlerDifferential.D (ZMod p) M)).restrictScalars ℤ, hφ⟩
