/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Sheaf.RingTheory.FiniteOverHenselianLocalProduct
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The tame Galois sequence of a henselian discrete valuation field

Source: Stacks Project, Fundamental Groups of Schemes, Tag 0BUB,
`literature/stacks-project/pione.tex`, specialized to a henselian DVR with
algebraically closed residue field; blueprint main-20261015,
`sec-six-functors-basics/sk-prop-a1-kummer/lem-exc-dvr-galois.proof.md`
(blueprint: lem-exc-henselian-dvr-tame-sequence).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace IsDiscreteValuationRing

/-- An excellent henselian DVR with algebraically closed residue field of characteristic `p > 0`
has a closed normal pro-`p` subgroup of its absolute Galois group with tame quotient the product
of the additive `r`-adic integers over all primes `r ≠ p`. The equivalence commutes with the
quotient projection. The identification of the tame quotient may depend on compatible primitive
roots of unity; no canonical trivialization of a Tate twist is asserted. `Multiplicative` changes
only the notation for the additive product's operation and retains its product topology.

Source: Stacks Project, Tag 0BUB, `lemma-structure-decomposition-separable-closure`, and the
blueprint main-20261015 proof of `lem-exc-dvr-galois`.
(blueprint: lem-exc-henselian-dvr-tame-sequence)

Proof:
1. For every finite Galois subfield L of Fsep/F, form the integral closure B_L of R in L.
   `lem-exc-finite-dvr-tame-inertia` gives finiteness and DVR localizations. Apply
   `lem-weil-pbc-finite-over-henselian-local-product`. Delete zero factors; since B_L is a
   nonzero domain, its product decomposition has exactly one nonzero factor (otherwise there
   is a nontrivial idempotent). Thus B_L is local and a DVR. Its residue field is finite over
   the algebraically closed residue field k, hence equals k. Consequently its decomposition,
   inertia and full Galois groups agree. The finite inertia lemma gives a surjection to the
   n_L-th roots of unity, with normal p-group kernel P_L, where e_L = q_L n_L, q_L is a
   p-power, and n_L is prime to p.
2. In a tower M/L/F, the unique maximal ideal of B_M contracts to that of B_L: the quotient
   by its contraction is a finite-dimensional domain over k and hence a field. Apply
   `lem-exc-finite-tame-character-tower` to obtain surjective restrictions on Galois groups
   and wild kernels, and n_L dividing n_M. Replace the character by its q_L-th power. The
   scaled characters then commute with restriction and the power map of exponent n_M/n_L.
   Restriction satisfies identity and composition, as do the power maps since the exponents
   multiply. Finite Galois subfields are nonempty and directed by bottom and compositum;
   these are the instances in `lem-exc-galois-krull-finite-limit`.
3. Choose a uniformizer of R. For each positive m prime to p,
   `lem-exc-tame-root-extension` lifts the roots of unity and gives its m-th-root extension,
   cyclic Galois of degree and ramification index m inside Fsep. Thus the tame indices
   realize every positive integer prime to p.
4. Apply `lem-exc-infinite-tame-inverse-limit` to the finite exact sequences and the
   surjective transitions from step 2. Identify Gal(Fsep/F) with the inverse limit of the
   finite Galois groups by `lem-exc-galois-krull-finite-limit`, namely Mathlib's
   `InfiniteGalois.continuousMulEquivToLimit`. This gives a continuous surjection to the
   root-group limit C with closed normal kernel P, an induced topological quotient
   equivalence, and p-power order for every finite continuous quotient of P.
5. Identify C with the full prime-to-p root limit T. A family z in T maps to its n_L
   coordinates. In the other direction, for each m choose L with m dividing n_L (step 3)
   and take the n_L/m-th power of c_L. A common Galois overfield proves independence of
   this choice and compatibility for m dividing m'. The constructions are inverse: to
   recover c_L choose that L at m = n_L. Every output coordinate is a power of a single
   finite discrete input coordinate, so both homomorphisms are continuous.
6. By `lem-exc-tame-roots-product`, compatible primitive roots and the Chinese remainder
   decomposition give a topological group equivalence from T to the full product of the
   additive r-adic integers for r different from p. Compose the maps and equivalences from
   steps 4 and 5 with it. The kernel, closedness, normality and p-power quotient assertion
   are unchanged. The choice of primitive roots explains the permitted noncanonicity. -/
theorem exists_tame_galois_sequence
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (hR : IsExcellent R) [HenselianLocalRing R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (Fsep : Type w) [Field Fsep] [Algebra F Fsep] [IsSepClosure F Fsep] :
    ∃ (P : Subgroup (Gal(Fsep/F))) (_ : P.Normal),
      IsClosed (P : Set (Gal(Fsep/F))) ∧
      ∃ θ : Gal(Fsep/F) →* Multiplicative
          (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p}, @PadicInt r.1 (Fact.mk r.1.2)),
        Continuous θ ∧ Function.Surjective θ ∧ θ.ker = P ∧
        (∃ e : (Gal(Fsep/F) ⧸ P) ≃ₜ* Multiplicative
            (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p}, @PadicInt r.1 (Fact.mk r.1.2)),
          ∀ g : Gal(Fsep/F), e (QuotientGroup.mk' P g) = θ g) ∧
        ∀ (Q : Type z) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
          (f : P →* Q), Continuous f → Function.Surjective f →
            ∃ n : ℕ, Nat.card Q = p ^ n := by
  sorry

end IsDiscreteValuationRing
