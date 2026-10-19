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
import Sheaf.FieldTheory.CanonicalTraitTameCharacter
import Sheaf.FieldTheory.TameRootsProduct
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.QuotientGroup.Basic

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

namespace TameRoots

private noncomputable def rootEquiv
    {K : Type u} {L : Type v} [Field K] [Field L]
    {n : ℕ} [NeZero n] {ζ : Kˣ} {η : Lˣ}
    (hζ : IsPrimitiveRoot ζ n) (hη : IsPrimitiveRoot η n) :
    rootsOfUnity n K ≃* rootsOfUnity n L :=
  (MulEquiv.subgroupCongr hζ.zpowers_eq.symm).trans
    (hζ.zmodEquivZPowers.symm.toMultiplicativeRight.trans
      (hη.zmodEquivZPowers.toMultiplicativeLeft.trans
        (MulEquiv.subgroupCongr hη.zpowers_eq)))

private theorem rootEquiv_pow
    {K : Type u} {L : Type v} [Field K] [Field L]
    {n : ℕ} [NeZero n] {ζ : Kˣ} {η : Lˣ}
    (hζ : IsPrimitiveRoot ζ n) (hη : IsPrimitiveRoot η n) (a : ℕ) :
    (rootEquiv hζ hη ⟨ζ ^ a, by
      rw [mem_rootsOfUnity, ← pow_mul, mul_comm a, pow_mul, hζ.pow_eq_one, one_pow]⟩ :
      Lˣ) = η ^ a := by
  change (hη.zmodEquivZPowers
    (hζ.zmodEquivZPowers.symm ⟨ζ ^ a, a, zpow_natCast ζ a⟩)).toMul.val = _
  rw [hζ.zmodEquivZPowers_symm_apply_pow', hη.zmodEquivZPowers_apply_coe_nat]
  rfl

private theorem rootEquiv_transition
    {K : Type u} {L : Type v} [Field K] [Field L] {p : ℕ}
    {ζ : Order p → Kˣ} {η : Order p → Lˣ}
    (hζ : IsCompatiblePrimitiveFamily p ζ) (hη : IsCompatiblePrimitiveFamily p η)
    (m n : Order p) (h : m.1 ∣ n.1) (x : rootsOfUnity n.1 K) :
    letI : NeZero m.1 := ⟨m.2.1.ne'⟩
    letI : NeZero n.1 := ⟨n.2.1.ne'⟩
    (rootEquiv (hζ.1 m) (hη.1 m)
      ⟨(x : Kˣ) ^ (n.1 / m.1), by
        rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel h]
        exact (mem_rootsOfUnity _ _).mp x.property⟩ : Lˣ) =
      (rootEquiv (hζ.1 n) (hη.1 n) x : Lˣ) ^ (n.1 / m.1) := by
  let : NeZero m.1 := ⟨m.2.1.ne'⟩
  let : NeZero n.1 := ⟨n.2.1.ne'⟩
  obtain ⟨a, _, ha⟩ := (hζ.1 n).eq_pow_of_mem_rootsOfUnity x.property
  have hm : (x : Kˣ) ^ (n.1 / m.1) = ζ m ^ a := by
    rw [← ha, ← pow_mul, mul_comm a, pow_mul, hζ.2.2 m n h]
  have hn : x = ⟨ζ n ^ a, by
      rw [mem_rootsOfUnity, ← pow_mul, mul_comm a, pow_mul, (hζ.1 n).pow_eq_one,
        one_pow]⟩ := Subtype.ext ha.symm
  rw [hn, rootEquiv_pow]
  have hh : (⟨((ζ n) ^ a) ^ (n.1 / m.1), by
      rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel h, ← pow_mul,
        mul_comm a, pow_mul, (hζ.1 n).pow_eq_one, one_pow]⟩ : rootsOfUnity m.1 K) =
      ⟨ζ m ^ a, by
        rw [mem_rootsOfUnity, ← pow_mul, mul_comm a, pow_mul, (hζ.1 m).pow_eq_one,
          one_pow]⟩ := Subtype.ext (by simpa only [ha] using hm)
  rw [hh, rootEquiv_pow, ← pow_mul, mul_comm a, pow_mul, hη.2.2 m n h]

private noncomputable def rootLimitHom
    {K : Type u} {L : Type v} [Field K] [Field L] {p : ℕ}
    {ζ : Order p → Kˣ} {η : Order p → Lˣ}
    (hζ : IsCompatiblePrimitiveFamily p ζ) (hη : IsCompatiblePrimitiveFamily p η) :
    limitSubgroup K p →* limitSubgroup L p := by
  classical
  let coord (x : limitSubgroup K p) (m : Order p) : rootsOfUnity m.1 K :=
    ⟨x.1 m, x.property.1 m (Set.mem_univ m)⟩
  let e (m : Order p) : rootsOfUnity m.1 K ≃* rootsOfUnity m.1 L :=
    letI : NeZero m.1 := ⟨m.2.1.ne'⟩
    rootEquiv (hζ.1 m) (hη.1 m)
  let val (x : limitSubgroup K p) (m : Order p) : Lˣ := e m (coord x m)
  have mem (x : limitSubgroup K p) : val x ∈ limitSubgroup L p := by
    simp only [limitSubgroup, Subgroup.mem_inf, Subgroup.mem_pi, Set.mem_univ,
      forall_const, Subgroup.mem_iInf, MonoidHom.eqLocus]
    refine ⟨fun m ↦ (e m (coord x m)).property, ?_⟩
    intro m n h
    have hx := x.property
    simp only [limitSubgroup, Subgroup.mem_inf, Subgroup.mem_pi, Set.mem_univ,
      forall_const, Subgroup.mem_iInf, MonoidHom.eqLocus] at hx
    have he := rootEquiv_transition hζ hη m n h (coord x n)
    change val x n ^ (n.1 / m.1) = val x m
    rw [← he]
    congr 2
    exact Subtype.ext (hx.2 m n h)
  exact
    { toFun := fun x ↦ ⟨val x, mem x⟩
      map_one' := by
        apply Subtype.ext
        funext m
        exact congrArg Subtype.val (map_one (e m))
      map_mul' := fun x y ↦ by
        apply Subtype.ext
        funext m
        exact congrArg Subtype.val (map_mul (e m) (coord x m) (coord y m)) }

private theorem rootLimitHom_continuous
    {K : Type u} {L : Type v} [Field K] [Field L] {p : ℕ}
    {ζ : Order p → Kˣ} {η : Order p → Lˣ}
    (hζ : IsCompatiblePrimitiveFamily p ζ) (hη : IsCompatiblePrimitiveFamily p η) :
    @Continuous _ _ (limitTopology K p) (limitTopology L p) (rootLimitHom hζ hη) := by
  classical
  let : TopologicalSpace Kˣ := ⊥
  let : DiscreteTopology Kˣ := ⟨rfl⟩
  let : TopologicalSpace Lˣ := ⊥
  let : DiscreteTopology Lˣ := ⟨rfl⟩
  let : TopologicalSpace (limitSubgroup K p) := limitTopology K p
  let : TopologicalSpace (limitSubgroup L p) := limitTopology L p
  rw [continuous_iInf_rng]
  intro m
  rw [continuous_induced_rng]
  let : NeZero m.1 := ⟨m.2.1.ne'⟩
  let f (x : Kˣ) : Lˣ := if hx : x ∈ rootsOfUnity m.1 K then
    rootEquiv (hζ.1 m) (hη.1 m) ⟨x, hx⟩ else 1
  have hc : Continuous (fun x : limitSubgroup K p ↦ x.1 m) :=
    continuous_iInf_dom (i := m) continuous_induced_dom
  convert (continuous_of_discreteTopology (f := f)).comp hc using 1
  funext x
  change (rootEquiv (hζ.1 m) (hη.1 m) ⟨x.1 m, _⟩ : Lˣ) = f (x.1 m)
  dsimp only [f]
  split_ifs with hx
  · rfl
  · exact False.elim (hx (x.property.1 m (Set.mem_univ m)))

private theorem rootLimitHom_inverse
    {K : Type u} {L : Type v} [Field K] [Field L] {p : ℕ}
    {ζ : Order p → Kˣ} {η : Order p → Lˣ}
    (hζ : IsCompatiblePrimitiveFamily p ζ) (hη : IsCompatiblePrimitiveFamily p η)
    (x : limitSubgroup K p) :
    rootLimitHom hη hζ (rootLimitHom hζ hη x) = x := by
  apply Subtype.ext
  funext m
  let : NeZero m.1 := ⟨m.2.1.ne'⟩
  obtain ⟨a, _, ha⟩ := (hζ.1 m).eq_pow_of_mem_rootsOfUnity
    (x.property.1 m (Set.mem_univ m))
  change (rootEquiv (hη.1 m) (hζ.1 m)
    (rootEquiv (hζ.1 m) (hη.1 m) ⟨x.1 m, _⟩) : Kˣ) = x.1 m
  have hx : (⟨x.1 m, x.property.1 m (Set.mem_univ m)⟩ : rootsOfUnity m.1 K) =
      ⟨ζ m ^ a, by
        rw [mem_rootsOfUnity, ← pow_mul, mul_comm a, pow_mul, (hζ.1 m).pow_eq_one,
          one_pow]⟩ := Subtype.ext ha.symm
  rw [hx]
  have he := rootEquiv_pow (hζ.1 m) (hη.1 m) a
  have he' : rootEquiv (hζ.1 m) (hη.1 m)
      ⟨ζ m ^ a, by
        rw [mem_rootsOfUnity, ← pow_mul, mul_comm a, pow_mul, (hζ.1 m).pow_eq_one,
          one_pow]⟩ = ⟨η m ^ a, by
        rw [mem_rootsOfUnity, ← pow_mul, mul_comm a, pow_mul, (hη.1 m).pow_eq_one,
          one_pow]⟩ := Subtype.ext he
  rw [he', rootEquiv_pow, ha]

private noncomputable def rootLimitEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] {p : ℕ}
    {ζ : Order p → Kˣ} {η : Order p → Lˣ}
    (hζ : IsCompatiblePrimitiveFamily p ζ) (hη : IsCompatiblePrimitiveFamily p η) :
    @ContinuousMulEquiv (limitSubgroup K p) (limitTopology K p)
      (limitSubgroup L p) (limitTopology L p) inferInstance inferInstance := by
  let : TopologicalSpace (limitSubgroup K p) := limitTopology K p
  let : TopologicalSpace (limitSubgroup L p) := limitTopology L p
  exact { rootLimitHom hζ hη with
    invFun := rootLimitHom hη hζ
    left_inv := rootLimitHom_inverse hζ hη
    right_inv := rootLimitHom_inverse hη hζ
    continuous_toFun := rootLimitHom_continuous hζ hη
    continuous_invFun := rootLimitHom_continuous hη hζ }

end TameRoots

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
  classical
  have _excellent : IsExcellent R := hR
  -- The canonical character supplies the finite-level assembly in steps 1--5 above.
  let : IsStrictlyHenselianLocalRing R :=
    (isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed R).mpr
      ⟨inferInstance, inferInstance⟩
  have hp : p = if ringChar (IsLocalRing.ResidueField R) = 0 then 1
      else ringChar (IsLocalRing.ResidueField R) := by
    rw [ringChar.eq (IsLocalRing.ResidueField R) p, if_neg (Fact.out : p.Prime).ne_zero]
  obtain ⟨t, ht, htsurj, _, _, hpro, _, ⟨ζ, hζ⟩, _⟩ :=
    exists_canonical_tame_character R F Fsep (AlgebraicClosure Fsep) p hp
  obtain ⟨⟨η, hη⟩, he⟩ :=
    TameRoots.compatible_roots_product (IsLocalRing.ResidueField R) p
  obtain ⟨c, _⟩ := he η hη
  let : TopologicalSpace (TameRoots.limitSubgroup (AlgebraicClosure Fsep) p) :=
    TameRoots.limitTopology (AlgebraicClosure Fsep) p
  let : TopologicalSpace (TameRoots.limitSubgroup (IsLocalRing.ResidueField R) p) :=
    TameRoots.limitTopology (IsLocalRing.ResidueField R) p
  let b := TameRoots.rootLimitEquiv hζ hη
  let e := b.trans c
  let θ := e.toMonoidHom.comp t
  have hθ : Continuous θ := e.continuous.comp ht
  have hθsurj : Function.Surjective θ := e.surjective.comp htsurj
  have heker : θ.ker = t.ker := by
    ext x
    change e (t x) = 1 ↔ t x = 1
    rw [← map_one e, e.injective.eq_iff]
  let : T2Space (TameRoots.AdicProduct p) := by
    change T2Space (∀ r : {r : Nat.Primes // (r : ℕ) ≠ p},
      @PadicInt r.1 (Fact.mk r.1.2))
    infer_instance
  refine ⟨t.ker, inferInstance, ?_, θ, hθ, hθsurj, heker, ?_, hpro⟩
  · have hc : IsClosed (θ.ker : Set (Gal(Fsep/F))) :=
      isClosed_singleton.preimage hθ
    rwa [heker] at hc
  · let eqv := QuotientGroup.quotientKerEquivOfSurjective θ hθsurj
    let eqv' : (Gal(Fsep/F) ⧸ t.ker) ≃* TameRoots.AdicProduct p :=
      (QuotientGroup.quotientMulEquivOfEq heker.symm).trans eqv
    have heqv : Continuous eqv' := by
      apply (QuotientGroup.isQuotientMap_mk t.ker).continuous_iff.mpr
      exact hθ
    exact ⟨{ (Continuous.homeoOfEquivCompactToT2
      (f := eqv'.toEquiv) heqv) with map_mul' := eqv'.map_mul }, fun _ ↦ rfl⟩

end IsDiscreteValuationRing
