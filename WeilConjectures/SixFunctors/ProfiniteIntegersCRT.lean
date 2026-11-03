/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Constructions
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms

/-! # Chinese remainder description and topology of profinite integers

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-smooth-base-change/sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md,
auxiliary profinite-integer construction in the counterexample paragraph; finite CRT:
Stacks Project, Tag 00DT, algebra-lemma-chinese-remainder
(blueprint: lem-sf-profinite-integers-crt).

`ProfiniteIntegers` is the inverse limit of the finite rings `ℤ/nℤ` over the POSITIVE
integers `n`, ordered by divisibility with the reductions `ZMod.castHom` as transition maps,
as the compatible subring of the product with its subspace topology
(def-kun-subspace-topology: `instTopologicalSpaceSubtype`); every `ZMod n` is discrete.
The modulus `0` is excluded: `ZMod 0 = ℤ` and every positive integer divides `0`, so
including it would collapse the limit to the discrete ring `ℤ`.
`PadicIntAt p` is Mathlib's `ℤ_[p]` (def-weil-l-adic-numbers) for a prime `p : Nat.Primes`.
-/

@[expose] public section

set_option autoImplicit false

/-- Compatibility of a family of residues modulo all positive integers: for `n ∣ m`, the
reduction of the `m`-th residue is the `n`-th residue.
Source: sk-rem-sf-fullcd-scope.md, counterexample paragraph, auxiliary profinite integers
(blueprint: lem-sf-profinite-integers-crt). -/
def profiniteIntegerCompatible (a : ∀ n : {n : ℕ // 0 < n}, ZMod n.1) : Prop :=
  ∀ ⦃n m : {n : ℕ // 0 < n}⦄ (h : n.1 ∣ m.1),
    ZMod.castHom h (ZMod n.1) (a m) = a n

/-- The inverse-limit subring of the finite rings `ℤ/nℤ`, `n ≥ 1`, over divisibility.
Source: sk-rem-sf-fullcd-scope.md, counterexample paragraph, auxiliary profinite integers
(blueprint: lem-sf-profinite-integers-crt). -/
def profiniteIntegersSubring : Subring (∀ n : {n : ℕ // 0 < n}, ZMod n.1) where
  carrier := {a | profiniteIntegerCompatible a}
  zero_mem' := by
    intro n m h
    simp
  neg_mem' := by
    intro a ha n m h
    change (ZMod.castHom h (ZMod n.1)) (-a m) = -a n
    rw [map_neg]
    exact congrArg Neg.neg (ha h)
  add_mem' := by
    intro a b ha hb n m h
    change (ZMod.castHom h (ZMod n.1)) (a m + b m) = a n + b n
    rw [map_add]
    exact congrArg₂ (· + ·) (ha h) (hb h)
  mul_mem' := by
    intro a b ha hb n m h
    change (ZMod.castHom h (ZMod n.1)) (a m * b m) = a n * b n
    rw [map_mul]
    exact congrArg₂ (· * ·) (ha h) (hb h)
  one_mem' := by
    intro n m h
    simpa using (ZMod.castHom h (ZMod n.1)).map_one

/-- Profinite integers `Ẑ = lim_{n ≥ 1} ℤ/nℤ` as the compatible families, with the subring
structure and the subspace topology of the product of the discrete rings `ZMod n`.
Source: sk-rem-sf-fullcd-scope.md, counterexample paragraph, auxiliary profinite integers
(blueprint: lem-sf-profinite-integers-crt). -/
abbrev ProfiniteIntegers : Type := profiniteIntegersSubring

/-- The `p`-adic integer ring `ℤ_[p]` indexed by a prime subtype, with its canonical prime
instance (def-weil-l-adic-numbers).
Source: sk-rem-sf-fullcd-scope.md, counterexample paragraph, auxiliary profinite integers
(blueprint: lem-sf-profinite-integers-crt). -/
def PadicIntAt (p : Nat.Primes) := @PadicInt (p : ℕ) ⟨p.2⟩

noncomputable section

/-- The ring structure of `ℤ_[p]` (blueprint: lem-sf-profinite-integers-crt). -/
instance (p : Nat.Primes) : CommRing (PadicIntAt p) :=
  @PadicInt.instCommRing (p : ℕ) ⟨p.2⟩
/-- The metric of `ℤ_[p]` (blueprint: lem-sf-profinite-integers-crt). -/
instance (p : Nat.Primes) : MetricSpace (PadicIntAt p) :=
  @PadicInt.instMetricSpace (p : ℕ) ⟨p.2⟩
/-- The metric topology of `ℤ_[p]` (blueprint: lem-sf-profinite-integers-crt). -/
instance (p : Nat.Primes) : TopologicalSpace (PadicIntAt p) := inferInstance

open Topology

private abbrev PositiveModulus := {n : ℕ // 0 < n}
private abbrev AdicCoordinates := ∀ p : Nat.Primes, PadicIntAt p

private lemma crt_cast_cast {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) (x : ZMod c) :
    ZMod.castHom hab (ZMod a) (ZMod.castHom hbc (ZMod b) x) =
      ZMod.castHom (dvd_trans hab hbc) (ZMod a) x :=
  RingHom.congr_fun (ZMod.castHom_comp hab hbc) x

private def crtPrime (m : PositiveModulus) (q : m.1.primeFactors) : Nat.Primes :=
  ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩

private noncomputable def crtCoordinate (m : PositiveModulus) :
    AdicCoordinates →+* ZMod m.1 :=
  (ZMod.equivPi m.1 m.2.ne').symm.toRingHom.comp
    (RingHom.pi fun q : m.1.primeFactors ↦
      (@PadicInt.toZModPow q.1 ⟨Nat.prime_of_mem_primeFactors q.2⟩
        (m.1.factorization q.1)).comp (Pi.evalRingHom _ (crtPrime m q)))

private lemma crtCoordinate_factor (m : PositiveModulus) (x : AdicCoordinates)
    (q : m.1.primeFactors) :
    ZMod.castHom (Nat.ordProj_dvd m.1 q.1) (ZMod (q.1 ^ m.1.factorization q.1))
      (crtCoordinate m x) =
        @PadicInt.toZModPow q.1 ⟨Nat.prime_of_mem_primeFactors q.2⟩
          (m.1.factorization q.1) (x (crtPrime m q)) := by
  have he : (Pi.evalRingHom _ q).comp (ZMod.equivPi m.1 m.2.ne').toRingHom =
      ZMod.castHom (Nat.ordProj_dvd m.1 q.1) (ZMod (q.1 ^ m.1.factorization q.1)) :=
    Subsingleton.elim _ _
  rw [← he]
  exact congrFun ((ZMod.equivPi m.1 m.2.ne').apply_symm_apply _) q

private lemma crtCoordinate_spec (m : PositiveModulus) (x : AdicCoordinates)
    (p : Nat.Primes) (a : ℕ) (h : p.1 ^ a ∣ m.1) :
    ZMod.castHom h (ZMod (p.1 ^ a)) (crtCoordinate m x) =
      @PadicInt.toZModPow p.1 ⟨p.2⟩ a (x p) := by
  let : Fact p.1.Prime := ⟨p.2⟩
  by_cases ha : a = 0
  · subst a
    change (ZMod.castHom h (ZMod 1)) (crtCoordinate m x) = _
    exact Subsingleton.elim _ _
  have hp : p.1 ∣ m.1 := dvd_trans (dvd_pow_self _ ha) h
  let q : m.1.primeFactors := ⟨p.1, Nat.mem_primeFactors.mpr ⟨p.2, hp, m.2.ne'⟩⟩
  have hab : a ≤ m.1.factorization p.1 :=
    (p.2.pow_dvd_iff_le_factorization m.2.ne').mp h
  calc
    _ = ZMod.castHom (pow_dvd_pow p.1 hab) _
        (ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _ (crtCoordinate m x)) :=
      (crt_cast_cast _ _ _).symm
    _ = _ := by
      rw [crtCoordinate_factor m x q]
      exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow a _ hab) (x p)

private lemma crtCoordinate_compat (m n : PositiveModulus) (h : m.1 ∣ n.1)
    (x : AdicCoordinates) :
    ZMod.castHom h (ZMod m.1) (crtCoordinate n x) = crtCoordinate m x := by
  apply (ZMod.equivPi m.1 m.2.ne').injective
  funext q
  have he (z : ZMod m.1) : ZMod.equivPi m.1 m.2.ne' z q =
      ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _ z :=
    RingHom.congr_fun
      (Subsingleton.elim ((Pi.evalRingHom _ q).comp
        (ZMod.equivPi m.1 m.2.ne').toRingHom)
        (ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _)) z
  rw [he, he, crt_cast_cast, crtCoordinate_factor]
  exact crtCoordinate_spec n x (crtPrime m q) (m.1.factorization q.1)
    (dvd_trans (Nat.ordProj_dvd m.1 q.1) h)

private noncomputable def crtReconstruct : AdicCoordinates →+* ProfiniteIntegers where
  toFun x := ⟨fun m ↦ crtCoordinate m x, fun {_ _} h ↦ crtCoordinate_compat _ _ h x⟩
  map_one' := Subtype.ext (funext fun m ↦ map_one (crtCoordinate m))
  map_zero' := Subtype.ext (funext fun m ↦ map_zero (crtCoordinate m))
  map_add' x y := Subtype.ext (funext fun m ↦ map_add (crtCoordinate m) x y)
  map_mul' x y := Subtype.ext (funext fun m ↦ map_mul (crtCoordinate m) x y)

private def crtPower (p : Nat.Primes) (a : ℕ) : PositiveModulus :=
  ⟨p.1 ^ a, pow_pos p.2.pos _⟩

private def crtProjection (p : Nat.Primes) (a : ℕ) :
    ProfiniteIntegers →+* ZMod (p.1 ^ a) :=
  (Pi.evalRingHom _ (crtPower p a)).comp profiniteIntegersSubring.subtype

private lemma crtProjection_compat (p : Nat.Primes) (a b : ℕ) (h : a ≤ b) :
    (ZMod.castHom (pow_dvd_pow p.1 h) _).comp (crtProjection p b) =
      crtProjection p a := by
  ext x
  exact x.2 (n := crtPower p a) (m := crtPower p b) (pow_dvd_pow p.1 h)

private noncomputable def crtRestrict : ProfiniteIntegers →+* AdicCoordinates :=
  RingHom.pi fun p ↦
    @PadicInt.lift _ _ p.1 (crtProjection p) ⟨p.2⟩ (crtProjection_compat p)

private lemma crtRestrict_spec (x : ProfiniteIntegers) (p : Nat.Primes) (a : ℕ) :
    @PadicInt.toZModPow p.1 ⟨p.2⟩ a (crtRestrict x p) = x.1 (crtPower p a) :=
  RingHom.congr_fun (@PadicInt.lift_spec _ _ p.1 (crtProjection p) ⟨p.2⟩
    (crtProjection_compat p) a) x

private lemma crtReconstruct_restrict (x : ProfiniteIntegers) :
    crtReconstruct (crtRestrict x) = x := by
  apply Subtype.ext
  funext m
  apply (ZMod.equivPi m.1 m.2.ne').injective
  funext q
  have he (z : ZMod m.1) : ZMod.equivPi m.1 m.2.ne' z q =
      ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _ z :=
    RingHom.congr_fun
      (Subsingleton.elim ((Pi.evalRingHom _ q).comp
        (ZMod.equivPi m.1 m.2.ne').toRingHom)
        (ZMod.castHom (Nat.ordProj_dvd m.1 q.1) _)) z
  change ZMod.equivPi m.1 m.2.ne' (crtCoordinate m (crtRestrict x)) q = _
  rw [he, crtCoordinate_factor, he]
  change @PadicInt.toZModPow (crtPrime m q).1 ⟨(crtPrime m q).2⟩
    (m.1.factorization q.1) (crtRestrict x (crtPrime m q)) = _
  rw [crtRestrict_spec]
  exact (x.2 (Nat.ordProj_dvd m.1 q.1)).symm

private lemma crtRestrict_reconstruct (x : AdicCoordinates) :
    crtRestrict (crtReconstruct x) = x := by
  funext p
  let : Fact p.1.Prime := ⟨p.2⟩
  apply PadicInt.ext_of_toZModPow.mp
  intro a
  rw [crtRestrict_spec]
  have h := crtCoordinate_spec (crtPower p a) x p a dvd_rfl
  change crtCoordinate (crtPower p a) x = _
  change ZMod.castHom (dvd_refl (p.1 ^ a)) _ _ = _ at h
  simpa only [ZMod.castHom_self, RingHom.id_apply] using h

private lemma crtCoordinate_continuous (m : PositiveModulus) :
    Continuous (crtCoordinate m) := by
  classical
  let : NeZero m.1 := ⟨m.2.ne'⟩
  have hc : Continuous (fun x : AdicCoordinates ↦ fun q : m.1.primeFactors ↦
      @PadicInt.toZModPow q.1 ⟨Nat.prime_of_mem_primeFactors q.2⟩
        (m.1.factorization q.1) (x (crtPrime m q))) := by
    apply continuous_pi
    intro q
    let : Fact q.1.Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
    exact (PadicInt.continuous_toZModPow _).comp (continuous_apply (crtPrime m q))
  have hd : Continuous (fun z : ∀ q : m.1.primeFactors,
      ZMod (q.1 ^ m.1.factorization q.1) ↦
      (ZMod.equivPi m.1 m.2.ne').symm z) := continuous_of_discreteTopology
  exact hd.comp hc

private lemma crtReconstruct_continuous : Continuous crtReconstruct :=
  (continuous_pi crtCoordinate_continuous).subtype_mk _

private def crtDiagonal : ℤ →+* ProfiniteIntegers :=
  { toFun := fun m ↦ ⟨fun n ↦ (m : ZMod n.1), by
      intro n k h
      exact map_intCast (ZMod.castHom h (ZMod n.1)) m⟩
    map_one' := Subtype.ext (funext fun _ ↦ Int.cast_one)
    map_zero' := Subtype.ext (funext fun _ ↦ Int.cast_zero)
    map_add' m n := Subtype.ext (funext fun _ ↦ Int.cast_add m n)
    map_mul' m n := Subtype.ext (funext fun _ ↦ Int.cast_mul m n) }

private lemma crtDiagonal_dense : Dense (Set.range crtDiagonal) := by
  classical
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨x, hx⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨s, u, hu, hsub⟩ := isOpen_pi_iff.mp hV x.1 hx
  let N : PositiveModulus := ⟨∏ n ∈ s, n.1, Finset.prod_pos (fun n _ ↦ n.2)⟩
  let : NeZero N.1 := ⟨N.2.ne'⟩
  let m : ℤ := (x.1 N).val
  refine ⟨crtDiagonal m, hsub ?_, ⟨m, rfl⟩⟩
  intro n hn
  have hd : n.1 ∣ N.1 := Finset.dvd_prod_of_mem (fun n : PositiveModulus ↦ n.1) hn
  have he : (crtDiagonal m).1 n = x.1 n := by
    change (((x.1 N).val : ℤ) : ZMod n.1) = x.1 n
    rw [Int.cast_natCast]
    calc
      _ = ZMod.castHom hd (ZMod n.1) (x.1 N) := by
        conv_rhs => rw [← ZMod.natCast_zmod_val (x.1 N), map_natCast]
      _ = _ := x.2 hd
  rw [he]
  exact (hu n hn).2

private lemma padicResidue_range (p : ℕ) [Fact p.Prime] :
    Set.range (fun (x : ℤ_[p]) (k : ℕ) ↦ PadicInt.toZModPow k x) =
      {b : ∀ k : ℕ, ZMod (p ^ k) | ∀ ⦃i k : ℕ⦄ (h : i ≤ k),
        ZMod.castHom (Nat.pow_dvd_pow p h) (ZMod (p ^ i)) (b k) = b i} := by
  ext b
  constructor
  · rintro ⟨x, rfl⟩ i k h
    exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow i k h) x
  · intro hb
    refine ⟨PadicInt.ofCompatible b (fun k ↦ hb (Nat.le_succ k)), ?_⟩
    funext k
    exact PadicInt.toZModPow_ofCompatible b _ k

private lemma padicPower_range (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Set.range (fun x : ℤ_[p] ↦ (p : ℤ_[p]) ^ k * x) =
      (PadicInt.toZModPow k) ⁻¹' {0} := by
  ext x
  rw [Set.mem_preimage, Set.mem_singleton_iff, ← RingHom.mem_ker,
    PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  simp only [Set.mem_range, dvd_def, eq_comm]

private lemma padicPower_open (p : ℕ) [Fact p.Prime] (k : ℕ) :
    IsOpen (Set.range (fun x : ℤ_[p] ↦ (p : ℤ_[p]) ^ k * x)) := by
  rw [padicPower_range]
  exact (isOpen_discrete _).preimage (PadicInt.continuous_toZModPow k)

private lemma padicPower_basis (p : ℕ) [Fact p.Prime] (U : Set ℤ_[p])
    (hU : U ∈ nhds 0) :
    ∃ k : ℕ, Set.range (fun x : ℤ_[p] ↦ (p : ℤ_[p]) ^ k * x) ⊆ U := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  refine ⟨k, fun x hx ↦ hsub ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  apply lt_of_le_of_lt _ hk
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  rcases hx with ⟨y, rfl⟩
  exact dvd_mul_right _ _

/-- Chinese-remainder description and topology of the profinite integers.
There is a ring isomorphism `Θ : Ẑ ≃ ∏_p ℤ_p` whose `p`-coordinate of `a` has residue
`a_{p^k}` modulo `p^k` for every `k`; it is a homeomorphism; the diagonal `j : ℤ → Ẑ`,
`j(m) = (m mod n)_n`, satisfies `Θ(j m) = (m)_p` and has dense range. For each prime `p`,
`ℤ_p` is compact Hausdorff; the residue maps `toZModPow k` are continuous and surjective
with kernel `p^k ℤ_p` (so `ℤ_p/p^kℤ_p ≅ ℤ/p^k`); together they embed `ℤ_p`
topologically onto the compatible families in `∏_k ℤ/p^k` (the inverse limit); and the
open subgroups `p^k ℤ_p` form a neighbourhood basis of zero.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md, counterexample paragraph
(pro-r part of the closed procyclic subgroup); Stacks Project, Tag 00DT,
algebra-lemma-chinese-remainder (1).

Proof (the node's steps):
1. Mathlib's `PadicInt.compactSpace` gives compactness directly; the metric gives
   Hausdorffness.
2. The continuous residues are surjective by integer representatives. Their kernels
   are the principal ideals `(p^k)`, hence these ideals are open. The norm description
   and `exists_pow_neg_lt` put one such ideal inside every neighbourhood of zero.
3. The joint residue map is continuous and injective, hence a closed embedding from
   the compact source into the Hausdorff product. `PadicInt.ofCompatible` realizes
   every compatible family and proves the claimed range equality.
4. `PadicInt.lift` constructs the prime coordinates of a compatible all-moduli family.
   In the other direction, `ZMod.equivPi` reconstructs the residue at every positive
   modulus from the finitely many residues at its prime-power factors.
5. Finite CRT injectivity proves compatibility of the reconstructed residues and one
   inverse identity; separation by p-adic residues proves the other. These give the
   ring equivalence and, by residue separation, its value on diagonal integers.
6. Each reconstructed residue is continuous, as a finite CRT combination of continuous
   p-adic residues. The reconstruction map is a continuous bijection from a compact
   product to a Hausdorff subtype; its inverse is continuous as well.
7. A basic open fixes finitely many moduli. Their positive product is a common multiple,
   and an integer representative at that product agrees at every required coordinate.
   This proves density, including the empty set of required moduli.
(blueprint: lem-sf-profinite-integers-crt). -/
theorem profinite_integers_crt :
    ∃ (Θ : ProfiniteIntegers ≃+* (∀ p : Nat.Primes, PadicIntAt p)),
      (∀ (a : ProfiniteIntegers) (p : Nat.Primes) (k : ℕ),
        (@PadicInt.toZModPow (p : ℕ) ⟨p.2⟩ k) (Θ a p) =
          a.1 ⟨(p : ℕ) ^ k, pow_pos p.2.pos k⟩) ∧
      Continuous Θ ∧ Continuous Θ.symm ∧
      (∃ (j : ℤ →+* ProfiniteIntegers),
        (∀ (m : ℤ) (n : {n : ℕ // 0 < n}), (j m).1 n = (m : ZMod n.1)) ∧
        (∀ (m : ℤ) (p : Nat.Primes), Θ (j m) p = (m : PadicIntAt p)) ∧
        Dense (Set.range j)) ∧
      (∀ (p : Nat.Primes), IsCompact (Set.univ : Set (PadicIntAt p)) ∧
        T2Space (PadicIntAt p) ∧
        (∀ k : ℕ, Continuous (@PadicInt.toZModPow (p : ℕ) ⟨p.2⟩ k)) ∧
        (∀ k : ℕ, Function.Surjective (@PadicInt.toZModPow (p : ℕ) ⟨p.2⟩ k)) ∧
        (∀ k : ℕ, RingHom.ker (@PadicInt.toZModPow (p : ℕ) ⟨p.2⟩ k) =
          Ideal.span ({(p : PadicIntAt p) ^ k} : Set (PadicIntAt p))) ∧
        Topology.IsEmbedding
          (fun (x : PadicIntAt p) (k : ℕ) => @PadicInt.toZModPow (p : ℕ) ⟨p.2⟩ k x) ∧
        Set.range
            (fun (x : PadicIntAt p) (k : ℕ) => @PadicInt.toZModPow (p : ℕ) ⟨p.2⟩ k x) =
          {b : ∀ k : ℕ, ZMod ((p : ℕ) ^ k) | ∀ ⦃i k : ℕ⦄ (h : i ≤ k),
            ZMod.castHom (Nat.pow_dvd_pow (p : ℕ) h) (ZMod ((p : ℕ) ^ i)) (b k) = b i} ∧
        (∀ k : ℕ, IsOpen
          (Set.range (fun x : PadicIntAt p => (p : PadicIntAt p) ^ k * x))) ∧
        (∀ U : Set (PadicIntAt p), U ∈ nhds 0 →
          ∃ k : ℕ, Set.range
            (fun x : PadicIntAt p => (p : PadicIntAt p) ^ k * x) ⊆ U)) := by
  classical
  let : ∀ p : Nat.Primes, CompactSpace (PadicIntAt p) :=
    fun p ↦ @PadicInt.compactSpace p.1 ⟨p.2⟩
  let : ∀ p : Nat.Primes, T2Space (PadicIntAt p) := fun _ ↦ inferInstance
  let : ∀ n : PositiveModulus, NeZero n.1 := fun n ↦ ⟨n.2.ne'⟩
  let e : AdicCoordinates ≃+* ProfiniteIntegers :=
    RingEquiv.ofBijective crtReconstruct
      ⟨Function.HasLeftInverse.injective ⟨crtRestrict, crtRestrict_reconstruct⟩,
        Function.HasRightInverse.surjective ⟨crtRestrict, crtReconstruct_restrict⟩⟩
  have hc : Continuous e := crtReconstruct_continuous
  have hci : Continuous e.symm :=
    (e.toEquiv.toHomeomorphOfContinuousClosed hc hc.isClosedMap).symm.continuous
  have hres (a : ProfiniteIntegers) (p : Nat.Primes) (k : ℕ) :
      @PadicInt.toZModPow p.1 ⟨p.2⟩ k (e.symm a p) = a.1 (crtPower p k) := by
    have he : e.symm a = crtRestrict a := by
      apply e.injective
      exact (e.apply_symm_apply a).trans (crtReconstruct_restrict a).symm
    rw [he]
    exact crtRestrict_spec a p k
  refine ⟨e.symm, hres, hci, hc, ⟨crtDiagonal, fun _ _ ↦ rfl, ?_, crtDiagonal_dense⟩,
    ?_⟩
  · intro m p
    let : Fact p.1.Prime := ⟨p.2⟩
    apply PadicInt.ext_of_toZModPow.mp
    intro k
    rw [hres]
    exact (map_intCast (PadicInt.toZModPow k) m).symm
  · intro p
    let : Fact p.1.Prime := ⟨p.2⟩
    refine ⟨isCompact_univ, inferInstance, PadicInt.continuous_toZModPow,
      fun k ↦ ZMod.ringHom_surjective (PadicInt.toZModPow k), PadicInt.ker_toZModPow,
      ?_, padicResidue_range p.1, padicPower_open p.1, padicPower_basis p.1⟩
    exact (continuous_pi PadicInt.continuous_toZModPow).isClosedEmbedding
      (fun x y h ↦ PadicInt.ext_of_toZModPow.mp (congrFun h)) |>.isEmbedding

end
