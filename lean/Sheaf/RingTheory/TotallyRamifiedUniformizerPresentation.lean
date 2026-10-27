module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.RingTheory.AdjoinRoot

/-!
# Uniformizer presentations of totally ramified extensions

Source: Stacks Project, More on Algebra, Tag 09ER,
`lemma-weakly-unramified-goes-up-along-totally-ramified`, first proof paragraph
(blueprint: lem-sfb-totally-ramified-uniformizer-presentation).

The two algebra equivalences below are explicitly induced by evaluation at the given
uniformizer. The subalgebra `S` is identified with the actual integral closure in `E`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open Polynomial IsLocalRing
open scoped nonZeroDivisors

namespace IsDiscreteValuationRing

/-- Finite residue expansion, followed by Nakayama. -/
private theorem span_uniformizer_powers
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Finite R S]
    (n : ℕ) (t : S) (ht : maximalIdeal S = Ideal.span {t})
    (hresidue : Function.Surjective (ResidueField.map (algebraMap R S)))
    (hramification : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ n) :
    Submodule.span R (Set.range fun i : Fin n ↦ t ^ (i : ℕ)) = ⊤ := by
  classical
  have hlift (s : S) : ∃ r : R, ∃ y : S, s = algebraMap R S r + t * y := by
    obtain ⟨a, ha⟩ := hresidue (residue S s)
    obtain ⟨r, rfl⟩ := residue_surjective a
    have hsub : s - algebraMap R S r ∈ Ideal.span {t} := by
      rw [← ht, ← residue_eq_zero_iff, map_sub, ← ResidueField.map_residue, ha, sub_self]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hsub
    exact ⟨r, y, by rw [← hy]; ring⟩
  have hexpand (k : ℕ) (s : S) :
      ∃ c : Fin k → R, ∃ y : S,
        s = (∑ i, algebraMap R S (c i) * t ^ (i : ℕ)) + t ^ k * y := by
    induction k generalizing s with
    | zero => exact ⟨Fin.elim0, s, by simp⟩
    | succ k ih =>
      obtain ⟨c, y, hy⟩ := ih s
      obtain ⟨r, z, hz⟩ := hlift y
      refine ⟨Fin.snoc c r, z, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      rw [hy, hz, pow_succ]
      ring
  let N := Submodule.span R (Set.range fun i : Fin n ↦ t ^ (i : ℕ))
  apply (map_mkQ_eq_top (N := N)).mp
  apply top_unique
  intro x _
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective (maximalIdeal R • (⊤ : Submodule R S)) x
  obtain ⟨c, y, hy⟩ := hexpand n s
  have hsum : (∑ i, algebraMap R S (c i) * t ^ (i : ℕ)) ∈ N := by
    apply Submodule.sum_mem
    intro i _
    simpa only [Algebra.smul_def] using
      N.smul_mem (c i) (Submodule.subset_span ⟨i, rfl⟩)
  have htail : t ^ n * y ∈ maximalIdeal R • (⊤ : Submodule R S) := by
    rw [Ideal.smul_top_eq_map, hramification, ht, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr ⟨y, rfl⟩
  refine Submodule.mem_map.mpr ⟨_, hsum, ?_⟩
  rw [hy, map_add]
  have hzero : (maximalIdeal R • (⊤ : Submodule R S)).mkQ (t ^ n * y) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr htail
  rw [hzero, add_zero]

/-- The coefficient formula for the polynomial of a power basis. -/
private theorem powerBasis_coeff
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (pb : PowerBasis R S) (i : ℕ) (hi : i < pb.dim) :
    pb.minpolyGen.coeff i = -pb.basis.repr (pb.gen ^ pb.dim) ⟨i, hi⟩ := by
  classical
  rw [PowerBasis.minpolyGen, coeff_sub, finsetSum_coeff]
  have hne : i ≠ pb.dim := Nat.ne_of_lt hi
  simp only [coeff_X_pow, if_neg hne, coeff_C_mul_X_pow, zero_sub]
  congr 1
  rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin pb.dim)]
  · simp
  · intro j _ hj
    have hji : i ≠ (j : ℕ) := fun h ↦ hj (Fin.ext h.symm)
    simp [hji]
  · simp

/-- Every uniformizer of the integral closure in a totally ramified finite separable
extension gives an Eisenstein polynomial and the integral and fraction-field presentations.

Source: Stacks Project, More on Algebra, Tag 09ER,
`lemma-weakly-unramified-goes-up-along-totally-ramified`, first proof paragraph
(blueprint: lem-sfb-totally-ramified-uniformizer-presentation).

Proof:
1. Finite separable normalization makes `S` a finite `R`-module, with rank `n`.
2. Residue surjectivity gives `s = r + t * y`. Iterate this `n` times; the remainder
   belongs to `t ^ n * S = maximalIdeal R * S`. By Nakayama the first `n` powers
   span `S`. Their number equals its rank, so they form a basis.
3. Write `t ^ n = pi * v` using the ramification equality. The reverse divisibility
   and cancellation show that `v` is a unit. The polynomial of the power basis has
   lower coefficients `-pi * c_i`, where the `c_i` are the coordinates of `v`.
   If its constant coefficient belonged to `(pi ^ 2)`, then `c_0` would belong to
   the maximal ideal of `R`. Locality and the coordinate expansion of `v` would
   put this unit in the maximal ideal of `S`, a contradiction.
4. The standard power-basis quotient equivalence gives the integral presentation.
   Localize the same basis at the nonzero elements of `R` to get an `F`-basis of
   `E`. Its coordinate maps, hence its basis polynomial, are the images of those
   over `R`. The same quotient equivalence gives the fraction-field presentation.
   Both equivalences send a polynomial class to its evaluation at the chosen `t`. -/
theorem exists_uniformizer_polynomial_presentation
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (F : Type v) [Field F] [Algebra R F] [IsFractionRing R F]
    (E : Type w) [Field E] [Algebra F E] [Algebra R E] [IsScalarTower R F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (n : ℕ) (hn : 1 ≤ n) (hdegree : Module.finrank F E = n)
    (S : Subalgebra R E) (hS : S = integralClosure R E)
    [IsDiscreteValuationRing S] [IsLocalHom (algebraMap R S)]
    (hresidue : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R S)))
    (hramification : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ n)
    (pi : R) (hpi : maximalIdeal R = Ideal.span {pi})
    (t : S) (ht : maximalIdeal S = Ideal.span {t}) :
    ∃ P : R[X], P.Monic ∧ P.natDegree = n ∧
      (∀ i : ℕ, i < n → P.coeff i ∈ Ideal.span {pi}) ∧
      P.coeff 0 ∉ Ideal.span {pi ^ 2} ∧
      (∃ e : (R[X] ⧸ Ideal.span {P}) ≃ₐ[R] S,
        ∀ Q : R[X], e (Ideal.Quotient.mk (Ideal.span {P}) Q) = aeval t Q) ∧
      (∃ e : (F[X] ⧸ Ideal.span {P.map (algebraMap R F)}) ≃ₐ[F] E,
        ∀ Q : F[X],
          e (Ideal.Quotient.mk (Ideal.span {P.map (algebraMap R F)}) Q) =
            aeval (t : E) Q) := by
  classical
  have : IsIntegralClosure S R E := by subst S; infer_instance
  have : Module.Finite R S := IsIntegralClosure.finite R F E S
  have : Module.IsTorsionFree R E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [IsScalarTower.algebraMap_eq R F E]
      exact (algebraMap F E).injective.comp (IsFractionRing.injective R F))
  have hrank : Module.finrank R S = n := (IsIntegralClosure.rank R F E S).trans hdegree
  have hspan := span_uniformizer_powers n t ht hresidue.2 hramification
  let b := basisOfTopLeSpanOfCardEqFinrank (fun i : Fin n ↦ t ^ (i : ℕ)) hspan.ge
    (by simpa using hrank.symm)
  have hb (i : Fin n) : b i = t ^ (i : ℕ) := by simp [b]
  let pb : PowerBasis R S := ⟨t, n, b, hb⟩
  have hideal : Ideal.span {algebraMap R S pi} = Ideal.span {t ^ n} := by
    simpa only [hpi, ht, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow]
      using hramification
  obtain ⟨v, hv⟩ : ∃ v : S, t ^ n = algebraMap R S pi * v := by
    have hm : t ^ n ∈ Ideal.span {algebraMap R S pi} := by
      rw [hideal]; exact Ideal.subset_span (Set.mem_singleton _)
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hm
    exact ⟨v, hv⟩
  have hcoeff (i : ℕ) (hi : i < n) :
      pb.minpolyGen.coeff i = -(pi * b.repr v ⟨i, hi⟩) := by
    rw [powerBasis_coeff pb i hi]
    change -b.repr (t ^ n) ⟨i, hi⟩ = _
    rw [hv, ← Algebra.smul_def, map_smul]
    rfl
  have ht0 : t ≠ 0 := ((irreducible_iff_uniformizer t).mpr ht).ne_zero
  have hpi0 : pi ≠ 0 := ((irreducible_iff_uniformizer pi).mpr hpi).ne_zero
  have hvunit : IsUnit v := by
    have hm : algebraMap R S pi ∈ Ideal.span {t ^ n} := by
      rw [← hideal]; exact Ideal.subset_span (Set.mem_singleton _)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hm
    have hwv : w * v = 1 := by
      apply mul_left_cancel₀ (pow_ne_zero n ht0)
      calc
        t ^ n * (w * v) = (t ^ n * w) * v := (mul_assoc _ _ _).symm
        _ = algebraMap R S pi * v := by rw [hw]
        _ = t ^ n * 1 := by rw [← hv, mul_one]
    exact IsUnit.of_mul_eq_one_right w hwv
  have hconst : pb.minpolyGen.coeff 0 ∉ Ideal.span {pi ^ 2} := by
    intro hbad
    have hc : b.repr v ⟨0, hn⟩ ∈ maximalIdeal R := by
      rw [hpi, Ideal.mem_span_singleton]
      have hh : pi * pi ∣ pi * (-b.repr v ⟨0, hn⟩) := by
        simpa only [pow_two, hcoeff 0 hn, neg_mul_eq_mul_neg] using
          (Ideal.mem_span_singleton.mp hbad)
      exact dvd_neg.mp ((mul_dvd_mul_iff_left hpi0).mp hh)
    have hvnot : v ∉ maximalIdeal S := by simpa using hvunit
    apply hvnot
    rw [← b.sum_repr v]
    apply Ideal.sum_mem
    intro i _
    by_cases hi : i = ⟨0, hn⟩
    · subst i
      simpa [hb, Algebra.smul_def] using map_nonunit (algebraMap R S) _ hc
    · rw [hb, Algebra.smul_def]
      apply Ideal.mul_mem_left
      have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero fun h ↦ hi (Fin.ext h)
      apply Ideal.pow_mem_of_mem _ _ _ hipos
      rw [ht]
      exact Ideal.subset_span (Set.mem_singleton _)
  have : IsLocalization (Algebra.algebraMapSubmonoid S R⁰) E :=
    IsIntegralClosure.isLocalization R F E S
  let bF := b.localizationLocalization F R⁰ E
  let pbF : PowerBasis F E :=
    ⟨(t : E), n, bF, fun i ↦ by simp [bF, hb]⟩
  have hpoly : pbF.minpolyGen = pb.minpolyGen.map (algebraMap R F) := by
    simp only [PowerBasis.minpolyGen, pb, pbF, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    change bF.repr (algebraMap S E t ^ n) i = algebraMap R F (b.repr (t ^ n) i)
    rw [← map_pow, Module.Basis.localizationLocalization_repr_algebraMap]
  refine ⟨pb.minpolyGen, pb.minpolyGen_monic, pb.natDegree_minpolyGen, ?_, hconst, ?_, ?_⟩
  · intro i hi
    rw [hcoeff i hi, Ideal.mem_span_singleton]
    exact dvd_neg.mpr (dvd_mul_right pi _)
  · let e := AdjoinRoot.equiv' pb.minpolyGen pb
      (by simp only [← pb.minpolyGen_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
      pb.aeval_minpolyGen
    exact ⟨e, fun Q ↦ by
      change AdjoinRoot.liftAlgHom pb.minpolyGen (Algebra.ofId R S) pb.gen
        pb.aeval_minpolyGen (AdjoinRoot.mk pb.minpolyGen Q) = _
      simp only [AdjoinRoot.liftAlgHom_mk, Polynomial.aeval_def, Algebra.toRingHom_ofId]
      rfl⟩
  · rw [← hpoly]
    let e := AdjoinRoot.equiv' pbF.minpolyGen pbF
      (by simp only [← pbF.minpolyGen_eq, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
      pbF.aeval_minpolyGen
    exact ⟨e, fun Q ↦ by
      change AdjoinRoot.liftAlgHom pbF.minpolyGen (Algebra.ofId F E) pbF.gen
        pbF.aeval_minpolyGen (AdjoinRoot.mk pbF.minpolyGen Q) = _
      simp only [AdjoinRoot.liftAlgHom_mk, Polynomial.aeval_def, Algebra.toRingHom_ofId]
      rfl⟩

end IsDiscreteValuationRing
