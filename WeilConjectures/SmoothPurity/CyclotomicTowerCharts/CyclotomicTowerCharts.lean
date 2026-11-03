/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import WeilConjectures.RingTheory.MonicUnitDifferenceEvaluation

/-! # Prime-power cyclotomic transition and root-splitting charts

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md`, Proof (1), primitive-root schemes
(blueprint: lem-pur-cyclotomic-tower-charts).

The abbreviations only specialize the existing localization, polynomial and quotient
constructions. All chart maps below are specified on every polynomial representative.
The successor algebra structure is quantified with its defining coefficient map, so the
statement can use the genuine algebra equivalence and tensor product APIs without choosing
a transition map before asserting its existence.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped Polynomial TensorProduct
open AlgebraicGeometry CategoryTheory Polynomial

namespace CyclotomicTowerCharts

universe u

/-- The base Z[1/ell]. Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev base (ell : ℕ) : Type := Localization.Away (ell : ℤ)

/-- The integer cyclotomic polynomial with coefficients localized in the base.
Source: primitive-root schemes, Proof (1) (blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev polynomial (ell n : ℕ) : (base ell)[X] :=
  (Polynomial.cyclotomic (ell ^ n) ℤ).map (algebraMap ℤ (base ell))

/-- C_n = Z[1/ell][T]/(Phi_(ell^n)). Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev ring (ell n : ℕ) : Type := AdjoinRoot (polynomial ell n)

/-- The class z_n of T. Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev root (ell n : ℕ) : ring ell n := AdjoinRoot.root (polynomial ell n)

/-- The transition presentation polynomial Y^ell-z_n. Source: primitive-root schemes,
Proof (1) (blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev stepPolynomial (ell n : ℕ) : (ring ell n)[X] := X ^ ell - C (root ell n)

/-- The splitting polynomial Y^(ell^n)-1. Source: primitive-root schemes, Proof (1)
(blueprint: lem-pur-cyclotomic-tower-charts). -/
abbrev rootsPolynomial (ell n : ℕ) : (ring ell n)[X] := X ^ (ell ^ n) - 1

private theorem polynomial_eq (ell n : ℕ) :
    polynomial ell n = cyclotomic (ell ^ n) (base ell) := by
  exact map_cyclotomic _ _

private theorem ell_unit (ell : ℕ) : IsUnit (ell : base ell) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (S := base ell) (ell : ℤ)

private theorem power_unit (ell n : ℕ) : IsUnit ((ell ^ n : ℕ) : base ell) := by
  simpa using (ell_unit ell).pow n

private theorem quotient_etale {R : Type*} [CommRing R] {f : R[X]}
    (hf : f.Monic) (hs : f.Separable) : Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := hs
  let P : StandardEtalePair R := ⟨f, hf, 1, b, a, 0, by simpa [mul_comm, add_comm] using hab⟩
  let e : P.Ring ≃ₐ[R] AdjoinRoot f := AlgEquiv.ofAlgHom
    (P.lift (AdjoinRoot.root f) ⟨by simp [P, AdjoinRoot.aeval_eq], by simp [P]⟩)
    (AdjoinRoot.liftAlgHom f (Algebra.ofId R _) P.X P.hasMap_X.1)
    (by apply AdjoinRoot.algHom_ext; simp)
    (by apply StandardEtalePair.hom_ext; simp)
  exact Algebra.Etale.of_equiv e

private theorem coefficient_injective {R : Type*} [CommRing R] [Nontrivial R]
    {f : R[X]} (hf : f.Monic) (hdeg : 0 < f.degree) :
    Function.Injective (algebraMap R (AdjoinRoot f)) := by
  change Function.Injective (AdjoinRoot.of f)
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hd : f ∣ C a := (AdjoinRoot.mk_eq_zero).mp ha
  have hm := (modByMonic_eq_zero_iff_dvd hf).mpr hd
  rw [(modByMonic_eq_self_iff hf).mpr (lt_of_le_of_lt (degree_C_le) hdeg)] at hm
  exact C_injective (by simpa using hm)

private theorem algebra_cover {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.Etale R S]
    (hinj : Function.Injective (algebraMap R S)) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  refine ⟨(IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance),
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance), ?_⟩
  exact ⟨RingHom.IsIntegral.comap_surjective
    (algebraMap_isIntegral_iff.mpr inferInstance) hinj⟩

private theorem quotient_cover {R : Type} [CommRing R] [Nontrivial R]
    {f : R[X]} (hf : f.Monic) (hdeg : 0 < f.degree) (hs : f.Separable) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot f)))) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot f)))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R (AdjoinRoot f)))) := by
  have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  have : Algebra.Etale R (AdjoinRoot f) := quotient_etale hf hs
  exact algebra_cover (coefficient_injective hf hdeg)

private theorem polynomial_separable (ell n : ℕ) : (polynomial ell n).Separable := by
  rw [polynomial_eq]
  exact (separable_X_pow_sub_C_unit (1 : (base ell)ˣ) (power_unit ell n)).of_dvd
    (by simpa using cyclotomic.dvd_X_pow_sub_one (ell ^ n) (base ell))

private theorem root_power (ell n : ℕ) : root ell n ^ (ell ^ n) = 1 := by
  have h := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
    (AdjoinRoot.of (polynomial ell n)) (root ell n)
    (show polynomial ell n ∣ X ^ (ell ^ n) - 1 by
      rw [polynomial_eq]; exact cyclotomic.dvd_X_pow_sub_one _ _) (AdjoinRoot.eval₂_root _)
  simpa [sub_eq_zero] using h

private theorem root_unit (ell n : ℕ) (hell : ell.Prime) : IsUnit (root ell n) := by
  exact IsUnit.of_pow_eq_one (root_power ell n) (pow_ne_zero n hell.ne_zero)

private theorem differences_unit (ell n : ℕ)
    (i j : ℕ) (hi : i < ell ^ n) (hj : j < ell ^ n) (hij : i ≠ j) :
    IsUnit (root ell n ^ i - root ell n ^ j) := by
  by_contra h
  obtain ⟨M, hM, hm⟩ := exists_max_ideal_of_mem_nonunits h
  let : M.IsMaximal := hM
  let π := Ideal.Quotient.mk M
  have hu : IsUnit ((ell ^ n : ℕ) : ring ell n) := by
    simpa using (power_unit ell n).map (algebraMap (base ell) (ring ell n))
  have hu' : IsUnit ((ell ^ n : ℕ) : ring ell n ⧸ M) := by simpa using hu.map π
  have : NeZero ((ell ^ n : ℕ) : ring ell n ⧸ M) := ⟨hu'.ne_zero⟩
  have hr : IsRoot (cyclotomic (ell ^ n) (ring ell n ⧸ M)) (π (root ell n)) := by
    have he : (polynomial ell n).eval₂ (algebraMap (base ell) (ring ell n))
        (root ell n) = 0 := AdjoinRoot.eval₂_root _
    have he' := congrArg π he
    rw [Polynomial.hom_eval₂, ← Polynomial.eval_map] at he'
    have hmap : (polynomial ell n).map
        (π.comp (algebraMap (base ell) (ring ell n))) =
        cyclotomic (ell ^ n) (ring ell n ⧸ M) :=
      (congrArg (Polynomial.map (π.comp (algebraMap (base ell) (ring ell n))))
        (polynomial_eq ell n)).trans (map_cyclotomic _ _)
    exact (congrArg (Polynomial.eval (π (root ell n))) hmap).symm.trans
      (by simpa only [map_zero] using he')
  have hp := isRoot_cyclotomic_iff.mp hr
  apply hij (hp.pow_inj hi hj ?_)
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  simpa [map_sub, map_pow, sub_eq_zero] using hz

private theorem splitting_chart {R : Type*} [CommRing R] (m : ℕ) (hm : 0 < m)
    (z : R) (hz : z ^ m = 1)
    (hdiff : ∀ i j : ℕ, i < m → j < m → i ≠ j → IsUnit (z ^ i - z ^ j)) :
    ∃ e : AdjoinRoot (X ^ m - 1 : R[X]) ≃ₐ[R] (ZMod m → R),
      ∀ (p : R[X]) (a : ZMod m), e (AdjoinRoot.mk _ p) a = p.eval (z ^ a.val) := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    have : Subsingleton (AdjoinRoot (X ^ m - 1 : R[X])) := Module.subsingleton R _
    let φ : AdjoinRoot (X ^ m - 1 : R[X]) →ₐ[R] (ZMod m → R) :=
      AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) 0 (Subsingleton.elim _ _)
    exact ⟨AlgEquiv.ofBijective φ
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩,
      fun _ _ ↦ Subsingleton.elim _ _⟩
  · let := hR
    obtain ⟨_, e, he⟩ := monic_unit_difference_evaluation (X ^ m - 1 : R[X])
      (monic_X_pow_sub_C (1 : R) hm.ne')
      (by simpa using (natDegree_X_pow_sub_C (R := R) (n := m) (r := 1)))
      (fun i : Fin m ↦ z ^ i.val)
      (by intro i; simp only [eval_sub, eval_pow, eval_X, eval_one]
          rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow, sub_self])
      (by intro i j hij; exact hdiff _ _ i.isLt j.isLt (fun h ↦ hij (Fin.ext h)))
    refine ⟨e.trans (AlgEquiv.piCongrLeft' R (fun _ : Fin m ↦ R)
      (ZMod.finEquiv m).toEquiv), ?_⟩
    intro p a
    have hv : (((ZMod.finEquiv m).symm a : Fin m) : ℕ) = a.val := by
      cases m with
      | zero => omega
      | succ m => rfl
    change e (Ideal.Quotient.mkₐ R (Ideal.span {X ^ m - 1}) p)
      ((ZMod.finEquiv m).symm a) = p.eval (z ^ a.val)
    simpa only [hv] using he p ((ZMod.finEquiv m).symm a)

private theorem expansion (ell n : ℕ) (hell : ell.Prime) (hn : 1 ≤ n) :
    (polynomial ell n).comp (X ^ ell) = polynomial ell (n + 1) := by
  simp only [polynomial_eq]
  rw [← Polynomial.expand_eq_comp_X_pow,
    cyclotomic_expand_eq_cyclotomic hell (dvd_pow_self ell (by omega)), pow_succ]

private theorem next_root_equation (ell n : ℕ) (hell : ell.Prime) (hn : 1 ≤ n) :
    (polynomial ell n).eval₂ (algebraMap (base ell) (ring ell (n + 1)))
      (root ell (n + 1) ^ ell) = 0 := by
  calc
    _ = ((polynomial ell n).comp (X ^ ell)).eval₂
        (algebraMap (base ell) (ring ell (n + 1))) (root ell (n + 1)) := by
      rw [eval₂_comp, eval₂_X_pow]
    _ = 0 := by
      rw [expansion ell n hell hn]
      exact AdjoinRoot.eval₂_root _

private theorem successor_chart (ell n : ℕ) (hell : ell.Prime) (hn : 1 ≤ n)
    (t : ring ell n →ₐ[base ell] ring ell (n + 1))
    (ht : t (root ell n) = root ell (n + 1) ^ ell)
    [Algebra (ring ell n) (ring ell (n + 1))]
    (hc : ∀ c : ring ell n, algebraMap (ring ell n) (ring ell (n + 1)) c = t c) :
    ∃ e : AdjoinRoot (stepPolynomial ell n) ≃ₐ[ring ell n] ring ell (n + 1),
      ∀ p : (ring ell n)[X],
        e (AdjoinRoot.mk _ p) = p.eval₂ t.toRingHom (root ell (n + 1)) := by
  let : IsScalarTower (base ell) (ring ell n) (ring ell (n + 1)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun b ↦ by
      simp only [RingHom.comp_apply, hc, AlgHom.commutes])
  let D := AdjoinRoot (stepPolynomial ell n)
  let y : D := AdjoinRoot.root (stepPolynomial ell n)
  have hy : y ^ ell = algebraMap (ring ell n) D (root ell n) := by
    have h := AdjoinRoot.eval₂_root (stepPolynomial ell n)
    simpa [stepPolynomial, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using h
  have hφ : (stepPolynomial ell n).eval₂
      (algebraMap (ring ell n) (ring ell (n + 1))) (root ell (n + 1)) = 0 := by
    simp [stepPolynomial, hc, ht]
  let φ : D →ₐ[ring ell n] ring ell (n + 1) :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (root ell (n + 1)) hφ
  have hψ : (polynomial ell (n + 1)).eval₂ (algebraMap (base ell) D) y = 0 := by
    rw [← expansion ell n hell hn, eval₂_comp]
    simp only [eval₂_X_pow, hy]
    rw [← aeval_def, aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self,
      map_zero]
  let ψ : ring ell (n + 1) →ₐ[base ell] D :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) y hψ
  have hψt : ψ.comp t = IsScalarTower.toAlgHom (base ell) (ring ell n) D := by
    apply AdjoinRoot.algHom_ext
    simp [ht, ψ, hy]
  let ψ' : ring ell (n + 1) →ₐ[ring ell n] D :=
    { ψ.toRingHom with
      commutes' := fun c ↦ by
        rw [hc]
        exact DFunLike.congr_fun hψt c }
  have hleft : ψ'.comp φ = AlgHom.id (ring ell n) D := by
    apply AdjoinRoot.algHom_ext
    simp [ψ', ψ, φ, y]
    rfl
  have hright : φ.comp ψ' = AlgHom.id (ring ell n) (ring ell (n + 1)) := by
    apply AlgHom.restrictScalars_injective (R := base ell)
    apply AdjoinRoot.algHom_ext
    change φ (ψ (root ell (n + 1))) = root ell (n + 1)
    have hψroot : ψ (root ell (n + 1)) = y := AdjoinRoot.liftAlgHom_root _ _ _ _
    rw [hψroot]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  refine ⟨AlgEquiv.ofAlgHom φ ψ' hright hleft, ?_⟩
  intro p
  change p.eval₂ (algebraMap (ring ell n) (ring ell (n + 1))) _ = _
  congr 1
  exact RingHom.ext hc

private theorem base_change_chart {R S A : Type*} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] (f : R[X]) (e : AdjoinRoot f ≃ₐ[R] S) :
    ∃ e' : AdjoinRoot (f.map (algebraMap R A)) ≃ₐ[A] A ⊗[R] S,
      ∀ p : A[X], e' (AdjoinRoot.mk _ p) =
        p.eval₂ (algebraMap A (A ⊗[R] S)) (1 ⊗ₜ[R] e (AdjoinRoot.root f)) := by
  let q := f.map (Algebra.TensorProduct.includeRight : R →ₐ[R] A ⊗[R] R).toRingHom
  let rid := Algebra.TensorProduct.rid R A A
  have hq : q.map rid.toRingHom = f.map (algebraMap R A) := by
    simp only [q, map_map]
    congr 1
    ext r
    simp [rid, Algebra.smul_def]
  let b : A ⊗[R] AdjoinRoot f ≃ₐ[A] AdjoinRoot (f.map (algebraMap R A)) :=
    (AdjoinRoot.tensorAlgEquiv f q rfl).trans
      (AdjoinRoot.mapAlgEquiv rid q _ (hq ▸ Associated.refl _))
  let c := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) e
  let e' := b.symm.trans c
  have hb : b (1 ⊗ₜ[R] AdjoinRoot.root f) = AdjoinRoot.root _ := by
    simp [b]
  have he' : e' (AdjoinRoot.root _) = 1 ⊗ₜ[R] e (AdjoinRoot.root f) := by
    rw [← hb]
    simp [e', c]
  refine ⟨e', ?_⟩
  intro p
  rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, he', aeval_def]

/-- The finite etale cyclotomic covers, their power transitions, and the transition and
root-splitting charts, including all commutative-algebra base changes.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md`, Proof (1), primitive-root schemes
(blueprint: lem-pur-cyclotomic-tower-charts).

Proof plan (the seven steps of the node):
1. The cyclotomic power identity gives z_n^(ell^n)=1. Differentiating it shows that
   Phi'(z_n)(z_n^(ell^(n-1))-1)=(ell^n)z_n^(ell^n-1), a unit, hence Phi'(z_n) is a unit.
2. Monicity and positive degree give a finite free quotient and injective coefficient map
   (lem-weil-pbc-monic-quotient-free). Finite-algebra integrality and lying over
   (lem-weil-pbc-finite-algebra-is-integral, lem-weil-pbc-integral-injective-lying-over)
   give a finite surjection. Inverting the already invertible derivative identifies the
   quotient with a standard etale algebra (lem-weil-pbc-standard-etale-monic-derivative).
3. Phi_(ell^n)(T^ell)=Phi_(ell^(n+1))(T) gives the transition map. The maps between
   C_n[Y]/(Y^ell-z_n) and C_(n+1) fix coefficients and the displayed generator in both
   composites (lem-pur-cyclotomic-power-identity, def-weil-pbc-algebra-hom-quotient).
4. The transition polynomial is monic with unit derivative ell*y^(ell-1). Apply the same
   finite-free, integral, lying-over and standard-etale arguments as in step 2.
5. The geometric sum for w=z_n^(ell^(n-1)) shows ell is a multiple of 1-w. For
   0<k<ell^n write k=ell^s*u with ell not dividing u, and choose v inverse to u modulo
   ell^(n-s). The geometric sums show 1-w is a multiple of 1-z_n^(ell^s), in turn a
   multiple of 1-z_n^k. Thus 1-z_n^k and all differences of distinct root powers are units.
6. Apply lem-pur-monic-unit-difference-evaluation to Y^(ell^n)-1 over the nonzero C_n,
   with roots z_n^a, indexed by their residue classes. This gives exactly evaluation.
7. Under coefficient base change the transition substitutions remain mutually inverse.
   For the splitting chart, root equations and unit differences persist; apply the same
   evaluation lemma when the algebra is nonzero. For the zero algebra all the displayed
   quotients, tensor products and finite products are zero rings and the maps are unique.
-/
theorem cyclotomicTowerCharts (ell n : ℕ) (hell : ell.Prime) (hn : 1 ≤ n) :
    (IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (base ell) (ring ell n)))) ∧
      Etale (Spec.map (CommRingCat.ofHom (algebraMap (base ell) (ring ell n)))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap (base ell) (ring ell n))))) ∧
    (∃ e : AdjoinRoot (rootsPolynomial ell n) ≃ₐ[ring ell n]
        (ZMod (ell ^ n) → ring ell n),
      ∀ (p : (ring ell n)[X]) (a : ZMod (ell ^ n)),
        e (AdjoinRoot.mk (rootsPolynomial ell n) p) a = p.eval (root ell n ^ a.val)) ∧
    (∀ (A : Type u) [CommRing A] [Algebra (ring ell n) A],
      ∃ e : AdjoinRoot ((rootsPolynomial ell n).map (algebraMap (ring ell n) A)) ≃ₐ[A]
          (ZMod (ell ^ n) → A),
        ∀ (p : A[X]) (a : ZMod (ell ^ n)),
          e (AdjoinRoot.mk _ p) a = p.eval (algebraMap (ring ell n) A (root ell n) ^ a.val)) ∧
    (∃ t : ring ell n →ₐ[base ell] ring ell (n + 1),
      t (root ell n) = root ell (n + 1) ^ ell ∧
      IsFinite (Spec.map (CommRingCat.ofHom t.toRingHom)) ∧
      Etale (Spec.map (CommRingCat.ofHom t.toRingHom)) ∧
      Surjective (Spec.map (CommRingCat.ofHom t.toRingHom)) ∧
      ∀ [nextAlgebra : Algebra (ring ell n) (ring ell (n + 1))],
        (∀ c : ring ell n,
          @algebraMap (ring ell n) (ring ell (n + 1)) _ _ nextAlgebra c = t c) →
        (∃ e : AdjoinRoot (stepPolynomial ell n) ≃ₐ[ring ell n] ring ell (n + 1),
          ∀ p : (ring ell n)[X],
            e (AdjoinRoot.mk _ p) = p.eval₂ t.toRingHom (root ell (n + 1))) ∧
        (∀ (A : Type u) [CommRing A] [Algebra (ring ell n) A],
          ∃ e : AdjoinRoot ((stepPolynomial ell n).map (algebraMap (ring ell n) A)) ≃ₐ[A]
              A ⊗[ring ell n] ring ell (n + 1),
            ∀ p : A[X], e (AdjoinRoot.mk _ p) =
              p.eval₂ (algebraMap A (A ⊗[ring ell n] ring ell (n + 1)))
                (1 ⊗ₜ[ring ell n] root ell (n + 1)))) := by
  let : IsDomain (base ell) := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (show (ell : ℤ) ≠ 0 by exact_mod_cast hell.ne_zero))
  have hm : 0 < ell ^ n := pow_pos hell.pos n
  have hf : (polynomial ell n).Monic := by
    rw [polynomial_eq]; exact cyclotomic.monic _ _
  have hd : 0 < (polynomial ell n).degree := by
    rw [polynomial_eq]; exact degree_cyclotomic_pos _ _ hm
  have : Nontrivial (ring ell n) := (coefficient_injective hf hd).nontrivial
  refine ⟨quotient_cover hf hd (polynomial_separable ell n),
    splitting_chart _ hm _ (root_power ell n) (differences_unit ell n), ?_, ?_⟩
  · intro A _ _
    have hmap : (rootsPolynomial ell n).map (algebraMap (ring ell n) A) =
        (X ^ (ell ^ n) - 1 : A[X]) := by
      simp only [rootsPolynomial, Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_one]
    rw [hmap]
    exact
      splitting_chart (ell ^ n) hm (algebraMap (ring ell n) A (root ell n))
        (by rw [← map_pow, root_power, map_one])
        (by
          intro i j hi hj hij
          simpa only [map_sub, map_pow] using
            (differences_unit ell n i j hi hj hij).map (algebraMap (ring ell n) A))
  · let t : ring ell n →ₐ[base ell] ring ell (n + 1) :=
      AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (root ell (n + 1) ^ ell)
        (next_root_equation ell n hell hn)
    have ht : t (root ell n) = root ell (n + 1) ^ ell := by
      simp [t]
    let : Algebra (ring ell n) (ring ell (n + 1)) := t.toRingHom.toAlgebra
    obtain ⟨e, he⟩ := successor_chart ell n hell hn t ht (fun _ ↦ rfl)
    have hq : (stepPolynomial ell n).Monic := monic_X_pow_sub_C _ hell.ne_zero
    have hdq : 0 < (stepPolynomial ell n).degree := by
      rw [stepPolynomial, degree_X_pow_sub_C hell.pos]
      exact_mod_cast hell.pos
    have hu : IsUnit (ell : ring ell n) := by
      simpa using (ell_unit ell).map (algebraMap (base ell) (ring ell n))
    have hs : (stepPolynomial ell n).Separable := by
      simpa only [IsUnit.unit_spec] using
        separable_X_pow_sub_C_unit (root_unit ell n hell).unit hu
    have : Module.Finite (ring ell n) (AdjoinRoot (stepPolynomial ell n)) := hq.finite_adjoinRoot
    have : Module.Finite (ring ell n) (ring ell (n + 1)) := Module.Finite.equiv e.toLinearEquiv
    have : Algebra.Etale (ring ell n) (AdjoinRoot (stepPolynomial ell n)) :=
      quotient_etale hq hs
    have : Algebra.Etale (ring ell n) (ring ell (n + 1)) := Algebra.Etale.of_equiv e
    have hinj : Function.Injective (algebraMap (ring ell n) (ring ell (n + 1))) := by
      intro a b hab
      apply coefficient_injective hq hdq
      apply e.injective
      simpa only [AlgEquiv.commutes] using hab
    obtain ⟨hfin, het, hsurj⟩ := algebra_cover hinj
    refine ⟨t, ht, hfin, het, hsurj, ?_⟩
    intro nextAlgebra hc
    obtain ⟨e', he'⟩ := @successor_chart ell n hell hn t ht nextAlgebra hc
    refine ⟨⟨e', he'⟩, ?_⟩
    intro A _ _
    obtain ⟨b, hb⟩ := base_change_chart (A := A) (stepPolynomial ell n) e'
    refine ⟨b, ?_⟩
    intro p
    rw [hb]
    congr 2
    simpa using he' X

end CyclotomicTowerCharts
