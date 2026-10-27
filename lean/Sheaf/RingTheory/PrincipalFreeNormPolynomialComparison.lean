module

public import WeilConjectures.Algebra.CharpolyLocallyFree
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Polynomial.Monic

/-! # Principal free norm polynomial comparison

Source: Stacks, Tags 02DV, 00DX, 00EK and 03BJ, the monicity and precise
Cayley–Hamilton paragraph of `groupoids-lemma-integral-over-invariants`.
(blueprint: lem-a1-principal-free-norm-polynomial-comparison)
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

private theorem charpoly_scalar_tower
    {A S T M : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
    [AddCommGroup M] [Module A M] {n : ℕ}
    (b : Module.Basis (Fin n) S (S ⊗[A] M))
    (e : Module.Basis (Fin n) T (T ⊗[A] M)) (φ : M →ₗ[A] M) :
    (LinearMap.toMatrix b b (φ.baseChange S)).charpoly.map (algebraMap S T) =
      (LinearMap.toMatrix e e (φ.baseChange T)).charpoly := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have := Module.Free.of_basis e
  have := Module.Finite.of_basis e
  let L := _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T M
  rw [LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix,
    ← LinearMap.charpoly_baseChange, LinearMap.baseChange_baseChange]
  change (L.symm.conj (φ.baseChange T)).charpoly = _
  exact LinearEquiv.charpoly_conj _ _

private theorem chosen_charpoly_local
    {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]
    {r m : ℕ} (f : Fin m → A) (hgen : Ideal.span (Set.range f) = ⊤)
    (e : ∀ i : Fin m, Module.Basis (Fin r) (Localization.Away (f i))
      (LocalizedModule.Away (f i) M)) (φ : M →ₗ[A] M) (i : Fin m) :
    (Classical.choose (charpoly_locallyFree_exists_unique.{u, v, w}
      f hgen (fun i ↦ ⟨e i, trivial⟩) φ)).map
        (algebraMap A (Localization.Away (f i))) =
      (LinearMap.toMatrix (e i) (e i)
        (IsLocalizedModule.mapExtendScalars (Submonoid.powers (f i))
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
          (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
          (Localization.Away (f i)) φ)).charpoly := by
  classical
  let S := Localization.Away (f i)
  let T := ULift.{w} S
  let q : S →+* T := ULift.ringEquiv.symm.toRingHom
  let ρ := q.comp (algebraMap A S)
  let : Algebra S T := q.toAlgebra
  let : Algebra A T := ρ.toAlgebra
  let : Module S T := Algebra.toModule
  let : Module A T := Algebra.toModule
  let : SMul S T := (inferInstance : Module S T).toSMul
  let : SMul A T := (inferInstance : Module A T).toSMul
  have : IsScalarTower A S T :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := S) (A := T) fun _ ↦ rfl
  let E := (LocalizedModule.isBaseChange (Submonoid.powers (f i)) M).equiv
  let b := (e i).map E.symm
  let eT := (b.baseChange T).map
    (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange A S T T M)
  have hP := (Classical.choose_spec (charpoly_locallyFree_exists_unique.{u, v, w}
    f hgen (fun i ↦ ⟨e i, trivial⟩) φ)).1.1
  have hS : (Classical.choose (charpoly_locallyFree_exists_unique.{u, v, w}
      f hgen (fun i ↦ ⟨e i, trivial⟩) φ)).map (algebraMap A S) =
      (LinearMap.toMatrix b b (φ.baseChange S)).charpoly := by
    apply Polynomial.map_injective q ULift.ringEquiv.symm.injective
    rw [Polynomial.map_map]
    exact (hP T ρ eT).trans (charpoly_scalar_tower b eT φ).symm
  rw [hS]
  congr 1
  simp only [b, LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right]
  congr 1
  apply LinearMap.restrictScalars_injective A
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers (f i))
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
  ext x
  change E ((φ.baseChange S) (E.symm
    ((LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M) x))) =
    IsLocalizedModule.map (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M) φ
      ((LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M) x)
  rw [IsLocalizedModule.map_apply]
  simp only [E, IsBaseChange.equiv_symm_apply, LinearMap.baseChange_tmul,
    IsBaseChange.equiv_tmul, one_smul]

private theorem localized_multiplication_eval
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (s : A) (b : B) (p : Polynomial A) :
    let ι := LocalizedModule.mkLinearMap (Submonoid.powers s) B
    let μ := IsLocalizedModule.mapExtendScalars (Submonoid.powers s) ι ι
      (Localization.Away s) (LinearMap.mul A B b)
    ι ((p.map (algebraMap A B)).eval b) =
      Polynomial.aeval μ (p.map (algebraMap A (Localization.Away s))) (ι 1) := by
  classical
  dsimp only
  let ι := LocalizedModule.mkLinearMap (Submonoid.powers s) B
  let μ := IsLocalizedModule.mapExtendScalars (Submonoid.powers s) ι ι
    (Localization.Away s) (LinearMap.mul A B b)
  have hμ (x : B) : μ (ι x) = ι (b * x) := by
    simp [μ, IsLocalizedModule.mapExtendScalars]
  have hpow (n : ℕ) (x : B) : (μ ^ n) (ι x) = ι (b ^ n * x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hμ, pow_succ', mul_assoc]
  change ι ((p.map (algebraMap A B)).eval b) =
    Polynomial.aeval μ (p.map (algebraMap A (Localization.Away s))) (ι 1)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, Polynomial.eval_add,
      map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [Polynomial.map_monomial, Polynomial.eval_monomial,
      Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      hpow, mul_one, IsScalarTower.algebraMap_smul]
    simpa only [Algebra.smul_def] using ι.map_smul c (b ^ n)

/-- A polynomial norm characterized by local determinants equals the scalar-extension
characteristic polynomial of multiplication and annihilates the element.

The algebra map is the given unital map A → B. In `hN`, the `(j,k)` entry is the
polynomial whose coefficient in degree d is the `(j,k)` entry of multiplication by
`v.coeff d` localized at fᵢ. Thus this is exactly the multiplication matrix of the
image of v in the constant polynomial basis C(eᵢₖ), without choosing a global basis.
The chosen characteristic polynomial below comes directly from the existence and
uniqueness theorem, with its test-algebra universe left arbitrary.

Source: Stacks, Tags 02DV(1),(3), 00DX, 00EK and 03BJ, monicity and precise
Cayley–Hamilton paragraph.
(blueprint: lem-a1-principal-free-norm-polynomial-comparison)

Proof:
1. Apply `lem-weil-pbc-charpoly-locally-free-existence` to multiplication by b.
Use `lem-weil-pbc-localization-module-tensor` to identify its scalar extension
with localized multiplication. `lem-weil-pbc-charpoly-free-module-properties`
gives the local matrix characteristic polynomials and the global expansion.
2. Expand multiplication by X-C(b) in each constant polynomial basis: its matrix
is XI minus the constant multiplication matrix. The hypothesis hN identifies its
determinant with the localization of N(X-C(b)); this is the local characteristic
polynomial by `def-weil-pbc-charpoly-free-module` and
`def-weil-endomorphism-determinant`.
3. For each coefficient, the difference between the norm polynomial and the
chosen characteristic polynomial vanishes in every localization. Apply
`lem-weil-pbc-localized-span-eq-zero` with M=A and the unit-ideal cover.
4. Apply `lem-weil-cayley-hamilton-free-module` to localized multiplication by b.
Evaluate the endomorphism identity at 1; its kth power sends 1 to bᵢ^k. Thus
the image of the characteristic polynomial evaluates to zero on every chart.
5. Polynomial evaluation commutes with localization. Apply
`lem-weil-pbc-localized-span-eq-zero` with M=B to descend the evaluation identity.
No injectivity of the algebra map is used.
6. Over a nonzero base ring the expansion has leading coefficient 1 in degree r.
If r=0 every localized module has an empty basis and is zero; localization
descent makes B zero, and the expansion is 1. If A is zero, unitality forces B
zero. These arguments include zero local rings and the empty cover.
-/
theorem principal_free_norm_polynomial_comparison
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {r m : ℕ} (f : Fin m → A) (hgen : Ideal.span (Set.range f) = ⊤)
    (e : ∀ i : Fin m, Module.Basis (Fin r) (Localization.Away (f i))
      (LocalizedModule.Away (f i) B))
    (N : Polynomial B → Polynomial A)
    (hN : ∀ (q : Polynomial B) (i : Fin m),
      (N q).map (algebraMap A (Localization.Away (f i))) =
        Matrix.det (fun j k : Fin r ↦ q.sum fun d c ↦ Polynomial.monomial d
          (LinearMap.toMatrix (e i) (e i)
            (IsLocalizedModule.mapExtendScalars (Submonoid.powers (f i))
              (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B)
              (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B)
              (Localization.Away (f i)) (LinearMap.mul A B c)) j k)))
    (b : B) :
    N (Polynomial.X - Polynomial.C b) =
        Classical.choose (charpoly_locallyFree_exists_unique.{u, v, w}
          f hgen (fun i ↦ ⟨e i, trivial⟩) (LinearMap.mul A B b)) ∧
      (∃ a : Fin r → A, N (Polynomial.X - Polynomial.C b) =
        Polynomial.X ^ r + ∑ j : Fin r, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) ∧
      ((N (Polynomial.X - Polynomial.C b)).map (algebraMap A B)).eval b = 0 ∧
      (Nontrivial A → (N (Polynomial.X - Polynomial.C b)).Monic ∧
        (N (Polynomial.X - Polynomial.C b)).natDegree = r) ∧
      (r = 0 → Subsingleton B ∧ N (Polynomial.X - Polynomial.C b) = 1) ∧
      (Subsingleton A → Subsingleton B) := by
  classical
  let χ := Classical.choose (charpoly_locallyFree_exists_unique.{u, v, w}
    f hgen (fun i ↦ ⟨e i, trivial⟩) (LinearMap.mul A B b))
  let μ (i : Fin m) := IsLocalizedModule.mapExtendScalars (Submonoid.powers (f i))
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B)
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B)
    (Localization.Away (f i))
  let M (i : Fin m) (c : B) := LinearMap.toMatrix (e i) (e i)
    (μ i (LinearMap.mul A B c))
  have hone (i : Fin m) : M i 1 = 1 := by
    have h : μ i (LinearMap.mul A B 1) = LinearMap.id := by
      apply LinearMap.restrictScalars_injective A
      apply IsLocalizedModule.linearMap_ext (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B)
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B)
      ext x
      change IsLocalizedModule.map (Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B)
        (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B)
        (LinearMap.mul A B 1)
        ((LocalizedModule.mkLinearMap (Submonoid.powers (f i)) B) x) = _
      rw [IsLocalizedModule.map_apply]
      simp
    simp only [M, h, LinearMap.toMatrix_id]
  have mzero (i : Fin m) : M i 0 = 0 := by
    dsimp only [M]
    rw [map_zero, map_zero, map_zero]
  have madd (i : Fin m) (c c' : B) : M i (c + c') = M i c + M i c' := by
    dsimp only [M]
    rw [map_add, map_add, map_add]
  have mneg (i : Fin m) (c : B) : M i (-c) = -M i c := by
    dsimp only [M]
    rw [map_neg, map_neg, map_neg]
  have hlocal (i : Fin m) :
      (N (Polynomial.X - Polynomial.C b)).map
        (algebraMap A (Localization.Away (f i))) = (M i b).charpoly := by
    rw [hN]
    change Matrix.det (fun j k ↦ (Polynomial.X - Polynomial.C b).sum
      fun d c ↦ Polynomial.monomial d (M i c j k)) = (M i b).charpoly
    unfold Matrix.charpoly
    congr 1
    ext j k : 1
    have hzero (d : ℕ) : Polynomial.monomial d (M i 0 j k) = 0 := by
      rw [mzero, Matrix.zero_apply, map_zero]
    have hadd (d : ℕ) (c c' : B) :
        Polynomial.monomial d (M i (c + c') j k) =
          Polynomial.monomial d (M i c j k) +
            Polynomial.monomial d (M i c' j k) := by
      rw [madd, Matrix.add_apply, map_add]
    rw [sub_eq_add_neg, ← Polynomial.C_neg,
      Polynomial.sum_add_index _ _ _ hzero hadd]
    rw [Polynomial.sum_X_index (f := fun d c ↦ Polynomial.monomial d (M i c j k))
      (hzero 1),
      Polynomial.sum_C_index (f := fun d c ↦ Polynomial.monomial d (M i c j k))
        (hzero 0)]
    rw [mneg, Matrix.neg_apply, map_neg]
    change Polynomial.monomial 1 (M i 1 j k) -
      Polynomial.monomial 0 (M i b j k) = _
    rw [hone]
    by_cases hjk : j = k
    · subst k
      simp [Polynomial.monomial_one_one_eq_X]
    · simp [hjk]
  have hχlocal (i : Fin m) : χ.map
      (algebraMap A (Localization.Away (f i))) = (M i b).charpoly :=
    chosen_charpoly_local.{u, v, w} f hgen e (LinearMap.mul A B b) i
  have heq : N (Polynomial.X - Polynomial.C b) = χ := by
    ext k
    apply Localization.algebraMap_injective_of_span_eq_top (Set.range f) hgen
    funext ⟨s, hs⟩
    obtain ⟨i, rfl⟩ := hs
    change algebraMap A (Localization.Away (f i))
      ((N (Polynomial.X - Polynomial.C b)).coeff k) =
      algebraMap A (Localization.Away (f i)) (χ.coeff k)
    have h := congrArg (fun p ↦ p.coeff k) ((hlocal i).trans (hχlocal i).symm)
    simpa only [Polynomial.coeff_map] using h
  obtain ⟨a, ha⟩ := (Classical.choose_spec (charpoly_locallyFree_exists_unique.{u, v, w}
    f hgen (fun i ↦ ⟨e i, trivial⟩) (LinearMap.mul A B b))).2.1
  have hexp : N (Polynomial.X - Polynomial.C b) = Polynomial.X ^ r +
      ∑ j : Fin r, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ) := heq.trans ha
  have heval : ((N (Polynomial.X - Polynomial.C b)).map (algebraMap A B)).eval b = 0 := by
    apply Module.eq_zero_of_isLocalized_span (Set.range f) hgen
      (fun s ↦ LocalizedModule.Away s.val B)
      (fun s ↦ LocalizedModule.mkLinearMap (Submonoid.powers s.val) B)
    rintro ⟨s, hs⟩
    obtain ⟨i, rfl⟩ := hs
    rw [localized_multiplication_eval, hlocal i]
    have := Module.Free.of_basis (e i)
    have := Module.Finite.of_basis (e i)
    rw [show (M i b).charpoly = (μ i (LinearMap.mul A B b)).charpoly from
      LinearMap.charpoly_toMatrix _ (e i), LinearMap.aeval_self_charpoly]
    rfl
  refine ⟨heq, ⟨a, hexp⟩, heval, ?_, ?_, ?_⟩
  · intro hA
    have := hA
    rw [hexp]
    refine ⟨Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt a), ?_⟩
    rw [Polynomial.natDegree_add_eq_left_of_degree_lt, Polynomial.natDegree_X_pow]
    simpa only [Polynomial.degree_X_pow] using Polynomial.degree_sum_fin_lt a
  · intro hr
    have : IsEmpty (Fin r) := by rw [hr]; infer_instance
    have hp : N (Polynomial.X - Polynomial.C b) = 1 := by simpa [hr] using hexp
    refine ⟨?_, hp⟩
    apply subsingleton_of_zero_eq_one
    have : (1 : B) = 0 := by simpa [hp] using heval
    exact this.symm
  · intro hA
    have := hA
    apply subsingleton_of_zero_eq_one
    exact (map_zero (algebraMap A B)).symm.trans
      ((congrArg (algebraMap A B) (Subsingleton.elim (0 : A) 1)).trans
        (map_one (algebraMap A B)))

end Algebra
