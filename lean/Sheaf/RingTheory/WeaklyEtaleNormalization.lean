/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.IndPrincipalZariski
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Pi
import WeilConjectures.RingTheory.ProEtale.WeakDimension
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions

/-!
# Normalization tensor decomposition for a local weakly etale map

Source: Silvio Greco, *Two theorems on excellent rings*, Nagoya Math. J. 60 (1976),
Lemma 5.5 proof, first two sentences (blueprint: lem-exc-weakly-etale-normalization-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct
open Algebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem generic_fractions
    (C D : Type*) [CommRing C] [IsDomain C] [CommRing D] [Algebra C D]
    [Algebra.WeaklyEtale C D] :
    IsFractionRing D (FractionRing C ⊗[C] D) ∧ IsReduced D := by
  let T := FractionRing C ⊗[C] D
  let : CommRing T := inferInstance
  let : Algebra D T := Algebra.TensorProduct.rightAlgebra
  let S := Algebra.algebraMapSubmonoid D (nonZeroDivisors C)
  have hS : S ≤ nonZeroDivisors D := by
    rintro _ ⟨s, hs, rfl⟩
    apply mem_nonZeroDivisors_iff_right.mpr
    intro d hd
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := D) hs (by
      simpa [Algebra.smul_def, mul_comm] using hd)
  have : IsLocalization S T := inferInstance
  have hinj : Function.Injective (algebraMap D T) := IsLocalization.injective T hS
  have habs : Ring.AbsolutelyFlat T :=
    Ring.AbsolutelyFlat.of_flat_lmul' (FractionRing C) T
      (Algebra.WeaklyEtale.flat_lmul' (FractionRing C) T)
  have htfae : Ring.AbsolutelyFlat T ↔
      IsReduced T ∧ ∀ P : Ideal T, P.IsPrime → P.IsMaximal :=
    (Ring.AbsolutelyFlat.tfae T).out 0 1
  have : IsReduced T := (htfae.mp habs).1
  have hred : IsReduced D := isReduced_of_injective (algebraMap D T) hinj
  refine ⟨?_, hred⟩
  apply IsLocalization.of_le S (nonZeroDivisors D) hS
  intro d hd
  have hr : IsRegular (algebraMap D T d) := by
    simpa only [IsLocalization.mk'_one] using
      (IsLocalization.isRegular_mk' (S := T) (M := S)
        (fun s hs ↦ isRegular_iff_mem_nonZeroDivisors.mpr (hS hs))
        (r := d) (m := (1 : S))).mpr (isRegular_iff_mem_nonZeroDivisors.mpr hd)
  obtain ⟨b, hb⟩ := Ring.AbsolutelyFlat.exists_eq_mul_self_mul (algebraMap D T d)
  apply isUnit_iff_exists_inv.mpr
  refine ⟨b, ?_⟩
  apply hr.left
  simpa only [mul_one, mul_assoc] using hb.symm

private theorem tensor_normalization_cancel
    (R A K D : Type*) [CommRing R] [CommRing A] [CommRing K] [CommRing D]
    [Algebra R A] [Algebra R K] [Algebra A K] [IsScalarTower R A K] [Algebra R D] :
    ∃ e : ((A ⊗[R] D) ⊗[A] K) ≃+* K ⊗[R] D,
      ∀ a d k, e ((a ⊗ₜ[R] d) ⊗ₜ[A] k) = (algebraMap A K a * k) ⊗ₜ[R] d := by
  let ec := Algebra.TensorProduct.comm A (A ⊗[R] D) K
  let eb := Algebra.TensorProduct.cancelBaseChange R A K K D
  let e := ec.toRingEquiv.trans eb.toRingEquiv
  refine ⟨e, ?_⟩
  intro a d k
  change eb (ec ((a ⊗ₜ[R] d) ⊗ₜ[A] k)) = _
  simp [ec, eb, Algebra.smul_def]

private theorem tensor_clear_denominator
    (R K D : Type*) [CommRing R] [CommRing K] [CommRing D]
    [Algebra R K] [Algebra R D] (x : K) (a s : R)
    (h : algebraMap R K s * x = algebraMap R K a) (d : D) :
    x ⊗ₜ[R] (algebraMap R D s * d) = (1 : K) ⊗ₜ[R] (algebraMap R D a * d) := by
  rw [← Algebra.smul_def s d, ← Algebra.smul_def a d]
  rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul]
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  rw [Algebra.smul_def, Algebra.smul_def, h]
  rw [mul_one]

private theorem normalization_comparison
    (C D : Type*) [CommRing C] [IsDomain C] [CommRing D] [Algebra C D]
    [Algebra.WeaklyEtale C D] :
    ∃ e : (integralClosure C (FractionRing C) ⊗[C] D) ≃ₐ[D]
        integralClosure D (FractionRing D),
      ∀ (c : integralClosure C (FractionRing C)) (a s : C), s ≠ 0 →
        algebraMap C (FractionRing C) s * c.val = algebraMap C (FractionRing C) a →
        ∀ d : D,
          algebraMap D (FractionRing D) (algebraMap C D s) * (e (c ⊗ₜ[C] d)).val =
            algebraMap D (FractionRing D) (algebraMap C D a * d) := by
  let K := FractionRing C
  let : Field K := inferInstance
  let : Algebra C K := inferInstance
  let A : Type _ := integralClosure C K
  let : CommRing A := inferInstance
  let : Algebra C A := inferInstance
  let : Algebra A K := inferInstance
  have : IsScalarTower C A K := inferInstance
  let H := A ⊗[C] D
  let : CommRing H := inferInstance
  let : Algebra A H := inferInstance
  let : Algebra D H := Algebra.TensorProduct.rightAlgebra
  let U := H ⊗[A] K
  let : CommRing U := inferInstance
  let : Algebra H U := inferInstance
  let : Algebra D U := inferInstance
  let T := K ⊗[C] D
  let : CommRing T := inferInstance
  let : Algebra D T := Algebra.TensorProduct.rightAlgebra
  have : IsFractionRing D T := (generic_fractions C D).1
  have : IsFractionRing A K := integralClosure.isFractionRing_of_finite_extension K K
  have : Algebra.IsAlgebraic A K :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := K)).mpr inferInstance
  have : IsIntegrallyClosedIn H U :=
    Algebra.WeaklyEtale.isIntegrallyClosedIn_tensorProduct A H K
  have : Algebra.IsIntegral D H := by
    let e : H ≃ₐ[D] D ⊗[C] A :=
      AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm C A D).toRingEquiv)
        (fun d ↦ by
          change (Algebra.TensorProduct.comm C A D) (1 ⊗ₜ[C] d) = d ⊗ₜ[C] 1
          simp)
    exact e.isIntegral_iff.mpr inferInstance
  have : IsIntegralClosure H D U := IsIntegralClosure.of_isIntegrallyClosedIn
  obtain ⟨e₀, he₀⟩ := tensor_normalization_cancel C A K D
  let e₁ : U ≃ₐ[D] T := AlgEquiv.ofRingEquiv (f := e₀) (by
    intro d
    change e₀ ((1 ⊗ₜ[C] d) ⊗ₜ[A] (1 : K)) = (1 : K) ⊗ₜ[C] d
    rw [he₀]
    simp)
  let e₂ : U ≃ₐ[D] FractionRing D :=
    e₁.trans (IsLocalization.algEquiv (nonZeroDivisors D) T (FractionRing D))
  let e : H ≃ₐ[D] integralClosure D (FractionRing D) :=
    (IsIntegralClosure.equiv D H U (integralClosure D U)).trans e₂.mapIntegralClosure
  refine ⟨e, ?_⟩
  intro c a s hs hsc d
  have hc : algebraMap C A s * c = algebraMap C A a := by
    apply Subtype.ext
    exact hsc
  have hH : algebraMap D H (algebraMap C D s) * (c ⊗ₜ[C] d) =
      algebraMap D H (algebraMap C D a * d) := by
    change ((1 : A) ⊗ₜ[C] algebraMap C D s) * (c ⊗ₜ[C] d) =
      (1 : A) ⊗ₜ[C] (algebraMap C D a * d)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tensor_clear_denominator C A D c a s hc d
  have he := congrArg e hH
  rw [map_mul, e.commutes, e.commutes] at he
  exact congrArg Subtype.val he

private theorem integral_pi_of_integral
    {R I : Type*} [CommRing R] [Finite I]
    (L : I → Type*) [∀ i, CommRing (L i)] [∀ i, Algebra R (L i)]
    (x : ∀ i, L i) (hx : ∀ i, IsIntegral R (x i)) : IsIntegral R x := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose p hp he using hx
  refine ⟨∏ i, p i, Polynomial.monic_prod_of_monic _ _ (fun i _ ↦ hp i), ?_⟩
  ext i
  change (Pi.evalRingHom L i) (Polynomial.eval₂ _ x (∏ j, p j)) = 0
  rw [Polynomial.hom_eval₂]
  rw [Polynomial.eval₂_finsetProd]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (he i)

private theorem closure_pi_quotients
    {D I : Type*} [CommRing D] [Finite I]
    (P : I → Ideal D) [∀ i, (P i).IsPrime] :
    Nonempty ((integralClosure D (∀ i, FractionRing (D ⧸ P i))) ≃ₐ[D]
      (∀ i, integralClosure (D ⧸ P i) (FractionRing (D ⧸ P i)))) := by
  let L (i : I) := FractionRing (D ⧸ P i)
  let E (i : I) := integralClosure (D ⧸ P i) (L i)
  let f : integralClosure D (∀ i, L i) →ₐ[D] ∀ i, E i :=
    { toFun := fun x i ↦ ⟨x.val i, (x.property.map (Pi.evalAlgHom D L i)).tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  refine ⟨AlgEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  · intro y
    have hi (i : I) : IsIntegral D (y i).val := by
      have : Algebra.IsIntegral D (D ⧸ P i) :=
        Algebra.isIntegral_of_surjective Ideal.Quotient.mk_surjective
      exact isIntegral_trans (R := D) (y i).val (y i).property
    refine ⟨⟨fun i ↦ (y i).val, integral_pi_of_integral L _ hi⟩, ?_⟩
    rfl

private theorem fraction_pi_equiv
    (D : Type*) [CommRing D] [IsNoetherianRing D] [IsReduced D] :
    ∃ (t : ℕ) (q : Fin t ≃ {p : PrimeSpectrum D // p.asIdeal ∈ minimalPrimes D}),
      Nonempty (FractionRing D ≃ₐ[D]
        (∀ i : Fin t, FractionRing (D ⧸ (q i).val.asIdeal))) := by
  classical
  obtain ⟨t, q, _, _, hres, _, hmaps, hbij⟩ :=
    reduced_noetherian_total_ring_fractions (R := D)
  choose φ hφ using fun i ↦ (hmaps i).exists
  let f : FractionRing D →ₐ[D] ∀ i, Localization.AtPrime (q i).val.asIdeal :=
    { toRingHom := RingHom.pi φ
      commutes' := fun d ↦ funext fun i ↦ RingHom.congr_fun (hφ i) d }
  let e₀ := AlgEquiv.ofBijective f (hbij φ hφ)
  let e₁ (i : Fin t) : Localization.AtPrime (q i).val.asIdeal ≃ₐ[D]
      Ideal.ResidueField (q i).val.asIdeal :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom D _ _) (hres i)
  let e₂ (i : Fin t) : Ideal.ResidueField (q i).val.asIdeal ≃ₐ[D]
      FractionRing (D ⧸ (q i).val.asIdeal) :=
    (IsLocalization.algEquiv (nonZeroDivisors (D ⧸ (q i).val.asIdeal)) _ _).restrictScalars D
  exact ⟨t, q, ⟨e₀.trans (AlgEquiv.piCongrRight fun i ↦ (e₁ i).trans (e₂ i))⟩⟩

private theorem pi_split
    {D I : Type*} [CommRing D]
    (E : I → Type*) [∀ i, CommRing (E i)] [∀ i, Algebra D (E i)] (j : I) :
    ∃ e : (∀ i, E i) ≃ₐ[D] E j × (∀ i : {i // i ≠ j}, E i),
      ∀ x, (e x).1 = x j := by
  classical
  let e : (∀ i, E i) ≃+* E j × (∀ i : {i // i ≠ j}, E i) :=
    { toEquiv := Equiv.piSplitAt j E
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  exact ⟨AlgEquiv.ofRingEquiv (f := e) (fun _ ↦ rfl), fun _ ↦ rfl⟩

/-- Normalization commutes canonically with the given local weakly etale base change,
and every minimal-prime normalization splits off. The fraction-clearing equation fixes
the comparison: if `s * c = a` in `Frac(C)` with `s ≠ 0`, its value on `c ⊗ d`
is the element of `Q(D)` whose product with `f(s)` is `f(a) * d`.

Source: Greco, *Two theorems on excellent rings*, Lemma 5.5 proof, first two sentences,
printed p. 147; Stacks Project, Tags 092H, 092Q, 092W and 035P.
(blueprint: lem-exc-weakly-etale-normalization-tensor)

Proof:
1. Put `S = C \ {0}`, `T = D ⊗[C] Frac(C)` and `H = C' ⊗[C] D`.
   Flatness from `def-weil-pbc-ind-etale-algebra` preserves the injections given by
   multiplication by `s ∈ S` and by `C' → Frac(C)`
   (`def-weil-pbc-flat-ring-map`). Thus `f(S)` consists of nonzerodivisors,
   `T = f(S)⁻¹D` by `lem-weil-pbc-localization-base-change`, and the fraction
   criterion of `def-weil-pbc-module-localization` gives injections `D → T` and `H → T`.
2. Base change (`lem-exc-weakly-etale-ring-base-change-composition`) makes `T` weakly
   etale over `Frac(C)`. By `lem-weil-pbc-weak-etale-field`, it is reduced and each
   finitely generated subalgebra is finite etale. The injection `D → T` gives reducedness.
3. A nonzerodivisor `a` of `D` stays a nonzerodivisor in `T`, by clearing denominators.
   The finite etale subalgebra generated by `a/1` is a finite product of fields
   (`lem-sc-finite-etale-algebra-criterion`). Every coordinate of `a/1` is nonzero:
   otherwise its coordinate idempotent annihilates `a/1` in `T`. Coordinatewise inverses
   show it is a unit. The fraction maps `Q(D) → T` and `T → Q(D)` are inverse, so
   `T = Q(D)` canonically (`def-weil-pbc-module-localization`).
4. `lem-weil-pbc-integral-closure-finite-extension-normal`, with the identity extension
   of `Frac(C)`, makes `C'` a normal domain with fraction field `Frac(C)`.
   Base change makes `C' → H` weakly etale; no locality or domain condition on `H` is used.
5. Tensor balancing identifies `H ⊗[C'] Frac(C)` with `T` by
   `(c' ⊗ d) ⊗ k ↦ d ⊗ (c' * k)`, with inverse `d ⊗ k ↦ (1 ⊗ d) ⊗ k`.
   Both composites fix pure tensors by `lem-weil-pbc-algebra-tensor-pushout-universal-property`.
6. `lem-weil-pbc-weak-etale-integral-closure` now says `H` is integrally closed in
   this ring, hence in `T = Q(D)` under the injection of step 1.
7. `lem-weil-pbc-integral-base-change` makes `H` integral over `D`, so its image lies
   in `D'`. Conversely an element integral over `D` is integral over `H`, and step 6
   puts it in `H`. This gives the canonical equivalence. Its value on a pure tensor is
   `c' * d`; clearing any nonzero denominator of `c'` gives the displayed equation.
   Such denominators map to units of `Q(D)`, so the equation uniquely fixes the map.
8. `lem-weil-pbc-reduced-noetherian-total-ring-fractions` expresses `Q(D)` as the
   finite product of the fields `D_P` at its distinct minimal primes, with `P D_P = 0`.
   The fraction maps identify each `D_P` with `Frac(D/P)`
   (`def-weil-pbc-localization-at-prime`).
9. Projecting monic equations shows the integral closure in this product lies in the
   product of the closures `E_i`. Conversely, lift monic annihilating polynomials from
   every `D/P_i` to `D` and multiply them. The resulting monic polynomial annihilates
   the tuple, proving equality (`def-weil-pbc-integral-closure`, Stacks Tag 035P).
10. For the specified minimal prime select its coordinate and group all other factors
    into `F`. The coordinate maps give the asserted restriction on `D`. A single minimal
    prime gives the empty product for `F`, which is the zero ring.
-/
theorem weaklyEtale_normalization_tensor
    (C : Type u) [CommRing C] [IsNoetherianRing C] (hCuc : IsUniversallyCatenary C)
    [IsLocalRing C] [IsDomain C]
    [Module.Finite C (integralClosure C (FractionRing C))]
    (D : Type v) [CommRing D] [IsNoetherianRing D] [IsLocalRing D]
    [Algebra C D] [IsLocalHom (algebraMap C D)] [Algebra.WeaklyEtale C D] :
    IsReduced D ∧
      (∃ e : @AlgEquiv D
        (TensorProduct C (integralClosure C (FractionRing C)) D)
        (integralClosure D (Localization (nonZeroDivisors D))) _ _ _
        (Algebra.TensorProduct.rightAlgebra) (inferInstance),
        ∀ (c : integralClosure C (FractionRing C)) (a s : C), s ≠ 0 →
          algebraMap C (FractionRing C) s * c.val = algebraMap C (FractionRing C) a →
          ∀ d : D,
            algebraMap D (Localization (nonZeroDivisors D)) (algebraMap C D s) *
                (e (c ⊗ₜ[C] d)).val =
              algebraMap D (Localization (nonZeroDivisors D)) (algebraMap C D a * d)) ∧
      ∀ (P : Ideal D), P ∈ Ideal.minimalPrimes (⊥ : Ideal D) →
        ∃ (F : CommRingCat.{v}) (A : Algebra D F),
          ∃ (e : @AlgEquiv D
            (integralClosure D (Localization (nonZeroDivisors D)))
            ((integralClosure (D ⧸ P) (FractionRing (D ⧸ P))) × F)
            _ _ _
            inferInstance
            (RingHom.toAlgebra
              (RingHom.prod
                ((@algebraMap (D ⧸ P) (integralClosure (D ⧸ P) (FractionRing (D ⧸ P))) _ _
                  (SubalgebraClass.toAlgebra (integralClosure (D ⧸ P) (FractionRing (D ⧸ P))))).comp
                  (Ideal.Quotient.mk P))
                (@algebraMap D F _ _ A)))),
            ∀ (d : D),
              (e (algebraMap D (integralClosure D (Localization (nonZeroDivisors D))) d)).1 =
                (@algebraMap (D ⧸ P) (integralClosure (D ⧸ P) (FractionRing (D ⧸ P))) _ _
                  (SubalgebraClass.toAlgebra (integralClosure (D ⧸ P) (FractionRing (D ⧸ P)))))
                  (Ideal.Quotient.mk P d)
  := by
    classical
    have _hCuc := hCuc
    have hred : IsReduced D := (generic_fractions C D).2
    refine ⟨hred, normalization_comparison C D, ?_⟩
    intro P hP
    let p : {p : PrimeSpectrum D // p.asIdeal ∈ minimalPrimes D} :=
      ⟨⟨P, hP.isPrime⟩, hP⟩
    obtain ⟨t, q, ⟨eQ⟩⟩ := fraction_pi_equiv D
    obtain ⟨j, hj⟩ := q.surjective p
    have hPj : (q j).val.asIdeal = P := congrArg (fun x ↦ x.val.asIdeal) hj
    subst P
    let E (i : Fin t) :=
      integralClosure (D ⧸ (q i).val.asIdeal) (FractionRing (D ⧸ (q i).val.asIdeal))
    obtain ⟨eN⟩ := closure_pi_quotients (fun i ↦ (q i).val.asIdeal)
    obtain ⟨es, hes⟩ := pi_split (D := D) (fun i ↦ (E i : Type v)) j
    let F := CommRingCat.of (∀ i : {i : Fin t // i ≠ j}, E i)
    let A : Algebra D F := inferInstance
    let e := eQ.mapIntegralClosure.trans (eN.trans es)
    refine ⟨F, A, ?_⟩
    let er := e.toRingEquiv
    let B : Type v := integralClosure D (FractionRing D)
    have hecomm (d : D) :
        er (algebraMap D B d) = (algebraMap D (E j) d, algebraMap D F d) :=
      e.commutes d
    let T := (E j) × F
    let : Algebra D T :=
      RingHom.toAlgebra
        (RingHom.prod
          ((algebraMap (D ⧸ (q j).val.asIdeal) (E j)).comp
            (Ideal.Quotient.mk (q j).val.asIdeal))
          (algebraMap D F))
    let e' : B ≃ₐ[D] T := by
      refine { er with commutes' := ?_ }
      intro d
      exact hecomm d
    exact ⟨e', fun d ↦ congrArg Prod.fst (hecomm d)⟩

end
