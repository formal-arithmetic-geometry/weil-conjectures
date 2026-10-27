module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.Algebra.Field.Shrink
import WeilConjectures.RingTheory.DvrGaloisNormalizationRamificationDvd
import WeilConjectures.RingTheory.DvrTameTensorFactorUnramified
import Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion

/-! # Normalized Galois tensor factors are étale at a tame boundary

Source: ILO, Travaux de Gabber, IX Proposition 2.1(i), printed pp.133–134;
Stacks Project, Tags 09EB, 0BRM, 032L, 0307, 00FP, 00RT and 08WD.
(blueprint: lem-sfb-kummer-normalization-boundary-etale)
-/

@[expose] public section

universe uR uB uK uE uL uF uJ uI

open scoped TensorProduct

namespace RingTheory

private theorem tensor_field_factor
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {J : Type*} [Finite J] (L : J → Type*)
    [∀ j, Field (L j)] [∀ j, Algebra K (L j)]
    {I : Type*} (F : I → Type*) [∀ a, Field (F a)] [∀ a, Algebra E (F a)]
    (decomposition : @AlgEquiv E (∀ j, L j ⊗[K] E) (∀ a, F a) _ _ _
      (@Pi.algebra J E (fun j ↦ L j ⊗[K] E) _ _
        (fun _ ↦ Algebra.TensorProduct.rightAlgebra)) _) (a : I) :
    ∃ (j : J) (f : L j →+* F a),
      (∀ k : K, f (algebraMap K (L j) k) =
        algebraMap E (F a) (algebraMap K E k)) ∧
      Algebra.adjoin E (Set.range f) = ⊤ := by
  classical
  let : ∀ j, Algebra E (L j ⊗[K] E) := fun _ ↦ Algebra.TensorProduct.rightAlgebra
  let φ : (∀ j, L j ⊗[K] E) →ₐ[E] F a :=
    (Pi.evalAlgHom E F a).comp decomposition.toAlgHom
  have hφ : Function.Surjective φ :=
    (show Function.Surjective (Pi.evalAlgHom E F a) from
      fun z ↦ ⟨Function.update 0 a z, by simp⟩).comp decomposition.surjective
  let p := RingHom.ker φ.toRingHom
  have hp : p.IsPrime := RingHom.ker_isPrime φ.toRingHom
  obtain ⟨j, P, hP⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (⟨p, hp⟩ : PrimeSpectrum (∀ j, L j ⊗[K] E))
  let ev : (∀ j, L j ⊗[K] E) →ₐ[E] L j ⊗[K] E := Pi.evalAlgHom E _ j
  have hev : Function.Surjective ev := fun z ↦ ⟨Function.update 0 j z, by simp [ev]⟩
  have hker : RingHom.ker ev.toRingHom ≤ RingHom.ker φ.toRingHom := by
    have he : P.asIdeal.comap (Pi.evalRingHom (fun j ↦ L j ⊗[K] E) j) = p :=
      congrArg PrimeSpectrum.asIdeal hP
    intro x hx
    change x ∈ p
    rw [← he]
    change ev x ∈ P.asIdeal
    rw [show ev x = 0 from hx]
    exact P.asIdeal.zero_mem
  let β := AlgHom.liftOfSurjective ev hev φ hker
  have hβ : Function.Surjective β :=
    AlgHom.liftOfSurjective_surjective ev hev φ hker hφ
  let f : L j →+* F a := β.toRingHom.comp
    (Algebra.TensorProduct.includeLeft : L j →ₐ[K] L j ⊗[K] E).toRingHom
  refine ⟨j, f, ?_, ?_⟩
  · intro k
    change β (algebraMap K (L j) k ⊗ₜ[K] (1 : E)) = _
    have hbal : algebraMap K (L j) k ⊗ₜ[K] (1 : E) =
        (1 : L j) ⊗ₜ[K] algebraMap K E k := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
    rw [hbal]
    exact β.commutes (algebraMap K E k)
  · apply top_unique
    intro z hz
    clear hz
    obtain ⟨x, rfl⟩ := hβ z
    induction x using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using (Algebra.adjoin E (Set.range f)).zero_mem
    | tmul l e =>
      have hl : f l ∈ Algebra.adjoin E (Set.range f) := Algebra.subset_adjoin ⟨l, rfl⟩
      have he := (Algebra.adjoin E (Set.range f)).algebraMap_mem e
      convert (Algebra.adjoin E (Set.range f)).mul_mem hl he using 1
      change β (l ⊗ₜ[K] e) = β (l ⊗ₜ[K] 1) * algebraMap E (F a) e
      rw [← β.commutes, ← map_mul]
      congr 1
      change l ⊗ₜ[K] e = (l ⊗ₜ[K] 1) * (1 ⊗ₜ[K] e)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => simpa only [map_add] using
        (Algebra.adjoin E (Set.range f)).add_mem hx hy

private theorem tame_compositum_unramified_same
    (V A L : Type uR) (F : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra V A] [Module.Finite V A] [FaithfulSMul V A]
    [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] [IsGalois (FractionRing V) L]
    [Field F] [Algebra A F] [Module.Finite A (integralClosure A F)]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : V))
    (hd : Module.finrank (FractionRing V) L ∣ n)
    (hindex : (IsLocalRing.maximalIdeal V).map (algebraMap V A) =
      IsLocalRing.maximalIdeal A ^ n) :
    let : Algebra V L := ((algebraMap (FractionRing V) L).comp
      (algebraMap V (FractionRing V))).toAlgebra
    ∀ (iL : L →+* F),
    (∀ v : V, iL (algebraMap V L v) = algebraMap A F (algebraMap V A v)) →
    Algebra.adjoin A (Set.range iL) = ⊤ →
    ∀ (Q : Ideal (integralClosure A F)) [Q.IsPrime],
      Q.comap (algebraMap A (integralClosure A F)) = IsLocalRing.maximalIdeal A →
      Algebra.FormallyUnramified A (Localization.AtPrime Q) := by
  let : Algebra V L := ((algebraMap (FractionRing V) L).comp
    (algebraMap V (FractionRing V))).toAlgebra
  dsimp only
  intro iL hcomm hgen Q hQ hclosed
  let : Algebra V F := ((algebraMap A F).comp (algebraMap V A)).toAlgebra
  have : IsScalarTower V A F := .of_algebraMap_eq' rfl
  let fL : L →ₐ[V] F := ⟨iL, hcomm⟩
  let φ : L ⊗[V] A →ₐ[V] F := Algebra.TensorProduct.lift fL
    (IsScalarTower.toAlgHom V A F) (fun _ _ ↦ Commute.all _ _)
  let : Algebra A (L ⊗[V] A) := Algebra.TensorProduct.rightAlgebra
  let φA : L ⊗[V] A →ₐ[A] F :=
    { φ with
      commutes' := fun a ↦ by
        change φ ((1 : L) ⊗ₜ[V] a) = _
        simp [φ] }
  have hφ : Function.Surjective φ := by
    have hle : Algebra.adjoin A (Set.range iL) ≤ φA.range := by
      apply Algebra.adjoin_le
      rintro _ ⟨l, rfl⟩
      exact ⟨l ⊗ₜ[V] 1, by simp [φA, φ, fL]⟩
    intro z
    exact hle (hgen ▸ (show z ∈ (⊤ : Subalgebra A F) from trivial))
  let P := RingHom.ker φ.toRingHom
  have hP : P.IsMaximal := RingHom.ker_isMaximal_of_surjective φ.toRingHom hφ
  let := hP
  let F' := (L ⊗[V] A) ⧸ P
  let alpha : A →+* F' := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[V] L ⊗[V] A).toRingHom
  let : Algebra A F' := alpha.toAlgebra
  let e : F' ≃ₐ[A] F :=
    { Ideal.quotientKerAlgEquivOfSurjective hφ with
      commutes' := fun a ↦ by
        change φ ((1 : L) ⊗ₜ[V] a) = algebraMap A F a
        simp [φ, fL] }
  let ec := e.mapIntegralClosure
  let Q' := Q.comap ec.toRingHom
  have : Q'.IsPrime := Ideal.comap_isPrime _ Q
  have hc : Q'.comap (algebraMap A (integralClosure A F')) =
      IsLocalRing.maximalIdeal A := by
    rw [Ideal.comap_comap]
    have hec : ec.toRingHom.comp (algebraMap A (integralClosure A F')) =
        algebraMap A (integralClosure A F) := by
      apply RingHom.ext
      intro a
      exact ec.commutes a
    rw [hec]
    exact hclosed
  have : Module.Finite A (integralClosure A F') :=
    Module.Finite.equiv ec.symm.toLinearEquiv
  have hur := dvr_tame_tensor_factor_formallyUnramified V n hn hunit A hindex L
    ⟨inferInstance, inferInstance⟩
    (dvr_galois_normalization_ramification_dvd V L n ⟨inferInstance, inferInstance, hd⟩)
    P hP inferInstance Q' inferInstance hc
  have : Algebra.FormallyUnramified A (Localization.AtPrime Q') := hur
  let el := Localization.localAlgEquiv Q' Q ec rfl
  exact Algebra.FormallyUnramified.of_equiv el

private theorem tame_compositum_unramified
    (V : Type uR) (A L F : Type*)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra V A] [Module.Finite V A] [FaithfulSMul V A]
    [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] [IsGalois (FractionRing V) L]
    [Field F] [Algebra A F] [Module.Finite A (integralClosure A F)]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : V))
    (hd : Module.finrank (FractionRing V) L ∣ n)
    (hindex : (IsLocalRing.maximalIdeal V).map (algebraMap V A) =
      IsLocalRing.maximalIdeal A ^ n) :
    let : Algebra V L := ((algebraMap (FractionRing V) L).comp
      (algebraMap V (FractionRing V))).toAlgebra
    ∀ (iL : L →+* F),
    (∀ v : V, iL (algebraMap V L v) = algebraMap A F (algebraMap V A v)) →
    Algebra.adjoin A (Set.range iL) = ⊤ →
    ∀ (Q : Ideal (integralClosure A F)) [Q.IsPrime],
      Q.comap (algebraMap A (integralClosure A F)) = IsLocalRing.maximalIdeal A →
      Algebra.FormallyUnramified A (Localization.AtPrime Q) := by
  classical
  let : Algebra V L := ((algebraMap (FractionRing V) L).comp
    (algebraMap V (FractionRing V))).toAlgebra
  dsimp only
  intro iL hcomm hgen Q hQ hclosed
  have : Small.{uR} A := Module.Finite.small V A
  have : Small.{uR} L := Module.Finite.small (FractionRing V) L
  let A' := Shrink.{uR} A
  let L' := Shrink.{uR} L
  obtain ⟨eA⟩ : Nonempty (A' ≃ₐ[V] A) := ⟨Shrink.algEquiv V A⟩
  obtain ⟨eL⟩ : Nonempty (L' ≃ₐ[FractionRing V] L) :=
    ⟨Shrink.algEquiv (FractionRing V) L⟩
  have : IsDiscreteValuationRing A' :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eA.symm.toRingEquiv
  have : FaithfulSMul V A' :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr fun x y h ↦
      FaithfulSMul.algebraMap_injective V A (by simpa using congrArg eA h)
  have : IsGalois (FractionRing V) L' := IsGalois.of_algEquiv eL.symm
  let : Algebra A' F := ((algebraMap A F).comp eA.toRingHom).toAlgebra
  have hindex' : (IsLocalRing.maximalIdeal V).map (algebraMap V A') =
      IsLocalRing.maximalIdeal A' ^ n := by
    suffices hh : ((IsLocalRing.maximalIdeal V).map (algebraMap V A')).map eA.toRingHom =
        (IsLocalRing.maximalIdeal A' ^ n).map eA.toRingHom by
      exact (Ideal.comap_map_of_bijective _ eA.bijective).symm.trans
        ((congrArg (Ideal.comap eA.toRingHom) hh).trans
          (Ideal.comap_map_of_bijective _ eA.bijective))
    rw [Ideal.map_map, show eA.toRingHom.comp (algebraMap V A') = algebraMap V A
      from eA.toAlgHom.comp_algebraMap, hindex, Ideal.map_pow,
      show (IsLocalRing.maximalIdeal A').map eA.toRingHom =
        IsLocalRing.maximalIdeal A from IsLocalRing.map_ringEquiv_maximalIdeal eA.toRingEquiv]
  have hint (z : F) : IsIntegral A' z ↔ IsIntegral A z :=
    eA.toRingEquiv.isIntegral_iff rfl z
  let ec : integralClosure A' F ≃+* integralClosure A F :=
    { toFun := fun z ↦ ⟨z, (hint z).mp z.property⟩
      invFun := fun z ↦ ⟨z, (hint z).mpr z.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let : Algebra A' (integralClosure A F) :=
    ((algebraMap A (integralClosure A F)).comp eA.toRingHom).toAlgebra
  let ecA : integralClosure A' F ≃ₐ[A'] integralClosure A F :=
    { ec with commutes' := fun _ ↦ rfl }
  have : Module.Finite A' (integralClosure A F) :=
    Module.Finite.of_equiv_equiv eA.symm.toRingEquiv (RingEquiv.refl (integralClosure A F)) (by
      apply RingHom.ext
      intro a
      apply Subtype.ext
      exact congrArg (algebraMap A F) (eA.apply_symm_apply a))
  have : Module.Finite A' (integralClosure A' F) := Module.Finite.equiv ecA.symm.toLinearEquiv
  let Q' := Q.comap ec.toRingHom
  have : Q'.IsPrime := Ideal.comap_isPrime _ Q
  have hclosed' : Q'.comap (algebraMap A' (integralClosure A' F)) =
      IsLocalRing.maximalIdeal A' := by
    rw [Ideal.comap_comap]
    change (Q.comap ((algebraMap A (integralClosure A F)).comp eA.toRingHom)) = _
    rw [← Ideal.comap_comap, hclosed]
    exact (congrArg (Ideal.comap eA.toRingHom)
      (IsLocalRing.map_ringEquiv_maximalIdeal eA.toRingEquiv)).symm.trans
        (Ideal.comap_map_of_bijective eA.toRingHom eA.bijective)
  let iL' : L' →+* F := iL.comp eL.toRingHom
  have hcomm' : ∀ v : V, iL' (algebraMap V L' v) =
      algebraMap A' F (algebraMap V A' v) := by
    intro v
    change iL (eL (algebraMap (FractionRing V) L' (algebraMap V (FractionRing V) v))) = _
    rw [eL.commutes]
    change iL (algebraMap V L v) = _
    rw [hcomm, ← eA.commutes]
    rfl
  have hgen' : Algebra.adjoin A' (Set.range iL') = ⊤ := by
    let S := Algebra.adjoin A' (Set.range iL')
    let SA : Subalgebra A F :=
      { S.toSubring with
        algebraMap_mem' := fun a ↦ by
          have hm := S.algebraMap_mem (eA.symm a)
          change algebraMap A F (eA (eA.symm a)) ∈ S at hm
          change algebraMap A F a ∈ S
          simpa only [eA.apply_symm_apply] using hm }
    have hle : Algebra.adjoin A (Set.range iL) ≤ SA := by
      apply Algebra.adjoin_le
      rintro _ ⟨l, rfl⟩
      have hm : iL' (eL.symm l) ∈ S := Algebra.subset_adjoin ⟨_, rfl⟩
      change iL (eL (eL.symm l)) ∈ S at hm
      change iL l ∈ S
      simpa only [eL.apply_symm_apply] using hm
    apply top_unique
    intro z _
    exact hle (hgen ▸ (show z ∈ (⊤ : Subalgebra A F) from trivial))
  have hd' : Module.finrank (FractionRing V) L' ∣ n := by
    simpa only [eL.toLinearEquiv.finrank_eq] using hd
  have hur := tame_compositum_unramified_same V A' L' F n hn hunit hd' hindex'
    iL' hcomm' hgen' Q' hclosed'
  let el := Localization.localRingEquiv Q' Q ec rfl
  have : Algebra.FormallyUnramified A' (Localization.AtPrime Q') := hur
  let elA : Localization.AtPrime Q' ≃ₐ[A'] Localization.AtPrime Q :=
    { el with
      commutes' := fun a ↦ by
        change el (algebraMap _ _ (algebraMap A' (integralClosure A' F) a)) = _
        change Localization.localRingHom Q' Q ec.toRingHom rfl
          (algebraMap _ _ (algebraMap A' (integralClosure A' F) a)) = _
        rw [Localization.localRingHom_to_map]
        rfl }
  have : Algebra.FormallyUnramified A' (Localization.AtPrime Q) :=
    .of_equiv elA
  have hcomp : RingHom.FormallyUnramified
      ((algebraMap A (Localization.AtPrime Q)).comp eA.toRingHom) := by
    exact (RingHom.formallyUnramified_algebraMap (R := A')
      (S := Localization.AtPrime Q)).mpr inferInstance
  have hf := (RingHom.FormallyUnramified.of_surjective
    (f := eA.symm.toRingHom) eA.symm.surjective).comp hcomp
  have heq : ((algebraMap A (Localization.AtPrime Q)).comp eA.toRingHom).comp
      eA.symm.toRingHom = algebraMap A (Localization.AtPrime Q) := by
    apply RingHom.ext
    intro a
    simp
  rw [heq, RingHom.formallyUnramified_algebraMap] at hf
  exact hf

private theorem adjoin_over_finite_dvr_extension
    {V A K E L F : Type*}
    [CommRing V] [IsDomain V] [CommRing A] [IsDomain A]
    [Algebra V A] [Module.Finite V A] [FaithfulSMul V A]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field E] [Algebra A E] [IsFractionRing A E] [Algebra K E]
    [Field L] [Algebra K L]
    [Field F] [Algebra A F] [Algebra E F] [IsScalarTower A E F]
    (hcompat : (algebraMap K E).comp (algebraMap V K) =
      (algebraMap A E).comp (algebraMap V A))
    (iL : L →+* F)
    (hcomm : ∀ k : K, iL (algebraMap K L k) =
      algebraMap E F (algebraMap K E k))
    (hgen : Algebra.adjoin E (Set.range iL) = ⊤) :
    Algebra.adjoin A (Set.range iL) = ⊤ := by
  let S := Algebra.adjoin A (Set.range iL)
  have hE (e : E) : algebraMap E F e ∈ S := by
    obtain ⟨⟨a, d⟩, he⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors V)) e
    obtain ⟨v, hv, hd⟩ := d.property
    have hinv : algebraMap E F
        ((algebraMap A E (algebraMap V A v))⁻¹) ∈ S := by
      have hc := RingHom.congr_fun hcompat v
      simp only [RingHom.comp_apply] at hc
      rw [← hc, ← map_inv₀, ← hcomm]
      exact Algebra.subset_adjoin ⟨_, rfl⟩
    have hden : algebraMap A E (algebraMap V A v) ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective A E).ne
        ((FaithfulSMul.algebraMap_injective V A).ne (nonZeroDivisors.ne_zero hv))
    have heq : algebraMap E F e = algebraMap A F a *
        algebraMap E F ((algebraMap A E (algebraMap V A v))⁻¹) := by
      rw [IsScalarTower.algebraMap_apply A E F, ← map_mul]
      congr 1
      rw [← he, ← hd, mul_assoc, mul_inv_cancel₀ hden, mul_one]
    rw [heq]
    exact S.mul_mem (S.algebraMap_mem a) hinv
  let SE : Subalgebra E F := { S.toSubring with algebraMap_mem' := hE }
  have hle : Algebra.adjoin E (Set.range iL) ≤ SE := by
    apply Algebra.adjoin_le
    intro z hz
    change z ∈ S
    exact Algebra.subset_adjoin hz
  apply top_unique
  intro z _
  exact hle (hgen ▸ (show z ∈ (⊤ : Subalgebra E F) from trivial))

private theorem normalization_local_unramified
    {B E F : Type*} [CommRing B] [IsDomain B]
    [Field E] [Algebra B E] [IsFractionRing B E]
    [Field F] [Algebra B F] [Algebra E F] [IsScalarTower B E F]
    (q : Ideal B) [q.IsPrime]
    [Algebra (Localization.AtPrime q) E] [IsScalarTower B (Localization.AtPrime q) E]
    [Algebra (Localization.AtPrime q) F]
    [IsScalarTower B (Localization.AtPrime q) F]
    (hur : ∀ (P : Ideal (integralClosure (Localization.AtPrime q) F)) [P.IsPrime],
      P.comap (algebraMap (Localization.AtPrime q)
        (integralClosure (Localization.AtPrime q) F)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) →
      Algebra.FormallyUnramified (Localization.AtPrime q) (Localization.AtPrime P))
    (Q : Ideal (integralClosure B F)) [Q.IsPrime]
    (hQ : q = Q.comap (algebraMap B (integralClosure B F))) :
    RingHom.FormallyUnramified
      (Localization.localRingHom q Q (algebraMap B (integralClosure B F)) hQ) := by
  let A := Localization.AtPrime q
  let C := integralClosure B F
  let S := integralClosure A F
  let iC : C →+* S :=
    { toFun := fun c ↦ ⟨c, c.property.tower_top⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  let : Algebra C S := iC.toAlgebra
  have : IsScalarTower C S F := .of_algebraMap_eq' rfl
  have : IsScalarTower B C S := .of_algebraMap_eq' rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid F q.primeCompl) F :=
    IsLocalization.of_le_isUnit (by
      rintro _ ⟨b, hb, rfl⟩
      apply isUnit_iff_ne_zero.mpr
      rw [IsScalarTower.algebraMap_apply B E F]
      simpa only [map_zero] using (algebraMap E F).injective.ne
        ((IsFractionRing.injective B E).ne
          (nonZeroDivisors.ne_zero (q.primeCompl_le_nonZeroDivisors hb))))
  let M := Algebra.algebraMapSubmonoid C q.primeCompl
  have : IsLocalization M S := IsLocalization.integralClosure
    (S := F) (Rf := A) (Sf := F) q.primeCompl
  have hdis : Disjoint (M : Set C) (Q : Set C) := by
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ hmem
    exact hb (show b ∈ q from hQ ▸ hmem)
  let P := Q.map (algebraMap C S)
  have : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S Q inferInstance hdis
  have hc : P.comap (algebraMap C S) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M S inferInstance hdis
  have hp : P.comap (algebraMap A S) = IsLocalRing.maximalIdeal A := by
    apply Localization.AtPrime.eq_maximalIdeal_iff_under_eq.mp
    change (P.comap (algebraMap A S)).comap (algebraMap B A) = q
    rw [Ideal.comap_comap]
    rw [← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq B C S,
      ← Ideal.comap_comap, hc]
    exact hQ.symm
  let T := Localization.AtPrime P
  have : IsLocalization.AtPrime T Q := by
    change IsLocalization Q.primeCompl T
    simpa only [hc] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M T P)
  let e := IsLocalization.algEquiv Q.primeCompl T (Localization.AtPrime Q)
  let f := Localization.localRingHom q Q (algebraMap B C) hQ
  let : Algebra A (Localization.AtPrime Q) := f.toAlgebra
  have htower : IsScalarTower B A (Localization.AtPrime Q) :=
    .of_algebraMap_eq fun b ↦ (Localization.localRingHom_to_map q Q _ hQ b).symm
  let eA : T ≃ₐ[A] Localization.AtPrime Q :=
    { e.toRingEquiv with
      commutes' := fun a ↦ by
        have he : e.toRingHom.comp (algebraMap A T) = algebraMap A (Localization.AtPrime Q) := by
          apply IsLocalization.ringHom_ext q.primeCompl
          apply RingHom.ext
          intro b
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply B A T,
            ← IsScalarTower.algebraMap_apply B A (Localization.AtPrime Q)]
          change e (algebraMap C T (algebraMap B C b)) = _
          rw [e.commutes]
          rfl
        exact RingHom.congr_fun he a }
  have : Algebra.FormallyUnramified A T := hur P hp
  exact Algebra.FormallyUnramified.of_equiv eA

private theorem flat_localRingHom_of_domain
    {B C : Type*} [CommRing B] [IsDomain B] [CommRing C] [IsDomain C]
    [Algebra B C] (hinj : Function.Injective (algebraMap B C))
    (q : Ideal B) [q.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime q)]
    (Q : Ideal C) [Q.IsPrime] (hQ : q = Q.comap (algebraMap B C)) :
    RingHom.Flat (Localization.localRingHom q Q (algebraMap B C) hQ) := by
  let f := Localization.localRingHom q Q (algebraMap B C) hQ
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime Q) := f.toAlgebra
  have hf : Function.Injective f := by
    exact IsLocalization.map_injective_of_injective' q.primeCompl
      (S := C) (Localization.AtPrime Q)
      (fun x hx ↦ by simpa only [Submonoid.mem_comap, Ideal.mem_primeCompl_iff,
        ← Ideal.mem_comap, ← hQ] using hx) (by simp) hinj
  have : FaithfulSMul (Localization.AtPrime q) (Localization.AtPrime Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  have : Module.IsTorsionFree (Localization.AtPrime q) (Localization.AtPrime Q) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hf
  exact inferInstanceAs (Module.Flat (Localization.AtPrime q) (Localization.AtPrime Q))

private theorem pi_boundary_local_properties
    {B : Type*} [CommRing B] (I : Type*) [Finite I] (C : I → Type*)
    [∀ i, CommRing (C i)] [∀ i, Algebra B (C i)]
    (q : Ideal B) [q.IsPrime]
    (hflat : ∀ (i : I) (P : Ideal (C i)) [P.IsPrime]
      (hP : q = P.comap (algebraMap B (C i))),
      RingHom.Flat (Localization.localRingHom q P (algebraMap B (C i)) hP))
    (hur : ∀ (i : I) (P : Ideal (C i)) [P.IsPrime]
      (hP : q = P.comap (algebraMap B (C i))),
      (Localization.localRingHom q P (algebraMap B (C i)) hP).FormallyUnramified)
    (Q : Ideal (∀ i, C i)) [Q.IsPrime]
    (hQ : q = Q.comap (algebraMap B (∀ i, C i))) :
    RingHom.Flat (Localization.localRingHom q Q (algebraMap B (∀ i, C i)) hQ) ∧
      Subsingleton (LocalizedModule Q.primeCompl (KaehlerDifferential B (∀ i, C i))) := by
  classical
  obtain ⟨i, P, he⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq (⟨Q, inferInstance⟩ : PrimeSpectrum (∀ i, C i))
  have he' : P.asIdeal.comap (Pi.evalRingHom C i) = Q :=
    congrArg PrimeSpectrum.asIdeal he
  have hP : q = P.asIdeal.comap (algebraMap B (C i)) := by
    rw [hQ, ← he', Ideal.comap_comap]
    rfl
  let e := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom P.asIdeal)
    (Localization.AtPrime.mapPiEvalRingHom_bijective P.asIdeal)
  subst Q
  let f := Localization.localRingHom q P.asIdeal (algebraMap B (C i)) hP
  let g := Localization.localRingHom q (P.asIdeal.comap (Pi.evalRingHom C i))
    (algebraMap B (∀ i, C i)) hQ
  have hcomp : e.toRingHom.comp g = f := by
    apply IsLocalization.ringHom_ext q.primeCompl
    ext b
    change e (g (algebraMap B (Localization.AtPrime q) b)) =
      f (algebraMap B (Localization.AtPrime q) b)
    rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map]
    change Localization.AtPrime.mapPiEvalRingHom P.asIdeal
      (algebraMap _ _ (algebraMap B (∀ i, C i) b)) = _
    rw [Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply]
    rfl
  have hgf : g = e.symm.toRingHom.comp f := by
    ext x
    apply e.injective
    exact (RingHom.congr_fun hcomp x).trans (e.apply_symm_apply (f x)).symm
  refine ⟨?_, ?_⟩
  · rw [show Localization.localRingHom q _ _ hQ = g from rfl, hgf]
    exact (hflat i P.asIdeal hP).comp (RingHom.Flat.of_bijective e.symm.bijective)
  · have hgu : g.FormallyUnramified := by
      rw [hgf]
      exact (hur i P.asIdeal hP).comp
        (RingHom.FormallyUnramified.of_surjective e.symm.surjective)
    let T := Localization.AtPrime (P.asIdeal.comap (Pi.evalRingHom C i))
    let : Algebra (Localization.AtPrime q) T := g.toAlgebra
    have : IsScalarTower B (Localization.AtPrime q) T :=
      .of_algebraMap_eq fun b ↦
        (Localization.localRingHom_to_map q _ _ hQ b).symm
    have : Algebra.FormallyUnramified (Localization.AtPrime q) T := hgu
    have : Algebra.FormallyUnramified B (Localization.AtPrime q) :=
      .of_isLocalization q.primeCompl
    have : Algebra.FormallyUnramified B T :=
      .comp B (Localization.AtPrime q) T
    exact (IsLocalizedModule.iso _ (KaehlerDifferential.map B B (∀ i, C i) T)).subsingleton

/-- Killing boundary ramification in all the normalized Galois tensor factors.
The explicit product algebra structure on the tensor side is Mathlib's right-hand
`E`-algebra structure, so the decomposition respects the specified field inclusions.
Differentials over the boundary DVR use the canonical map of prime localizations.
The affine étale neighbourhood is expressed by `Algebra.Etale B (Localization.Away g)`.

Source: ILO IX Proposition 2.1(i), pp.133–134; Stacks Tags 09EB, 0BRM, 032L,
0307, 00FP, 00RT and 08WD.
(blueprint: lem-sfb-kummer-normalization-boundary-etale)

Proof:
1. By lem-weil-pbc-noetherian-normal-separable-integral-closure-finite (032L),
   each integral closure is finite over B. Coordinatewise generators generate the
   finite product. Its module generators also generate it as an algebra, and
   lem-weil-pbc-finite-type-noetherian-finite-presentation (00FP) gives finite presentation.
2. Put V = R_p and A = B_q. The domain A tensor_V K is finite dimensional over K,
   hence a field, and therefore equals E. Thus L_j tensor_V A equals L_j tensor_K E.
   The given decomposition identifies each F_a with a maximal quotient of one tensor factor,
   with the specified A-structure.
3. By lem-weil-pbc-integral-closure-commutes-localization (0307), localizing C_a
   at B minus q gives the integral closure S_a of A in F_a, finite over A.
   A prime of C_a over q induces a prime of S_a over the maximal ideal of A;
   the two subsequent localizations are canonically the same A-algebra.
4. Apply lem-sbc-dvr-galois-normalization-ramification-dvd (09EB) to V and L_j.
   Its ramification and residue degrees divide n. The hypotheses on V to A and n
   therefore allow lem-sbc-dvr-tame-tensor-factor-unramified (0BRM) to give zero
   differentials at the localization of S_a. Step 3 gives the asserted factor vanishing.
5. Each localized C_a embeds in F_a, hence is torsion free over A. A DVR is a PID,
   so lem-weil-pbc-pid-torsion-free-module-flat gives flatness over A.
6. A prime of the finite product selects exactly one factor, by its orthogonal
   coordinate idempotents. Its local ring is the corresponding localized C_a, hence flat.
   By lem-weil-pbc-kahler-differentials-localization (00RT), localized differentials
   equal those of this local ring over B. A B-derivation annihilates inverses of
   elements outside q, by the Leibniz rule, so is an A-derivation. The universal
   property of differentials and step 4 give the second asserted vanishing.
7. Apply lem-sc-etale-at-prime-flat-unramified-criterion (08WD), using finite
   presentation, flatness and differential vanishing, to obtain g outside the prime.
   None of these steps requires excellence. -/
theorem kummer_normalization_boundary_etale
    (R : Type uR) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (B : Type uB) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    [Algebra R B] (hRB : Function.Injective (algebraMap R B))
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (E : Type uE) [Field E] [Algebra B E] [IsFractionRing B E] [Algebra K E]
    (hKE : (algebraMap K E).comp (algebraMap R K) =
      (algebraMap B E).comp (algebraMap R B))
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (J : Type uJ) [Finite J] [Nonempty J]
    (L : J → Type uL) [∀ j, Field (L j)] [∀ j, Algebra K (L j)]
    [∀ j, FiniteDimensional K (L j)] [∀ j, IsGalois K (L j)]
    (hdegree : ∀ j, Module.finrank K (L j) ∣ n)
    (I : Type uI) [Finite I] (F : I → Type uF) [∀ a, Field (F a)]
    [∀ a, Algebra E (F a)] [∀ a, FiniteDimensional E (F a)]
    [∀ a, Algebra.IsSeparable E (F a)] [∀ a, Algebra B (F a)]
    (hBF : ∀ a, algebraMap B (F a) = (algebraMap E (F a)).comp (algebraMap B E))
    (decomposition : @AlgEquiv E (∀ j, L j ⊗[K] E) (∀ a, F a) _ _ _
      (@Pi.algebra J E (fun j ↦ L j ⊗[K] E) _ _
        (fun _ ↦ Algebra.TensorProduct.rightAlgebra)) _)
    (q : Ideal B) [q.IsPrime]
    (hheight : q ≠ ⊥ ∧ ∀ r : Ideal B, r.IsPrime → r < q → r = ⊥)
    [IsDiscreteValuationRing (Localization.AtPrime (q.comap (algebraMap R B)))]
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    (hfinite : RingHom.Finite (Localization.localRingHom
      (q.comap (algebraMap R B)) q (algebraMap R B) rfl))
    (hinjective : Function.Injective (Localization.localRingHom
      (q.comap (algebraMap R B)) q (algebraMap R B) rfl))
    (hindex : (IsLocalRing.maximalIdeal
        (Localization.AtPrime (q.comap (algebraMap R B)))).map
          (Localization.localRingHom (q.comap (algebraMap R B)) q (algebraMap R B) rfl) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n) :
    Module.Finite B (∀ a, integralClosure B (F a)) ∧
    Algebra.FinitePresentation B (∀ a, integralClosure B (F a)) ∧
    (∀ (a : I) (Q : Ideal (integralClosure B (F a))) [Q.IsPrime]
      (hQ : q = Q.comap (algebraMap B (integralClosure B (F a)))),
      Subsingleton (@KaehlerDifferential (Localization.AtPrime q) (Localization.AtPrime Q)
        _ _ (Localization.localRingHom q Q (algebraMap B (integralClosure B (F a)))
          hQ).toAlgebra)) ∧
    (∀ (Q : Ideal (∀ a, integralClosure B (F a))) [Q.IsPrime]
      (hQ : q = Q.comap (algebraMap B (∀ a, integralClosure B (F a)))),
      RingHom.Flat (Localization.localRingHom q Q
        (algebraMap B (∀ a, integralClosure B (F a))) hQ) ∧
      Subsingleton (LocalizedModule Q.primeCompl
        (KaehlerDifferential B (∀ a, integralClosure B (F a)))) ∧
      ∃ g : (∀ a, integralClosure B (F a)), g ∉ Q ∧
        Algebra.Etale B (Localization.Away g)) := by
  have _ := hRB
  have hBEF (a : I) : IsScalarTower B E (F a) :=
    IsScalarTower.of_algebraMap_eq' (hBF a)
  let : ∀ a, IsScalarTower B E (F a) := hBEF
  have hfin (a : I) : Module.Finite B (integralClosure B (F a)) :=
    IsIntegralClosure.finite B E (F a) (integralClosure B (F a))
  let : ∀ a, Module.Finite B (integralClosure B (F a)) := hfin
  have hfinprod : Module.Finite B (∀ a, integralClosure B (F a)) := inferInstance
  have hfp : Algebra.FinitePresentation B (∀ a, integralClosure B (F a)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let p := q.comap (algebraMap R B)
  let V := Localization.AtPrime p
  let A := Localization.AtPrime q
  let vA := Localization.localRingHom p q (algebraMap R B) rfl
  let : Algebra V A := vA.toAlgebra
  have : Module.Finite V A := hfinite
  have : FaithfulSMul V A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjective
  let fVK := Localization.mapToFractionRing K p.primeCompl V
    p.primeCompl_le_nonZeroDivisors
  let : Algebra V K := fVK.toRingHom.toAlgebra
  have : IsScalarTower R V K :=
    .of_algebraMap_eq fun r ↦ (fVK.commutes r).symm
  have : IsFractionRing V K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl V K
  let fAE := Localization.mapToFractionRing E q.primeCompl A
    q.primeCompl_le_nonZeroDivisors
  let : Algebra A E := fAE.toRingHom.toAlgebra
  have : IsScalarTower B A E :=
    .of_algebraMap_eq fun b ↦ (fAE.commutes b).symm
  have : IsFractionRing A E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  have hcompat : (algebraMap K E).comp (algebraMap V K) =
      (algebraMap A E).comp (algebraMap V A) := by
    apply IsLocalization.ringHom_ext p.primeCompl
    apply RingHom.ext
    intro r
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R V K]
    change algebraMap K E (algebraMap R K r) = fAE (vA (algebraMap R V r))
    rw [Localization.localRingHom_to_map, fAE.commutes]
    exact RingHom.congr_fun hKE r
  obtain ⟨eK⟩ : Nonempty (FractionRing V ≃ₐ[V] K) :=
    ⟨IsLocalization.algEquiv (nonZeroDivisors V) (FractionRing V) K⟩
  have hnV : IsUnit (n : V) := by
    simpa only [map_natCast] using hnunit.map (algebraMap R V)
  have hindexV : (IsLocalRing.maximalIdeal V).map (algebraMap V A) =
      IsLocalRing.maximalIdeal A ^ n := hindex
  have hvan : ∀ (a : I) (Q : Ideal (integralClosure B (F a))) [Q.IsPrime]
      (hQ : q = Q.comap (algebraMap B (integralClosure B (F a)))),
      Subsingleton (@KaehlerDifferential (Localization.AtPrime q) (Localization.AtPrime Q)
        _ _ (Localization.localRingHom q Q (algebraMap B (integralClosure B (F a)))
          hQ).toAlgebra) := by
    intro a Q hprime hQ
    let : Algebra A (F a) := ((algebraMap E (F a)).comp (algebraMap A E)).toAlgebra
    have : IsScalarTower A E (F a) := .of_algebraMap_eq' rfl
    have : IsScalarTower B A (F a) := IsScalarTower.to₁₂₄ B A E (F a)
    have : Module.Finite A (integralClosure A (F a)) :=
      IsIntegralClosure.finite A E (F a) (integralClosure A (F a))
    obtain ⟨j, iL, hcomm, hgen⟩ := tensor_field_factor L F decomposition a
    have hgenA : Algebra.adjoin A (Set.range iL) = ⊤ :=
      adjoin_over_finite_dvr_extension (V := V) (A := A) (K := K) (E := E)
        hcompat iL hcomm hgen
    let : Algebra (FractionRing V) (L j) :=
      ((algebraMap K (L j)).comp eK.toRingHom).toAlgebra
    have heq : (algebraMap (FractionRing V) (L j)).comp eK.symm.toRingHom =
        (RingEquiv.refl (L j)).toRingHom.comp (algebraMap K (L j)) := by
      apply RingHom.ext
      intro k
      change algebraMap K (L j) (eK (eK.symm k)) = algebraMap K (L j) k
      rw [eK.apply_symm_apply]
    have : FiniteDimensional (FractionRing V) (L j) :=
      Module.Finite.of_equiv_equiv eK.symm.toRingEquiv (RingEquiv.refl (L j)) heq
    have : IsGalois (FractionRing V) (L j) :=
      IsGalois.of_equiv_equiv (F := K) (E := L j)
        (f := eK.symm.toRingEquiv) (g := RingEquiv.refl (L j)) heq
    have hd : Module.finrank (FractionRing V) (L j) ∣ n := by
      rw [← Algebra.finrank_eq_of_equiv_equiv eK.symm.toRingEquiv
        (RingEquiv.refl (L j)) heq]
      exact hdegree j
    have hur : ∀ (P : Ideal (integralClosure A (F a))) [P.IsPrime],
        P.comap (algebraMap A (integralClosure A (F a))) = IsLocalRing.maximalIdeal A →
        Algebra.FormallyUnramified A (Localization.AtPrime P) := by
      apply tame_compositum_unramified V A (L j) (F a) n hn hnV hd hindexV iL
      · intro v
        change iL (algebraMap K (L j) (eK (algebraMap V (FractionRing V) v))) = _
        rw [eK.commutes, hcomm]
        exact congrArg (algebraMap E (F a)) (RingHom.congr_fun hcompat v)
      · exact hgenA
    have hh := normalization_local_unramified (E := E) (F := F a) q hur Q hQ
    exact hh.1
  refine ⟨hfinprod, hfp, hvan, ?_⟩
  intro Q hprime hQ
  have hlocal := pi_boundary_local_properties I (fun a ↦ integralClosure B (F a)) q
    (fun a P _ hP ↦ flat_localRingHom_of_domain
      (by
        intro x y hxy
        apply IsFractionRing.injective B E
        apply (algebraMap E (F a)).injective
        rw [← IsScalarTower.algebraMap_apply B E (F a),
          ← IsScalarTower.algebraMap_apply B E (F a)]
        exact congrArg (fun z : integralClosure B (F a) ↦ (z : F a)) hxy) q P hP)
    (fun a P _ hP ↦ by
      let := (Localization.localRingHom q P
        (algebraMap B (integralClosure B (F a))) hP).toAlgebra
      exact ⟨hvan a P hP⟩) Q hQ
  refine ⟨hlocal.1, hlocal.2, ?_⟩
  subst q
  have hcrit := Algebra.isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler
    (R := B) Q
  exact hcrit.1.mp (hcrit.2.mpr hlocal)

end RingTheory
