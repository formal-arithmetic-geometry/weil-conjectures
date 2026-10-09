/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Fixed points of finite étale algebras

Let `A` be a finite étale `R`-algebra and `σ` a finite family of `R`-algebra endomorphisms of
`A`, e.g. the action of a finite group. We show that the subalgebra `A^σ` of common fixed
points is again finite étale over `R`, and compute its geometric points.

## Main definitions

- `AlgHom.fixedPoints`: the subalgebra of common fixed points of a family of endomorphisms.

## Main results

- `AlgHom.tensorFixedPointsEquiv`: base change along a flat algebra commutes with taking fixed
  points.

-/

@[expose] public section

universe u

open TensorProduct

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}

/-- The subalgebra of common fixed points of a family `σ` of `R`-algebra endomorphisms of `A`. -/
def fixedPoints (σ : ι → A →ₐ[R] A) : Subalgebra R A :=
  AlgHom.equalizer (AlgHom.pi σ) (AlgHom.pi fun _ ↦ AlgHom.id R A)

@[simp]
lemma mem_fixedPoints {σ : ι → A →ₐ[R] A} {a : A} : a ∈ fixedPoints σ ↔ ∀ i, σ i a = a := by
  simp [fixedPoints, AlgHom.mem_equalizer, funext_iff]

variable (T : Type*) [CommRing T] [Algebra R T]

/-- The base change `𝟙 ⊗ σᵢ` of a family of endomorphisms. -/
noncomputable abbrev baseChangeFamily (σ : ι → A →ₐ[R] A) : ι → T ⊗[R] A →ₐ[T] T ⊗[R] A :=
  fun i ↦ Algebra.TensorProduct.map (AlgHom.id T T) (σ i)

lemma equalizer_map_pi_eq_fixedPoints [_root_.Finite ι] (σ : ι → A →ₐ[R] A) :
    AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.pi σ))
      (Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.pi fun _ ↦ AlgHom.id R A)) =
      fixedPoints (baseChangeFamily T σ) := by
  classical
  cases nonempty_fintype ι
  have key (τ : ι → A →ₐ[R] A) (x : T ⊗[R] A) :
      Algebra.TensorProduct.piRight R T T (fun _ : ι ↦ A)
        (Algebra.TensorProduct.map (AlgHom.id T T) (AlgHom.pi τ) x) =
        fun i ↦ Algebra.TensorProduct.map (AlgHom.id T T) (τ i) x := by
    induction x with
    | zero => simp; rfl
    | tmul t a => ext i; simp
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
  ext x
  rw [AlgHom.mem_equalizer, mem_fixedPoints,
    ← (Algebra.TensorProduct.piRight R T T fun _ : ι ↦ A).injective.eq_iff, key, key, funext_iff]
  simp

/-- Base change along a flat algebra commutes with taking common fixed points of a finite family
of endomorphisms. -/
noncomputable def tensorFixedPointsEquiv [_root_.Finite ι] [Module.Flat R T] (σ : ι → A →ₐ[R] A) :
    T ⊗[R] fixedPoints σ ≃ₐ[T] fixedPoints (baseChangeFamily T σ) :=
  (AlgHom.tensorEqualizerEquiv T T _ _).trans
    (Subalgebra.equivOfEq _ _ (equalizer_map_pi_eq_fixedPoints T σ))

@[simp]
lemma coe_tensorFixedPointsEquiv_tmul [_root_.Finite ι] [Module.Flat R T] (σ : ι → A →ₐ[R] A)
    (t : T) (a : fixedPoints σ) :
    (tensorFixedPointsEquiv T σ (t ⊗ₜ a) : T ⊗[R] A) = t ⊗ₜ (a : A) :=
  rfl

section Conj

variable {A' : Type*} [CommRing A'] [Algebra R A']

/-- The conjugate `e ∘ σᵢ ∘ e⁻¹` of a family of endomorphisms by an algebra isomorphism. -/
def conjFamily (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) : ι → A' →ₐ[R] A' :=
  fun i ↦ (e : A →ₐ[R] A').comp ((σ i).comp (e.symm : A' →ₐ[R] A))

@[simp]
lemma conjFamily_apply (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) (i : ι) (a : A') :
    conjFamily e σ i a = e (σ i (e.symm a)) :=
  rfl

lemma fixedPoints_conjFamily (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) :
    fixedPoints (conjFamily e σ) = (fixedPoints σ).map (e : A →ₐ[R] A') := by
  ext a
  simp only [mem_fixedPoints, conjFamily_apply, Subalgebra.mem_map]
  constructor
  · intro h
    refine ⟨e.symm a, fun i ↦ ?_, by simp⟩
    rw [← e.injective.eq_iff, h, AlgEquiv.apply_symm_apply]
  · rintro ⟨b, hb, rfl⟩ i
    simp [hb]

/-- An algebra isomorphism identifies the fixed points of a family with the fixed points of its
conjugate. -/
noncomputable def fixedPointsCongr (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) :
    fixedPoints σ ≃ₐ[R] fixedPoints (conjFamily e σ) :=
  (e.subalgebraMap _).trans (Subalgebra.equivOfEq _ _ (fixedPoints_conjFamily e σ).symm)

@[simp]
lemma coe_fixedPointsCongr_apply (e : A ≃ₐ[R] A') (σ : ι → A →ₐ[R] A) (a : fixedPoints σ) :
    (fixedPointsCongr e σ a : A') = e a :=
  rfl

end Conj

end AlgHom

namespace Algebra

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Finite étale is local on the base: if every prime `p` of `R` has a basic open neighbourhood
`D(f)` over which `B` is finite étale, then `B` is finite étale over `R`. -/
theorem finite_and_etale_of_forall_exists_localizationAway
    (H : ∀ p : Ideal R, p.IsPrime → ∃ f ∉ p,
      Module.Finite (Localization.Away f) (Localization.Away f ⊗[R] B) ∧
        Algebra.Etale (Localization.Away f) (Localization.Away f ⊗[R] B)) :
    Module.Finite R B ∧ Algebra.Etale R B := by
  let s : Set R := {f | Module.Finite (Localization.Away f) (Localization.Away f ⊗[R] B) ∧
    Algebra.Etale (Localization.Away f) (Localization.Away f ⊗[R] B)}
  have hs : Ideal.span s = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hfs⟩ := H m hm.isPrime
    exact hf (hsm (Ideal.subset_span hfs))
  have hcomp (f : R) : (algebraMap (Localization.Away f) (Localization.Away f ⊗[R] B)).comp
      (algebraMap R (Localization.Away f)) =
      (algebraMap B (Localization.Away f ⊗[R] B)).comp (algebraMap R B) := by
    ext r
    simp [Algebra.algebraMap_eq_smul_one]
  constructor
  · rw [← RingHom.finite_algebraMap]
    refine RingHom.finite_ofLocalizationSpan.ofIsLocalization RingHom.finite_respectsIso _ s hs
      fun f ↦ ⟨Localization.Away f.1, Localization.Away f.1 ⊗[R] B, _, _, _, _, inferInstance,
        inferInstance,
        algebraMap _ _, hcomp f.1, ?_⟩
    rw [RingHom.finite_algebraMap]
    exact f.2.1
  · rw [← RingHom.etale_algebraMap]
    refine RingHom.Etale.ofLocalizationSpan.ofIsLocalization RingHom.Etale.respectsIso _ s hs
      fun f ↦ ⟨Localization.Away f.1, Localization.Away f.1 ⊗[R] B, _, _, _, _, inferInstance,
        inferInstance,
        algebraMap _ _, hcomp f.1, ?_⟩
    rw [RingHom.etale_algebraMap]
    exact f.2.2

end Algebra

namespace Pi

variable {S X : Type*} [CommRing S] [Fintype X] [DecidableEq X]

/-- A ring map out of `X → S` sending the idempotent `δ_{x₀}` to `1` only depends on the value
at `x₀`. -/
lemma ringHom_apply_eq_of_apply_single {B : Type*} [CommRing B] (ψ : (X → S) →+* B) (x₀ : X)
    (h : ψ (Pi.single x₀ 1) = 1) (f : X → S) : ψ f = ψ (fun _ ↦ f x₀) := by
  have hsingle (x : X) : Pi.single x (f x) = (fun _ ↦ f x) * Pi.single x 1 := by
    ext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  conv_lhs => rw [← Finset.univ_sum_single f]
  rw [map_sum, Finset.sum_eq_single x₀]
  · rw [hsingle, map_mul, h, mul_one]
  · intro x _ hx
    have h0 : (Pi.single x 1 : X → S) * Pi.single x₀ 1 = 0 := by
      ext y
      by_cases hy : y = x
      · subst hy; simp [hx]
      · simp [Pi.single_apply, hy]
    rw [hsingle, map_mul, ← mul_one (ψ (Pi.single x 1)), ← h, ← map_mul, h0, map_zero,
      mul_zero]
  · simp

end Pi

namespace AlgHom

variable {S X : Type*} [CommRing S] [Fintype X] [DecidableEq X] {ι : Type*}

/-- The family of coordinate endomorphisms `f ↦ f ∘ πᵢ` of `X → S`. -/
def coordFamily (π : ι → X → X) : ι → (X → S) →ₐ[S] (X → S) :=
  fun i ↦ AlgHom.pi fun x ↦ Pi.evalAlgHom S (fun _ ↦ S) (π i x)

omit [Fintype X] [DecidableEq X] in
@[simp]
lemma coordFamily_apply (π : ι → X → X) (i : ι) (f : X → S) :
    coordFamily (S := S) π i f = f ∘ π i :=
  rfl

/-- The fixed points of a family of coordinate endomorphisms are the functions on the quotient of
`X` by the relation generated by `x ~ πᵢ x`. -/
noncomputable def fixedPointsCoordFamilyEquiv (π : ι → X → X) :
    fixedPoints (coordFamily (S := S) π) ≃ₐ[S] (Quot (fun x y : X ↦ ∃ i, π i x = y) → S) where
  toFun f := Quot.lift f.1 fun x y ⟨i, hi⟩ ↦ by
    have := congr_fun (mem_fixedPoints.mp f.2 i) x
    simp only [coordFamily_apply, Function.comp_apply] at this
    rw [← hi, this]
  invFun g := ⟨g ∘ Quot.mk _, mem_fixedPoints.mpr fun i ↦ funext fun x ↦ by
    simp only [coordFamily_apply, Function.comp_apply]
    exact congr_arg g (Quot.sound ⟨i, rfl⟩).symm⟩
  left_inv f := rfl
  right_inv g := funext fun x ↦ by obtain ⟨x, rfl⟩ := Quot.mk_surjective x; rfl
  map_mul' f g := funext fun x ↦ by obtain ⟨x, rfl⟩ := Quot.mk_surjective x; rfl
  map_add' f g := funext fun x ↦ by obtain ⟨x, rfl⟩ := Quot.mk_surjective x; rfl
  commutes' r := funext fun x ↦ by obtain ⟨x, rfl⟩ := Quot.mk_surjective x; rfl

/-- After inverting a suitable element outside a given prime, every finite family of algebra
endomorphisms of `X → S` becomes a family of coordinate endomorphisms. -/
lemma exists_localizationAway_coordinate [_root_.Finite ι] (σ : ι → (X → S) →ₐ[S] (X → S))
    (q : Ideal S) [q.IsPrime] :
    ∃ h ∉ q, ∃ π : ι → X → X, ∀ i x,
      algebraMap S (Localization.Away h) (σ i (Pi.single (π i x) 1) x) = 1 := by
  classical
  cases nonempty_fintype ι
  have hex (i : ι) (x : X) : ∃ y, σ i (Pi.single y 1) x ∉ q := by
    by_contra! H
    have : ∑ y, σ i (Pi.single y 1) x ∈ q := Ideal.sum_mem _ fun y _ ↦ H y
    rw [← Finset.sum_apply, ← map_sum, Finset.univ_sum_single (fun _ ↦ (1 : S)),
      show (fun _ ↦ (1 : S)) = (1 : X → S) from rfl, map_one, Pi.one_apply] at this
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr this)
  choose π hπ using hex
  let u (i : ι) (x : X) : S := σ i (Pi.single (π i x) 1) x
  refine ⟨∏ i, ∏ x, u i x, ?_, π, fun i x ↦ ?_⟩
  · simp only [Ideal.IsPrime.prod_mem_iff, not_exists, not_and]
    exact fun i _ x _ ↦ hπ i x
  · have hunit : IsUnit (algebraMap S (Localization.Away (∏ i, ∏ x, u i x)) (u i x)) := by
      refine isUnit_of_dvd_unit (map_dvd _ ?_)
        (IsLocalization.Away.algebraMap_isUnit (R := S)
          (S := Localization.Away (∏ i, ∏ x, u i x)) (∏ i, ∏ x, u i x))
      exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ x)).trans
        (Finset.dvd_prod_of_mem (fun i ↦ ∏ x, u i x) (Finset.mem_univ i))
    have hidem : IsIdempotentElem (u i x) := by
      change σ i _ x * σ i _ x = σ i _ x
      rw [← Pi.mul_apply, ← map_mul, ← Pi.single_mul, mul_one]
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp (hidem.map (algebraMap S _))

end AlgHom

namespace AlgHom

/-- The fixed points of a finite family of algebra endomorphisms of `Fin n → S` form a finite
étale `S`-algebra: locally on `Spec S` the family consists of coordinate endomorphisms, whose
fixed points are the functions on a quotient of `Fin n`. -/
theorem finite_and_etale_fixedPoints_fun {S : Type u} [CommRing S] {n : ℕ} {ι : Type*}
    [_root_.Finite ι] (σ : ι → (Fin n → S) →ₐ[S] (Fin n → S)) :
    Module.Finite S (fixedPoints σ) ∧ Algebra.Etale S (fixedPoints σ) := by
  refine Algebra.finite_and_etale_of_forall_exists_localizationAway fun q _ ↦ ?_
  obtain ⟨h, hq, π, hπ⟩ := exists_localizationAway_coordinate σ q
  refine ⟨h, hq, ?_⟩
  let Sh := Localization.Away h
  let e := Algebra.TensorProduct.piScalarRight S Sh Sh (Fin n)
  have hconj : conjFamily e (baseChangeFamily Sh σ) = coordFamily π := by
    funext i
    ext f x
    let ψ : (Fin n → Sh) →+* Sh :=
      (Pi.evalRingHom _ x).comp (conjFamily e (baseChangeFamily Sh σ) i).toRingHom
    have hsymm (y : Fin n) : e.symm (Pi.single y 1) = 1 ⊗ₜ Pi.single y 1 := by
      rw [AlgEquiv.symm_apply_eq]
      ext z
      by_cases hz : z = y
      · subst hz; simp [e]
      · simp [e, hz]
    have h1 : ψ (Pi.single (π i x) 1) = 1 := by
      simp only [ψ, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, conjFamily_apply, hsymm, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      simp only [e, Algebra.TensorProduct.piScalarRight_tmul, Algebra.smul_def, mul_one]
      exact hπ i x
    have := Pi.ringHom_apply_eq_of_apply_single ψ (π i x) h1 f
    simp only [ψ, RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] at this
    rw [this, show (fun _ ↦ f (π i x)) = algebraMap Sh (Fin n → Sh) (f (π i x)) from rfl,
      AlgHom.commutes]
    rfl
  let E : Sh ⊗[S] fixedPoints σ ≃ₐ[Sh] (Quot (fun x y : Fin n ↦ ∃ i, π i x = y) → Sh) :=
    (tensorFixedPointsEquiv Sh σ).trans <| (fixedPointsCongr e _).trans <|
      (Subalgebra.equivOfEq _ _ (by rw [hconj])).trans (fixedPointsCoordFamilyEquiv π)
  exact ⟨Module.Finite.equiv E.symm.toLinearEquiv, Algebra.Etale.of_equiv E.symm⟩

/-- **Fixed points of a finite étale algebra.** The common fixed points of a finite family of
endomorphisms of a finite étale `R`-algebra form a finite étale `R`-algebra.

Locally on `Spec R` the algebra `A` has constant rank, hence becomes split, `T ⊗ A ≅ Fin n → T`,
after a faithfully flat finite étale base change `T`
(`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`). Taking fixed points commutes with the
flat base change, and the fixed points of a family of endomorphisms of `Fin n → T` are finite
étale (`AlgHom.finite_and_etale_fixedPoints_fun`); finiteness and étaleness descend along `T`. -/
theorem finite_and_etale_fixedPoints {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra.Etale R A] {ι : Type*} [_root_.Finite ι] (σ : ι → A →ₐ[R] A) :
    Module.Finite R (fixedPoints σ) ∧ Algebra.Etale R (fixedPoints σ) := by
  have : Module.FinitePresentation R A := .of_finite_of_finitePresentation R A
  refine Algebra.finite_and_etale_of_forall_exists_localizationAway fun p hp ↦ ?_
  -- the rank of `A` is constant on a basic open neighbourhood `D(f)` of `p`
  have hopen := (Module.isLocallyConstant_rankAtStalk (R := R) (M := A)).isOpen_fiber
    (Module.rankAtStalk A ⟨p, hp⟩)
  obtain ⟨_, ⟨f, rfl⟩, hpf, hf⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := ⟨p, hp⟩) (show (⟨p, hp⟩ : PrimeSpectrum R) ∈
        {x | Module.rankAtStalk A x = Module.rankAtStalk A ⟨p, hp⟩} from rfl) hopen
  refine ⟨f, hpf, ?_⟩
  let Rf := Localization.Away f
  have hrank : Module.rankAtStalk (R := Rf) (Rf ⊗[R] A) = Module.rankAtStalk A ⟨p, hp⟩ := by
    ext q
    rw [Module.rankAtStalk_baseChange, Pi.natCast_apply, Nat.cast_id]
    refine hf ?_
    change f ∉ (q.comap (algebraMap R Rf)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    exact fun h ↦ q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (IsLocalization.Away.algebraMap_isUnit f))
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hrank
  obtain ⟨m, ⟨e⟩⟩ := hT.nonempty_algEquiv_fun
  obtain ⟨h₁, h₂⟩ :=
    finite_and_etale_fixedPoints_fun (conjFamily e (baseChangeFamily T (baseChangeFamily Rf σ)))
  let E : T ⊗[Rf] (Rf ⊗[R] fixedPoints σ) ≃ₐ[T]
      fixedPoints (conjFamily e (baseChangeFamily T (baseChangeFamily Rf σ))) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl (tensorFixedPointsEquiv Rf σ)).trans <|
      (tensorFixedPointsEquiv T _).trans (fixedPointsCongr e _)
  have : Module.Finite T (T ⊗[Rf] (Rf ⊗[R] fixedPoints σ)) :=
    Module.Finite.equiv E.symm.toLinearEquiv
  have : Algebra.Etale T (T ⊗[Rf] (Rf ⊗[R] fixedPoints σ)) := Algebra.Etale.of_equiv E.symm
  exact ⟨.of_finite_tensorProduct_of_faithfullyFlat T,
    Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat T⟩

end AlgHom
