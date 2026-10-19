/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.RingTheory.WeaklyEtaleField
import Sheaf.RingTheory.NormalOfFlatNormalFibers
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite residue-field models under weakly etale maps

Source: Greco, Two theorems on excellent rings, Theorem 5.3(ii), and the normalization
construction in Stacks Project, Tags 092Q, 0C22 and 030C.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace RingHom

open scoped TensorProduct

private theorem residue_algebraic
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.WeaklyEtale A B] (q : Ideal B) [q.IsPrime] :
    let p := q.comap (algebraMap A B)
    letI : q.LiesOver p := ⟨rfl⟩
    letI := Localization.AtPrime.algebraOfLiesOver p q
    Algebra.IsAlgebraic p.ResidueField q.ResidueField := by
  dsimp only
  let p := q.comap (algebraMap A B)
  let : q.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  let F := p.Fiber B
  let χ : F →ₐ[p.ResidueField] q.ResidueField :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (IsScalarTower.toAlgHom A B q.ResidueField) (fun _ _ ↦ Commute.all _ _)
  let Q := RingHom.ker χ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime χ.toRingHom
  have : Ring.AbsolutelyFlat F :=
    Ring.AbsolutelyFlat.of_flat_lmul' p.ResidueField F
      (Algebra.WeaklyEtale.flat_lmul' p.ResidueField F)
  let : Field (Localization.AtPrime Q) :=
    (Ring.AbsolutelyFlat.isField_of_isLocalization_prime F Q (Localization.AtPrime Q)).toField
  have : Algebra.WeaklyEtale p.ResidueField (Localization.AtPrime Q) :=
    Algebra.WeaklyEtale.trans p.ResidueField F _
  have : Algebra.IsSeparable p.ResidueField (Localization.AtPrime Q) :=
    Algebra.WeaklyEtale.isAlgebraic
  let ψ : Localization.AtPrime Q →ₐ[p.ResidueField] q.ResidueField :=
    IsLocalization.liftAlgHom (M := Q.primeCompl) (f := χ) (fun x ↦
      isUnit_iff_ne_zero.mpr x.property)
  have key (b : B) : _root_.IsIntegral p.ResidueField (algebraMap B q.ResidueField b) := by
    have h := (Algebra.IsIntegral.isIntegral (R := p.ResidueField)
      (algebraMap F (Localization.AtPrime Q) ((1 : p.ResidueField) ⊗ₜ[A] b))).map ψ
    simp only [ψ, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq] at h
    change _root_.IsIntegral p.ResidueField (χ ((1 : p.ResidueField) ⊗ₜ[A] b)) at h
    have heq : χ ((1 : p.ResidueField) ⊗ₜ[A] b) = algebraMap B q.ResidueField b := by
      dsimp only [χ]
      rw [Algebra.TensorProduct.lift_tmul]
      simp
    exact heq ▸ h
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, s, -, hxs⟩ := IsFractionRing.div_surjective (A := B ⧸ q) y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [← hxs, Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk]
  rw [div_eq_mul_inv]
  exact ((key x).mul (key s).inv).isAlgebraic


private theorem minimal_kernel
    {R : Type u} {S : Type w} {L : Type v} [CommRing R] [IsDomain R]
    [CommRing S] [Field L] [Algebra R S] [Algebra.WeaklyEtale R S]
    [Algebra R L] (h : S →ₐ[R] L) (hinj : Function.Injective (algebraMap R L)) :
    IsMinimalPrime (RingHom.ker h.toRingHom) := by
  let Q := RingHom.ker h.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime h.toRingHom
  have hQ : Q.comap (algebraMap R S) = ⊥ := by
    change (RingHom.ker h.toRingHom).comap (algebraMap R S) = ⊥
    rw [RingHom.comap_ker]
    have hc : h.toRingHom.comp (algebraMap R S) = algebraMap R L := by
      ext r
      exact h.commutes r
    rw [hc]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  intro q hq hle
  have : q.IsPrime := hq.1
  have hqR : q.comap (algebraMap R S) = ⊥ :=
    le_antisymm ((Ideal.comap_mono hle).trans hQ.le) bot_le
  let p : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} :=
    ⟨⟨q, inferInstance⟩, PrimeSpectrum.ext hqR⟩
  let y : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} :=
    ⟨⟨Q, inferInstance⟩, PrimeSpectrum.ext hQ⟩
  let e := PrimeSpectrum.preimageOrderIsoFiber R S p
  have : Ring.AbsolutelyFlat (p.asIdeal.Fiber S) :=
    Ring.AbsolutelyFlat.of_flat_lmul' p.asIdeal.ResidueField _
      (Algebra.WeaklyEtale.flat_lmul' p.asIdeal.ResidueField _)
  have habs : Ring.AbsolutelyFlat (p.asIdeal.Fiber S) ↔
      IsReduced (p.asIdeal.Fiber S) ∧ Ring.KrullDimLE 0 (p.asIdeal.Fiber S) :=
    (Ring.AbsolutelyFlat.tfae (p.asIdeal.Fiber S)).out 0 2
  have : Ring.KrullDimLE 0 (p.asIdeal.Fiber S) := (habs.mp inferInstance).2
  have hxy : e x ≤ e y := e.monotone hle
  have heq : e x = e y := PrimeSpectrum.ext <|
    (e x).isPrime.isMaximal'.eq_of_le (e y).isPrime.ne_top hxy
  have : q = Q := congrArg (fun z ↦ z.1.asIdeal) (e.injective heq)
  exact this.ge

private theorem normal_domain_image
    {S : Type w} {D : Type v} [CommRing S] [IsNoetherianRing S]
    [CommRing D] [IsDomain D] [Algebra S D]
    (hsurj : Function.Surjective (algebraMap S D))
    (hn : ∀ (p : Ideal S) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hmin : IsMinimalPrime (RingHom.ker (algebraMap S D))) :
    IsIntegrallyClosed D ∧ ∃ e : S, IsIdempotentElem e ∧ IsLocalization.Away e D := by
  classical
  have : IsReduced S := isReduced_ofLocalizationMaximal S fun p hp ↦ by
    have : IsDomain (Localization.AtPrime p) := (hn p).1
    infer_instance
  obtain ⟨n, T, hT, ⟨e⟩⟩ :=
    (reduced_normal_iff_integrallyClosed_totalFractions S
      (minimalPrimes.finite_of_isNoetherianRing S)).2.mp
      ((reduced_normal_iff_integrallyClosed_totalFractions S
        (minimalPrimes.finite_of_isNoetherianRing S)).1.mp hn)
  let Q := RingHom.ker (algebraMap S D)
  let P : PrimeSpectrum S := ⟨Q, RingHom.ker_isPrime _⟩
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
    (PrimeSpectrum.comap e.symm.toRingHom P)
  let : IsDomain (T i) := (hT i).1
  let : IsIntegrallyClosed (T i) := (hT i).2
  let π : S →+* T i := (Pi.evalRingHom (fun j ↦ T j) i).comp e.toRingHom
  have hπ : Function.Surjective π :=
    (Pi.evalRingHom (fun j ↦ T j) i).surjective.comp e.surjective
  have hker : Q = RingHom.ker π := by
    have hle : RingHom.ker π ≤ Q := by
      have hq' := congrArg (fun p ↦ p.asIdeal.comap e.toRingHom) hq
      have hq'' : (q.asIdeal.comap (Pi.evalRingHom (fun j ↦ T j) i)).comap
          e.toRingHom = Q := by
        simpa [P, Q, Ideal.comap_comap] using hq'
      rw [← hq'']
      intro x hx
      change e x i ∈ q.asIdeal
      change π x = 0 at hx
      rw [show e x i = 0 from hx]
      exact Ideal.zero_mem _
    have : (RingHom.ker π).IsPrime := RingHom.ker_isPrime π
    exact le_antisymm (hmin.2 ⟨inferInstance, bot_le⟩ hle) hle
  let eD : S ⧸ Q ≃+* D := RingHom.quotientKerEquivOfSurjective hsurj
  let eT : S ⧸ RingHom.ker π ≃+* T i := RingHom.quotientKerEquivOfSurjective hπ
  let eDT : D ≃+* T i := eD.symm.trans
    ((Ideal.quotientEquivAlgOfEq S hker).toRingEquiv.trans eT)
  refine ⟨IsIntegrallyClosed.of_equiv eDT.symm, e.symm (Pi.single i 1), ?_, ?_⟩
  · apply (e.injective)
    simp [← map_mul, ← Pi.single_mul]
  · apply IsLocalization.away_of_isIdempotentElem_of_mul
    · apply e.injective
      simp [← map_mul, ← Pi.single_mul]
    · intro x y
      have heq : algebraMap S D x = algebraMap S D y ↔ π x = π y := by
        rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ← sub_eq_zero,
          ← map_sub, ← RingHom.mem_ker]
        exact Iff.of_eq (congrArg (fun J : Ideal S ↦ x - y ∈ J) hker)
      rw [heq, ← e.injective.eq_iff]
      simp [map_mul, ← Pi.single_mul_left, π]
    · exact hsurj

private theorem normal_fibres_of_weaklyEtale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.WeaklyEtale) :
    letI : Algebra R S := f.toAlgebra
    ∀ (p : Ideal R) [p.IsPrime], ∀ (q : Ideal (p.Fiber S)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.WeaklyEtale R S := hf
  intro p hp q hq
  have : Ring.AbsolutelyFlat (p.Fiber S) :=
    Ring.AbsolutelyFlat.of_flat_lmul' p.ResidueField _
      (Algebra.WeaklyEtale.flat_lmul' p.ResidueField _)
  let : Field (Localization.AtPrime q) :=
    (Ring.AbsolutelyFlat.isField_of_isLocalization_prime _ q _).toField
  exact ⟨inferInstance, inferInstance⟩

set_option maxHeartbeats 150000 in
-- The normalization tower requires instance synthesis through the small field copy.
/-- A finite extension of a residue field of a Noetherian weakly etale algebra over a
Nagata ring has a finite domain model weakly etale over a finite domain over the source.
This statement concerns the finite normalization construction only; no regularity or
J-2 hypothesis is involved.

Source: Greco, Two theorems on excellent rings, Theorem 5.3(ii), pp. 146--147;
Stacks Project, Tags 092Q, 0C22 and 030C
(blueprint: lem-exc-weakly-etale-finite-residue-model).

Proof:
1. Put p = f^-1(q), k = kappa(p), E = kappa(q). Base change and the weakly etale field
   calculation give that E/k is algebraic and that all primes in every field fibre are
   maximal. Choose a finite E-basis of L. Its elements are algebraic over k, so the field
   L0 generated by them over k is finite over k, and E L0 = L.
2. Replace the finite extension L0/k by a small isomorphic field K0 in Type u, using
   that a finite-dimensional k-vector space has cardinal bounded by finite tuples of k.
   Normalize A/p in K0. The Nagata hypothesis makes this normal domain R finite over
   A/p, hence over A and Noetherian, with fraction field K0. No size bound on E/k is
   required.
3. Put C = B tensor_A R. It is finite over B and Noetherian. The map R -> C is weakly
   etale by base change. Its fibres are normal, since a weakly etale field algebra is
   absolutely flat and all its prime localizations are fields. Flat normal-fibre ascent
   makes C normal.
4. The multiplication map C -> L has image D and kernel Q. Its restriction to R is
   injective. Any prime Q0 contained in Q avoids the nonzero elements of R. Extend
   both primes to the generic fibre C tensor_R L0. All primes there are maximal, so
   their extensions coincide; contraction gives Q0 = Q. Thus Q is minimal.
5. A Noetherian normal ring is a finite product of normal domains. In this product Q
   is the kernel of one projection, since it is minimal. Therefore D = C/Q is a direct
   factor. That projection is a localization at the corresponding idempotent, hence
   weakly etale. Composition makes R -> D weakly etale and it is injective.
6. Regard D as the B-subalgebra of L generated by the image of R. The images of a finite
   A-module spanning set of R span D over B. Fractions of D contain E (fractions of
   B/q) and L0 (fractions of R), and hence all of L = E L0. This proves the displayed
   fraction property. The zero target has no prime q, so causes no extra case.
-/
public theorem exists_finite_residue_model_of_weaklyEtale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : f.WeaklyEtale) (hNagata : IsNagataRing A)
    (q : Ideal B) [q.IsPrime] (L : Type v) [Field L]
    [Algebra q.ResidueField L] [Algebra B L] [IsScalarTower B q.ResidueField L]
    [Module.Finite q.ResidueField L] :
    ∃ D : Subalgebra B L, Module.Finite B D ∧ IsIntegrallyClosed D ∧
      (∀ x : L, ∃ b c : D, (c : L) ≠ 0 ∧ x = (b : L) / (c : L)) ∧
      ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra A R),
        Module.Finite A R ∧ ∃ (_ : Algebra R D),
          Algebra.WeaklyEtale R D ∧ Function.Injective (algebraMap R D) := by
  classical
  let : Algebra A B := f.toAlgebra
  have : Algebra.WeaklyEtale A B := hf
  let p := q.comap (algebraMap A B)
  let : p.IsPrime := Ideal.comap_isPrime _ q
  let : q.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra A L := ((algebraMap B L).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsAlgebraic p.ResidueField q.ResidueField := residue_algebraic q
  let : Algebra p.ResidueField L :=
    ((algebraMap q.ResidueField L).comp (algebraMap p.ResidueField q.ResidueField)).toAlgebra
  have : IsScalarTower p.ResidueField q.ResidueField L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A q.ResidueField L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B q.ResidueField,
      IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply B q.ResidueField L]
  have : IsScalarTower A p.ResidueField L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A L a = algebraMap q.ResidueField L
      (algebraMap p.ResidueField q.ResidueField (algebraMap A p.ResidueField a))
    rw [← IsScalarTower.algebraMap_apply A p.ResidueField q.ResidueField,
      ← IsScalarTower.algebraMap_apply A q.ResidueField L]
  let : Algebra (A ⧸ p) L :=
    ((algebraMap p.ResidueField L).comp (algebraMap (A ⧸ p) p.ResidueField)).toAlgebra
  have : IsScalarTower (A ⧸ p) p.ResidueField L :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (A ⧸ p) L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A L a = algebraMap p.ResidueField L
      (algebraMap (A ⧸ p) p.ResidueField (algebraMap A (A ⧸ p) a))
    rw [← IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField,
      ← IsScalarTower.algebraMap_apply A p.ResidueField L]
  have : Algebra.IsAlgebraic p.ResidueField L := Algebra.IsAlgebraic.trans _ q.ResidueField _
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := q.ResidueField) (M := L)
  let L₀ := IntermediateField.adjoin p.ResidueField (Set.range s)
  have : Module.Finite p.ResidueField L₀ :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have : Small.{u} L₀ := Module.Finite.small p.ResidueField L₀
  obtain ⟨K₀, _, _, ⟨e₀⟩⟩ :
      ∃ (K₀ : Type u) (_ : Field K₀) (_ : Algebra p.ResidueField K₀),
        Nonempty (K₀ ≃ₐ[p.ResidueField] L₀) :=
    ⟨Shrink.{u} L₀, inferInstance, inferInstance, ⟨Shrink.algEquiv _ _⟩⟩
  have : Module.Finite p.ResidueField K₀ := Module.Finite.equiv e₀.symm.toLinearEquiv
  let : Algebra (A ⧸ p) K₀ :=
    ((algebraMap p.ResidueField K₀).comp (algebraMap (A ⧸ p) p.ResidueField)).toAlgebra
  have : IsScalarTower (A ⧸ p) p.ResidueField K₀ :=
    IsScalarTower.of_algebraMap_eq' (R := A ⧸ p) (S := p.ResidueField) (A := K₀) rfl
  let : Algebra A K₀ :=
    ((algebraMap (A ⧸ p) K₀).comp (algebraMap A (A ⧸ p))).toAlgebra
  have : IsScalarTower A (A ⧸ p) K₀ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A p.ResidueField K₀ := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap p.ResidueField K₀
      (algebraMap (A ⧸ p) p.ResidueField (algebraMap A (A ⧸ p) a)) = _
    rw [← IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField]
  let : Algebra A L₀ :=
    ((algebraMap p.ResidueField L₀).comp (algebraMap A p.ResidueField)).toAlgebra
  have : IsScalarTower A p.ResidueField L₀ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A L₀ L := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap A L a = algebraMap p.ResidueField L (algebraMap A p.ResidueField a)
    exact IsScalarTower.algebraMap_apply A p.ResidueField L a
  let eF : FractionRing (A ⧸ p) ≃ₐ[A ⧸ p] p.ResidueField :=
    IsLocalization.algEquiv (nonZeroDivisors (A ⧸ p)) _ _
  let : Algebra (FractionRing (A ⧸ p)) K₀ :=
    ((algebraMap p.ResidueField K₀).comp eF.toRingHom).toAlgebra
  have : IsScalarTower (A ⧸ p) (FractionRing (A ⧸ p)) K₀ :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap (A ⧸ p) K₀ a = algebraMap p.ResidueField K₀
        (eF (algebraMap (A ⧸ p) (FractionRing (A ⧸ p)) a))
      rw [eF.commutes, ← IsScalarTower.algebraMap_apply (A ⧸ p) p.ResidueField K₀]
  have : Module.Finite (FractionRing (A ⧸ p)) K₀ :=
    Module.Finite.of_equiv_equiv eF.symm.toRingEquiv (RingEquiv.refl K₀) (by
      apply RingHom.ext
      intro x
      change algebraMap p.ResidueField K₀ (eF (eF.symm x)) = _
      simp)
  let R := integralClosure (A ⧸ p) K₀
  have : Module.Finite (A ⧸ p) R := hNagata.2 p K₀
  let : Algebra A R :=
    ((algebraMap (A ⧸ p) R).comp (algebraMap A (A ⧸ p))).toAlgebra
  have : IsScalarTower A (A ⧸ p) R := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A R K₀ := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap (A ⧸ p) K₀ (algebraMap A (A ⧸ p) a) = _
    rw [IsScalarTower.algebraMap_apply (A ⧸ p) R K₀]
    rfl
  have : Module.Finite A R := Module.Finite.trans (A ⧸ p) R
  have : IsNoetherianRing R := IsNoetherianRing.of_finite A R
  have : IsIntegrallyClosed R := integralClosure.isIntegrallyClosedOfFiniteExtension
    (FractionRing (A ⧸ p))
  have : IsFractionRing R K₀ := integralClosure.isFractionRing_of_finite_extension
    (FractionRing (A ⧸ p)) K₀
  let ι₀ : K₀ →ₐ[A] L :=
    L₀.val.restrictScalars A |>.comp (e₀.restrictScalars A).toAlgHom
  let rL : R →ₐ[A] L := ι₀.comp (IsScalarTower.toAlgHom A R K₀)
  let : Algebra R L := rL.toRingHom.toAlgebra
  have : IsScalarTower A R L := IsScalarTower.of_algebraMap_eq' rL.comp_algebraMap.symm
  let C := R ⊗[A] B
  let : Algebra B C := Algebra.TensorProduct.rightAlgebra
  have : Module.Finite B C := by
    let e := Algebra.TensorProduct.comm A R B
    exact Module.Finite.of_equiv_equiv (RingEquiv.refl B) e.symm.toRingEquiv (by
      ext b
      change (1 : R) ⊗ₜ[A] b =
        (Algebra.TensorProduct.comm A B R) (b ⊗ₜ[A] (1 : R))
      rw [Algebra.TensorProduct.comm_tmul])
  have : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  have : Algebra.WeaklyEtale R C := inferInstance
  let hA : C →ₐ[A] L := Algebra.TensorProduct.lift rL
    (IsScalarTower.toAlgHom A B L) (fun _ _ ↦ Commute.all _ _)
  let hB : C →ₐ[B] L :=
    { hA.toRingHom with
      commutes' := fun b ↦ by
        change hA ((1 : R) ⊗ₜ[A] b) = algebraMap B L b
        dsimp only [hA]
        rw [Algebra.TensorProduct.lift_tmul]
        simp }
  let D := hB.range
  let g : C →ₐ[B] D := hB.rangeRestrict
  let : Algebra C D := g.toRingHom.toAlgebra
  have : IsScalarTower B C D := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let : Algebra R D :=
    (g.toRingHom.comp (algebraMap R C)).toAlgebra
  have : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R D L := IsScalarTower.of_algebraMap_eq' (by
    ext r
    change rL r = hA (r ⊗ₜ[A] (1 : B))
    dsimp only [hA]
    rw [Algebra.TensorProduct.lift_tmul]
    simp)
  have hRinj : Function.Injective (algebraMap R L) :=
    ι₀.injective.comp (IsFractionRing.injective R K₀)
  have hRDinj : Function.Injective (algebraMap R D) := by
    intro x y hxy
    apply hRinj
    simpa only [IsScalarTower.algebraMap_apply R D L] using
      congrArg (algebraMap D L) hxy
  have hnormal : ∀ (p : Ideal C) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
    apply normal_of_flat_normal_fibers (algebraMap R C)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
    · exact normal_fibres_of_weaklyEtale (algebraMap R C)
        (weaklyEtale_algebraMap_iff.mpr inferInstance)
    · intro p hp
      exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization _ p.primeCompl
        p.primeCompl_le_nonZeroDivisors⟩
  let hR : C →ₐ[R] L :=
    { hA.toRingHom with
      commutes' := fun r ↦ by
        change hA (r ⊗ₜ[A] (1 : B)) = rL r
        dsimp only [hA]
        rw [Algebra.TensorProduct.lift_tmul]
        simp }
  have hmin : IsMinimalPrime (RingHom.ker (algebraMap C D)) := by
    have hk : RingHom.ker (algebraMap C D) = RingHom.ker hR.toRingHom := by
      ext c
      change g c = 0 ↔ hA c = 0
      exact Subtype.ext_iff
    rw [hk]
    exact minimal_kernel hR hRinj
  obtain ⟨hDnormal, e, he, hloc⟩ := normal_domain_image hB.rangeRestrict_surjective
    hnormal hmin
  have : IsLocalization.Away e D := hloc
  have : Algebra.WeaklyEtale C D :=
    Algebra.WeaklyEtale.of_isLocalization C (Submonoid.powers e) D
  have : Algebra.WeaklyEtale R D := Algebra.WeaklyEtale.trans R C D
  have : Module.Finite B D := Module.Finite.of_surjective g.toLinearMap
    hB.rangeRestrict_surjective
  refine ⟨D, inferInstance, hDnormal, ?_, R, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hRDinj⟩
  let j : FractionRing D →+* L := IsFractionRing.lift
    (g := algebraMap D L) (FaithfulSMul.algebraMap_injective D L)
  let F := j.fieldRange
  have hD (d : D) : (d : L) ∈ F := by
    exact ⟨algebraMap D (FractionRing D) d, IsFractionRing.lift_algebraMap _ d⟩
  have hB (b : B) : algebraMap B L b ∈ F := hD (algebraMap B D b)
  have hE (x : q.ResidueField) : algebraMap q.ResidueField L x ∈ F := by
    obtain ⟨b, c, -, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ q) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    simpa only [map_div₀, Ideal.algebraMap_quotient_residueField_mk,
      ← IsScalarTower.algebraMap_apply B q.ResidueField L] using F.div_mem (hB b) (hB c)
  have hRmem (r : R) : rL r ∈ F := by
    have h := hD (algebraMap R D r)
    change algebraMap D L (algebraMap R D r) ∈ F at h
    rw [← IsScalarTower.algebraMap_apply R D L] at h
    exact h
  have hK (x : K₀) : ι₀ x ∈ F := by
    obtain ⟨r, t, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    change ι₀ (algebraMap R K₀ r / algebraMap R K₀ t) ∈ F
    rw [map_div₀]
    exact F.div_mem (hRmem r) (hRmem t)
  have hsF (i : Fin n) : s i ∈ F := by
    let x : L₀ := ⟨s i, IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)⟩
    have hx := hK (e₀.symm x)
    change ((e₀ (e₀.symm x) : L₀) : L) ∈ F at hx
    rw [e₀.apply_symm_apply] at hx
    exact hx
  let V : Submodule q.ResidueField L :=
    { carrier := F
      zero_mem' := F.zero_mem
      add_mem' := F.add_mem
      smul_mem' := fun a x hx ↦ by
        change a • x ∈ F
        rw [Algebra.smul_def]
        exact F.mul_mem (hE a) hx }
  have hV : V = ⊤ := top_unique <| hs ▸ Submodule.span_le.mpr (by
    rintro x ⟨i, rfl⟩
    exact hsF i)
  intro x
  have hx : x ∈ F := show x ∈ V from hV ▸ Submodule.mem_top
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := D) z
  refine ⟨b, c, ?_, ?_⟩
  · exact fun h ↦ (mem_nonZeroDivisors_iff_ne_zero.mp hc) (Subtype.ext h)
  · rw [map_div₀]
    change j (algebraMap D (FractionRing D) b) /
      j (algebraMap D (FractionRing D) c) = _
    rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
    rfl

end RingHom
