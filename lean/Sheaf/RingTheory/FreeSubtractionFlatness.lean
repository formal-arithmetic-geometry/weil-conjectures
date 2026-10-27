/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.ULift
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer
import Sheaf.RingTheory.UniversalInjectiveLocalization
import Sheaf.TraceFormula.LocalUIFlatCokernel
import Sheaf.TraceFormula.LocalGenericBasisUniversalInjective

/-!
# Generic basis subtraction and the relative flat locus

Source: Stacks Project, Tag 05I3, `flat.tex`, Lemma `lemma-induction-step`, localized over
all base primes; Tag 05CL, `algebra.tex`, Lemma `lemma-universally-injective-check-stalks`.
(blueprint: lem-trf-free-subtraction-flatness)

A localization at an A-prime q over an R-prime p has its canonical R_p-module structure.
For this module, flatness over R_p is equivalent to flatness over R, by
`Module.flat_iff_of_isLocalization`. We use the latter formulation, with exactly the
same localized module, both in the generic-point hypothesis and the flat-locus conclusion.
The fibre ring is written with the residue field on the left; tensor symmetry identifies
it with A tensor_R kappa(p).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z t

open AlgebraicGeometry TensorProduct CategoryTheory

namespace Module

private theorem geom_domain (R A K : Type u) [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    IsDomain (K ⊗[R] A) := by
  have hs := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R K A)).flip
  have : IsIntegral (Spec (.of (K ⊗[R] A))) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ hs
  exact (affine_isIntegral_iff _).mp this

private theorem restrict_ui {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N]
    (f : M →ₗ[S] N) (L : Type z) [AddCommGroup L] [Module R L]
    (h : Function.Injective (f.rTensor (S ⊗[R] L))) :
    Function.Injective ((f.restrictScalars R).rTensor L) := by
  let eM := AlgebraTensorModule.cancelBaseChange R S S M L
  let eN := AlgebraTensorModule.cancelBaseChange R S S N L
  have he : (f.restrictScalars R).rTensor L ∘ₗ (eM.restrictScalars R).toLinearMap =
      (eN.restrictScalars R).toLinearMap ∘ₗ
        ((f.rTensor (S ⊗[R] L)).restrictScalars R) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp_all only [map_add]
    | tmul m n =>
      induction n using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all only [tmul_add, map_add]
      | tmul s l => simp [eM, eN]
  intro x y hxy
  apply eM.symm.injective
  apply h
  apply eN.injective
  change (((eN.restrictScalars R).toLinearMap) ∘ₗ
    ((f.rTensor (S ⊗[R] L)).restrictScalars R)) (eM.symm x) =
    (((eN.restrictScalars R).toLinearMap) ∘ₗ
    ((f.rTensor (S ⊗[R] L)).restrictScalars R)) (eM.symm y)
  rw [← he]
  simpa using hxy

private theorem localized_tensor_injective (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (N : Type v) [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [Module.Finite A N] (r : ℕ) (α : (Fin r → A) →ₗ[A] N)
    (p : PrimeSpectrum R) (ξ : PrimeSpectrum A)
    (hξ : ξ.asIdeal = RingHom.ker
      (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.ResidueField ⊗[R] A))
    (hflat : Module.Flat R (LocalizedModule ξ.asIdeal.primeCompl N))
    (hα : Function.Bijective (α.baseChange ξ.asIdeal.ResidueField))
    (L : Type w) [AddCommGroup L] [Module R L] :
    Function.Injective (LocalizedModule.map p.asIdeal.primeCompl
      ((α.restrictScalars R).rTensor L)) := by
  -- Base change to R_p and its algebra A_p.
  let Rp := Localization.AtPrime p.asIdeal
  let S := Localization (Algebra.algebraMapSubmonoid A p.asIdeal.primeCompl)
  have : Module.Flat Rp S := inferInstance
  have hfp : RingHom.FinitePresentation (algebraMap Rp S) := by
    apply RingHom.finitePresentation_isStableUnderBaseChange.of_isLocalization
      (R := R) (S := A) p.asIdeal.primeCompl
    exact (RingHom.finitePresentation_algebraMap).mpr inferInstance
  have : Algebra.IsPushout R Rp A S :=
    (Algebra.isPushout_of_isLocalization p.asIdeal.primeCompl Rp A S).symm
  have hs := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R Rp A S)
  have hgeom : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap Rp S))) :=
    MorphismProperty.of_isPullback hs.flip inferInstance
  have hg : ∀ (q : PrimeSpectrum Rp) (K : Type u) [Field K] [Algebra Rp K]
      (ι : q.asIdeal.ResidueField →+* K),
      algebraMap Rp K = ι.comp (algebraMap Rp q.asIdeal.ResidueField) →
      IsDomain (K ⊗[Rp] S) := by
    intro q K _ _ ι hι
    exact geom_domain Rp S K
  -- The generic fibre prime is the contraction of the extended maximal ideal.
  let I := Ideal.map (algebraMap Rp S) (IsLocalRing.maximalIdeal Rp)
  have hI : I.IsPrime := RingHom.maximalIdeal_map_isPrime_of_geometricFibres hg
  let q : PrimeSpectrum S := ⟨I, hI⟩
  have hq : q.asIdeal.comap (algebraMap Rp S) = IsLocalRing.maximalIdeal Rp := by
    symm
    apply (IsLocalRing.maximalIdeal.isMaximal Rp).eq_of_le
    · exact Ideal.comap_ne_top _ hI.ne_top
    · exact Ideal.le_comap_map
  let : Algebra A (p.asIdeal.Fiber A) := Algebra.TensorProduct.rightAlgebra
  let e := Ideal.Fiber.algEquivQuotient (S := A) p.asIdeal
  have hker : RingHom.ker
      (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.ResidueField ⊗[R] A) =
      I.comap (algebraMap A S) := by
    ext a
    change (1 : p.asIdeal.ResidueField) ⊗ₜ[R] a = 0 ↔ algebraMap A S a ∈ I
    rw [← e.map_eq_zero_iff]
    change e (algebraMap A (p.asIdeal.Fiber A) a) = 0 ↔ _
    rw [e.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hqc : q.asIdeal.comap (algebraMap A S) = ξ.asIdeal := hker.symm.trans hξ.symm
  let Np := S ⊗[A] N
  let jN : N →ₗ[A] Np := TensorProduct.mk A S N 1
  have hjN : IsBaseChange S jN := TensorProduct.isBaseChange A N S
  let jM : (Fin r → A) →ₗ[A] (Fin r → S) :=
    .pi fun i ↦ (Algebra.linearMap A S).comp (.proj i)
  have hjM : IsBaseChange S jM := IsBaseChange.pi _ (fun _ ↦ IsBaseChange.linearMap A S)
  let αp : (Fin r → S) →ₗ[S] Np :=
    (α.baseChange S).comp hjM.equiv.symm.toLinearMap
  have hNp : Module.Finite S Np := inferInstance
  -- Iterated localization gives the original generic stalk and its residue field.
  let Q := Localization.AtPrime q.asIdeal
  have hloc : IsLocalization.AtPrime Q ξ.asIdeal := by
    change IsLocalization ξ.asIdeal.primeCompl Q
    simp only [← hqc]
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid A p.asIdeal.primeCompl) Q q.asIdeal
  let eQ : Q ≃ₐ[A] Localization.AtPrime ξ.asIdeal :=
    IsLocalization.algEquiv ξ.asIdeal.primeCompl Q _
  let Nq := LocalizedModule q.asIdeal.primeCompl Np
  let jQ : Np →ₗ[S] Nq := LocalizedModule.mkLinearMap q.asIdeal.primeCompl Np
  have hjQ : IsBaseChange Q jQ := LocalizedModule.isBaseChange _ _
  let eN : Nq ≃ₗ[A] LocalizedModule ξ.asIdeal.primeCompl N :=
    (hjN.comp hjQ).equiv.symm.restrictScalars A ≪≫ₗ
      TensorProduct.congr eQ.toLinearEquiv (.refl A N) ≪≫ₗ
      (LocalizedModule.equivTensorProduct ξ.asIdeal.primeCompl N).symm.restrictScalars A
  have hNqR : Module.Flat R Nq :=
    Module.Flat.of_linearEquiv (eN.restrictScalars R)
  have hNq : @Module.Flat Rp Nq _ _
      (Module.compHom Nq (algebraMap Rp S)) := by
    have hm : (inferInstance : Module Rp Nq) =
        Module.compHom Nq (algebraMap Rp S) := by
      apply Module.ext'
      intro s n
      exact (IsScalarTower.algebraMap_smul S s n).symm
    rw [← hm]
    exact (Module.flat_iff_of_isLocalization Rp p.asIdeal.primeCompl Nq).mpr hNqR
  -- Transport the generic basis through these residue-field and tensor equivalences.
  let σ : q.asIdeal.ResidueField ≃ₐ[A] ξ.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.mapAlgEquiv eQ
  let K := q.asIdeal.ResidueField
  let fK : K ⊗[S] (Fin r → S) →ₗ[S] K ⊗[S] Np := αp.lTensor K
  let eMK : K ⊗[S] (Fin r → S) ≃ₗ[A] K ⊗[A] (Fin r → A) :=
    (hjM.tensorEquiv K).restrictScalars A
  let eNK : K ⊗[S] Np ≃ₗ[A] K ⊗[A] N :=
    (hjN.tensorEquiv K).restrictScalars A
  have heK : eNK.toLinearMap.comp (fK.restrictScalars A) =
      (α.lTensor K).comp eMK.toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (hjM.equiv.lTensor K).surjective x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp_all only [map_add]
    | tmul k m =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp_all only [map_add, tmul_add]
      | tmul s a =>
        have hgen : αp (jM a) = jN (α a) := by
          change (α.baseChange S) (hjM.equiv.symm (jM a)) = jN (α a)
          rw [hjM.equiv_symm_apply]
          rfl
        simp [eNK, eMK, fK, IsBaseChange.tensorEquiv, hgen]
  let dM := TensorProduct.congr σ.toLinearEquiv (.refl A (Fin r → A))
  let dN := TensorProduct.congr σ.toLinearEquiv (.refl A N)
  have hd : dN.toLinearMap.comp (α.lTensor K) =
      (α.lTensor ξ.asIdeal.ResidueField).comp dM.toLinearMap := by
    ext k a
    rfl
  have hKA : Function.Bijective (α.lTensor K) := by
    have hb : Function.Bijective (dN ∘ α.lTensor K) := by
      change Function.Bijective (dN.toLinearMap.comp (α.lTensor K))
      rw [hd]
      exact hα.comp dM.bijective
    exact (Function.Bijective.of_comp_iff' dN.bijective _).mp hb
  have hK : Function.Bijective fK := by
    have hb : Function.Bijective (eNK ∘ fK) := by
      change Function.Bijective (eNK.toLinearMap.comp (fK.restrictScalars A))
      rw [heK]
      exact hKA.comp eMK.bijective
    exact (Function.Bijective.of_comp_iff' eNK.bijective _).mp hb
  have hui := (RingHom.local_generic_basis_universal_injective.{u, u, u, max u w, max u v}
    ((RingHom.flat_algebraMap_iff).mpr (inferInstance : Module.Flat Rp S))
    hfp hg r Np q hq hNq αp hK).1
  -- Compare the localized tensor map with the map supplied by the local criterion.
  have hu : Function.Injective ((αp.restrictScalars R).rTensor L) := by
    apply restrict_ui (S := Rp) (αp.restrictScalars Rp) L
    exact (LinearMap.lTensor_inj_iff_rTensor_inj
      (f := αp.restrictScalars Rp) (M := Rp ⊗[R] L)).mp (hui _)
  have hjML : IsLocalizedModule (Algebra.algebraMapSubmonoid A p.asIdeal.primeCompl) jM :=
    (isLocalizedModule_iff_isBaseChange _ S _).mpr hjM
  have hjNL : IsLocalizedModule (Algebra.algebraMapSubmonoid A p.asIdeal.primeCompl) jN :=
    (isLocalizedModule_iff_isBaseChange _ S _).mpr hjN
  have hMR := IsLocalizedModule.restrictScalars p.asIdeal.primeCompl jM
  have hNR := IsLocalizedModule.restrictScalars p.asIdeal.primeCompl jN
  let lM := (jM.restrictScalars R).rTensor L
  let lN := (jN.restrictScalars R).rTensor L
  have : IsLocalizedModule p.asIdeal.primeCompl lM := by
    exact IsLocalizedModule.rTensor R p.asIdeal.primeCompl (N := L) (jM.restrictScalars R)
  have : IsLocalizedModule p.asIdeal.primeCompl lN := by
    exact IsLocalizedModule.rTensor R p.asIdeal.primeCompl (N := L) (jN.restrictScalars R)
  have hmap : IsLocalizedModule.map p.asIdeal.primeCompl lM lN
      ((α.restrictScalars R).rTensor L) = (αp.restrictScalars R).rTensor L := by
    apply IsLocalizedModule.linearMap_ext p.asIdeal.primeCompl lM lN
    rw [IsLocalizedModule.map_comp]
    apply TensorProduct.ext'
    intro a l
    change jN (α a) ⊗ₜ[R] l = αp (jM a) ⊗ₜ[R] l
    congr 1
    change jN (α a) = (α.baseChange S) (hjM.equiv.symm (jM a))
    rw [hjM.equiv_symm_apply]
    rfl
  apply (IsLocalizedModule.map_injective_iff_localizedModuleMap_injective lM lN).mp
  rw [hmap]
  exact hu

private theorem tensor_injective_of_ulift
    {R : Type u} [CommRing R] {M : Type v} {P : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] P) (L : Type*) [AddCommGroup L] [Module R L]
    (h : Function.Injective (f.lTensor (ULift.{max u v w z} L))) :
    Function.Injective (f.lTensor L) := by
  let e := (ULift.moduleEquiv (R := R) (M := L)).symm
  have he : (f.lTensor (ULift.{max u v w z} L)).comp (e.rTensor M).toLinearMap =
      (e.rTensor P).toLinearMap.comp (f.lTensor L) := by
    ext x y
    rfl
  intro x y hxy
  apply (e.rTensor M).injective
  apply h
  change ((f.lTensor _).comp (e.rTensor M).toLinearMap) x =
    ((f.lTensor _).comp (e.rTensor M).toLinearMap) y
  rw [he]
  exact congrArg (e.rTensor P) hxy

private theorem flat_iff_of_universally_injective
    {R : Type u} [CommRing R] {M : Type v} {N : Type w} {P : Type z}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [Module.Flat R M]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hex : Function.Exact f g) (hg : Function.Surjective g)
    (hui : ∀ (L : Type (max u v w z t)) [AddCommGroup L] [Module R L],
      Function.Injective (f.lTensor L)) :
    Module.Flat R N ↔ Module.Flat R P := by
  constructor
  · intro hN
    apply Module.flat_of_universally_exact.{u, v, w, z, max v w z t} f g
    intro L _ _
    exact ⟨(LinearMap.lTensor_inj_iff_rTensor_inj (f := f) (M := L)).mp (hui L),
      _root_.rTensor_exact L hex hg, g.rTensor_surjective L hg⟩
  · intro hP
    have hf : Function.Injective f := by
      have hinj := tensor_injective_of_ulift.{u, v, w, max z t}
        f R (hui (ULift.{max u v w z t} R))
      intro x y hxy
      apply (TensorProduct.lid R _).symm.injective
      apply hinj
      change (1 : R) ⊗ₜ[R] f x = (1 : R) ⊗ₜ[R] f y
      rw [hxy]
    exact Module.Flat.of_exact_of_flat_of_flat f g hf hg hex

set_option backward.isDefEq.respectTransparency false in
private theorem localized_flat_iff_quotient
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (N : Type v) [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    (r : ℕ) (α : (Fin r → A) →ₗ[A] N)
    (hα : ∀ (L : Type (max u v w)) [AddCommGroup L] [Module R L],
      Function.Injective ((α.restrictScalars R).lTensor L))
    (q : PrimeSpectrum A) :
    Module.Flat R (LocalizedModule q.asIdeal.primeCompl N) ↔
      Module.Flat R (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α)) := by
  let T := q.asIdeal.primeCompl
  let f : LocalizedModule T (Fin r → A) →ₗ[R] LocalizedModule T N :=
    (LocalizedModule.map T α).restrictScalars R
  let g : LocalizedModule T N →ₗ[R]
      LocalizedModule T (N ⧸ LinearMap.range α) :=
    (LocalizedModule.map T (LinearMap.range α).mkQ).restrictScalars R
  have hex : Function.Exact f g :=
    LocalizedModule.map_exact T α (LinearMap.range α).mkQ α.exact_map_mkQ_range
  have hsurj : Function.Surjective g :=
    LocalizedModule.map_surjective T _ (Submodule.mkQ_surjective _)
  -- Globalize the local criterion on the base ring, using Mathlib maximal localizations.
  have hui (L : Type (max u v w)) [AddCommGroup L] [Module R L] :
      Function.Injective (f.lTensor L) :=
    LinearMap.universally_injective_localizedModule_map.{u, u, u, v, max v w}
      T α hα L
  have : Module.Flat (Localization T) (LocalizedModule T (Fin r → A)) := inferInstance
  have : Module.Flat A (LocalizedModule T (Fin r → A)) :=
    Module.Flat.trans A (Localization T) _
  have : Module.Flat R (LocalizedModule T (Fin r → A)) := Module.Flat.trans R A _
  refine flat_iff_of_universally_injective.{u, u, max u v, max u v, w}
    (M := LocalizedModule T (Fin r → A)) (N := LocalizedModule T N)
    (P := LocalizedModule T (N ⧸ LinearMap.range α)) f g hex hsurj ?_
  intro L _ _
  exact hui L


/-- Generic basis subtraction (Stacks, Tag 05I3 and Tag 05CL).
(blueprint: lem-trf-free-subtraction-flatness)

The family `ξ` consists of the inverse images of the zero ideals in the fibre rings;
`hξ` specifies these primes uniquely. Geometric integrality guarantees that these
kernels are prime. `hgenericFlat` is flatness at these generic points, equivalently over
R_p. The map `α` becomes an isomorphism over each kappa(ξ(p)), as stated by `hgenericBasis`.
The cokernel is the actual quotient `N ⧸ LinearMap.range α`.

Proof: (1) Fix a base prime p and localize to R_p. Flatness, finite presentation, and
geometric integrality survive this base change. Apply
`lem-trf-local-generic-basis-universal-injective` (05I3) at the generic prime ξ(p):
`hgenericFlat` and `hgenericBasis` give universal injectivity of the base-localized map.
(2) For an arbitrary R-module L, identify the localization of α tensor L at p with
α_p tensor_R L, then identify the latter with α_p tensor_{R_p} (R_p tensor_R L).
The preceding universal injectivity makes it injective. Mathlib's
`injective_of_localized_maximal` globalizes this result on Spec R; tensor symmetry
and `ULift` give the exact testing universe in the statement.
(3) Localization preserves universal injectivity. Localizing the quotient sequence
and tensoring therefore gives universally short exact rows. If N_q is R-flat,
`Module.flat_of_universally_exact` makes its cokernel flat. Conversely, the localized
source is R-flat because A is R-flat, and the proved flat-extension theorem
`Module.Flat.of_exact_of_flat_of_flat` makes N_q flat when its cokernel is flat.
These are the universally exact cokernel argument of Tag 058P and the flat-extension
argument of Tag 00HM. No second application of the local generic-basis criterion at
q is needed. -/
theorem free_subtraction_flatness
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R A)))]
    (N : Type v) [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [Module.Finite A N] (r : ℕ) (α : (Fin r → A) →ₗ[A] N)
    (ξ : PrimeSpectrum R → PrimeSpectrum A)
    (hξ : ∀ p : PrimeSpectrum R,
      (ξ p).asIdeal = RingHom.ker
        (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.ResidueField ⊗[R] A))
    (hgenericFlat : ∀ p : PrimeSpectrum R,
      Module.Flat R (LocalizedModule (ξ p).asIdeal.primeCompl N))
    (hgenericBasis : ∀ p : PrimeSpectrum R,
      Function.Bijective (α.baseChange (ξ p).asIdeal.ResidueField)) :
    (∀ (L : Type (max u w)) [AddCommGroup L] [Module R L],
      Function.Injective ((α.restrictScalars R).lTensor L)) ∧
    ∀ q : PrimeSpectrum A,
      Module.Flat R (LocalizedModule q.asIdeal.primeCompl N) ↔
        Module.Flat R (LocalizedModule q.asIdeal.primeCompl (N ⧸ LinearMap.range α)) := by
  -- Globalize the local criterion on the base ring, using Mathlib maximal localizations.
  have hui (L : Type (max u v w)) [AddCommGroup L] [Module R L] :
      Function.Injective ((α.restrictScalars R).lTensor L) := by
    apply (LinearMap.lTensor_inj_iff_rTensor_inj
      (f := α.restrictScalars R) (M := L)).mpr
    apply injective_of_localized_maximal
    intro p hp
    exact localized_tensor_injective R A N r α ⟨p, inferInstance⟩
      (ξ ⟨p, inferInstance⟩) (hξ _) (hgenericFlat _) (hgenericBasis _) L
  constructor
  · intro L _ _
    exact tensor_injective_of_ulift.{u, u, v, w}
      (α.restrictScalars R) L (hui (ULift.{max u v w} L))
  · exact localized_flat_iff_quotient R A N r α hui

end Module
