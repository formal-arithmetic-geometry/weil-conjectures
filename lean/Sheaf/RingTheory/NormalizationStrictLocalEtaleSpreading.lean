/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Pi
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.BaseChange
import Sheaf.RingTheory.StrictHenselizationModuleFlatness
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Finite normalization models and strict-local etale spreading

Source: Stacks Project, Tags 032L, 0CBF, 02VN and 07RP.
(blueprint: lem-sfb-normalization-strict-local-etale-spreading).
-/

@[expose] public section

universe u v w t s

open scoped TensorProduct
open CategoryTheory

namespace Algebra

/-- The canonical map of normalization models after scalar extension along `B → D`.
Source: Stacks Project, Tags 02VN and 07RP, the base-changed affine morphism
(blueprint: lem-sfb-normalization-strict-local-etale-spreading). -/
def normalizationModelBaseChangeMap (B : Type u) (C : Type v) (F : Type w) (D : Type t)
    [CommRing B] [CommRing C] [CommRing F] [CommRing D]
    [Algebra B C] [Algebra C F] [Algebra B F] [IsScalarTower B C F] [Algebra B D] :
    C ⊗[B] D →+* (integralClosure C F) ⊗[B] D :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom B C (integralClosure C F))
    (AlgHom.id B D)).toRingHom

/-- The scalar extension of the actual inclusion of the normalization in the cover algebra.
Source: Stacks Project, Tag 0CBF, canonical localization restriction
(blueprint: lem-sfb-normalization-strict-local-etale-spreading). -/
def normalizationCoverBaseChangeMap (B : Type u) (C : Type v) (F : Type w) (D : Type t)
    [CommRing B] [CommRing C] [CommRing F] [CommRing D]
    [Algebra B C] [Algebra C F] [Algebra B F] [IsScalarTower B C F] [Algebra B D] :
    (integralClosure C F) ⊗[B] D →+* F ⊗[B] D :=
  (Algebra.TensorProduct.map ((integralClosure C F).val.restrictScalars B)
    (AlgHom.id B D)).toRingHom

private theorem finite_closure_etale_fraction
    (R : Type u) (K : Type v) (D : Type w)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing D] [Algebra K D] [Algebra R D] [IsScalarTower R K D]
    [Algebra.Etale K D] : Module.Finite R (integralClosure R D) := by
  classical
  obtain ⟨I, hI, L, hL, aL, e, hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K D).mp inferInstance
  let := hI
  let := hL
  let := aL
  let (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  have (i : I) : IsScalarTower R K (L i) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have (i : I) : Module.Finite K (L i) := (hfin i).1
  have (i : I) : Algebra.IsSeparable K (L i) := (hfin i).2
  have (i : I) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.finite R K (L i) (integralClosure R (L i))
  let f (i : I) : D →ₐ[R] L i :=
    ((Pi.evalAlgHom K L i).comp e.toAlgHom).restrictScalars R
  let f' : integralClosure R D →ₗ[R] ∀ i, integralClosure R (L i) :=
    { toFun := fun x i ↦ ⟨f i x, x.property.map (f i)⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply Module.Finite.of_injective f'
  intro x y hxy
  apply Subtype.ext
  apply e.injective
  funext i
  exact congrArg Subtype.val (congrFun hxy i)

private theorem strict_presentation_faithfullyFlat
    (R : Type u) (K A : Type (max u s)) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing A] [Algebra R A]
    (P : StrictHenselizationPresentationIn.{u, s} R K A) :
    Module.FaithfullyFlat R A := by
  have hh := (Module.flat_iff_strictHenselization R K A P A).mpr inferInstance
  have : Module.Flat R A := by
    convert hh using 1 <;> ext x y <;> first | rfl | exact Algebra.smul_def x y
  let r : A →ₐ[R] K := (P.identification.inv ≫
    P.isColimit.desc (strictHenselizationPointingCoconeIn R K)).hom
  have hker : Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) ≤
      RingHom.ker r.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change r (algebraMap R A x) = 0
    rw [r.commutes, IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) K]
    change algebraMap (IsLocalRing.ResidueField R) K (IsLocalRing.residue R x) = 0
    rw [(IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]
  refine ⟨fun m hm ↦ ?_⟩
  rw [Ideal.smul_top_eq_map, IsLocalRing.eq_maximalIdeal hm]
  apply (Submodule.restrictScalars_eq_top_iff _ _ _).ne.mpr
  intro h
  have : (1 : A) ∈ RingHom.ker r.toRingHom := hker (h ▸ (show (1 : A) ∈ (⊤ : Ideal A) from trivial))
  simp at this

private theorem cover_tensor_localization
    (B : Type u) (C : Type v) (F : Type w) (D : Type t)
    [CommRing B] [CommRing C] [CommRing F] [CommRing D]
    [Algebra B C] [Algebra C F] [Algebra B F] [IsScalarTower B C F] [Algebra B D]
    (g : C) [IsLocalization.Away (algebraMap C (integralClosure C F) g) F] :
    @IsLocalization ((integralClosure C F) ⊗[B] D) _
      (Submonoid.powers ((algebraMap C (integralClosure C F) g) ⊗ₜ[B] (1 : D)))
      (F ⊗[B] D) _ (normalizationCoverBaseChangeMap B C F D).toAlgebra := by
  let : Algebra ((integralClosure C F) ⊗[B] D) (F ⊗[B] D) :=
    (normalizationCoverBaseChangeMap B C F D).toAlgebra
  have : IsScalarTower (integralClosure C F) ((integralClosure C F) ⊗[B] D)
      (F ⊗[B] D) := .of_algebraMap_eq' (by ext x; rfl)
  have h := IsLocalization.tensorProduct_tensorProduct B D
    (Submonoid.powers (algebraMap C (integralClosure C F) g)) F (by ext x; rfl)
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using h

private theorem etale_locus_of_localization
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid S) [IsLocalization M T] [FormallyEtale R T] :
    Set.range (PrimeSpectrum.comap (algebraMap S T)) ⊆ etaleLocus R S := by
  rintro _ ⟨p, rfl⟩
  have : FormallyEtale T (Localization.AtPrime p.asIdeal) :=
    FormallyEtale.of_isLocalization p.asIdeal.primeCompl
  have : FormallyEtale R (Localization.AtPrime p.asIdeal) :=
    FormallyEtale.comp R T _
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal)
      (p.asIdeal.comap (algebraMap S T)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ _
  exact FormallyEtale.of_equiv
    ((IsLocalization.algEquiv (p.asIdeal.comap (algebraMap S T)).primeCompl
      (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime (p.asIdeal.comap (algebraMap S T)))).restrictScalars R)

private theorem formallyEtale_of_localization_locus
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid S) [IsLocalization M T]
    (h : Set.range (PrimeSpectrum.comap (algebraMap S T)) ⊆ etaleLocus R S) :
    FormallyEtale R T := by
  apply etaleLocus_eq_univ_iff.mp
  apply Set.eq_univ_of_forall
  intro p
  have : IsEtaleAt R (p.asIdeal.comap (algebraMap S T)) := h ⟨p, rfl⟩
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal)
      (p.asIdeal.comap (algebraMap S T)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ _
  exact FormallyEtale.of_equiv
    ((IsLocalization.algEquiv (p.asIdeal.comap (algebraMap S T)).primeCompl
      (Localization.AtPrime (p.asIdeal.comap (algebraMap S T)))
      (Localization.AtPrime p.asIdeal)).restrictScalars R)

private theorem finite_tensor_map
    (R : Type u) (S : Type v) (T : Type w) (D : Type t)
    [CommRing R] [CommRing S] [CommRing T] [CommRing D]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra R D] [Module.Finite S T] :
    (TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R D)).toRingHom.Finite := by
  let f := (TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R D)).toRingHom
  let : Algebra (S ⊗[R] D) (T ⊗[R] D) := f.toAlgebra
  have : IsScalarTower S (S ⊗[R] D) (T ⊗[R] D) :=
    .of_algebraMap_eq' (by ext x; rfl)
  have : IsPushout S T (S ⊗[R] D) (T ⊗[R] D) :=
    IsPushout.tensorProduct_tensorProduct R D S T (by
      ext x
      change algebraMap S T 1 ⊗ₜ[R] x = 1 ⊗ₜ[R] x
      rw [map_one])
  have : Module.Finite (S ⊗[R] D) ((S ⊗[R] D) ⊗[S] T) := inferInstance
  let e : (S ⊗[R] D) ⊗[S] T ≃ₐ[S ⊗[R] D] T ⊗[R] D :=
    AlgEquiv.ofRingEquiv (f :=
      (TensorProduct.comm S (S ⊗[R] D) T).toRingEquiv.trans
        (IsPushout.equiv S T (S ⊗[R] D) (T ⊗[R] D)).toRingEquiv)
      (by intro x; simp [IsPushout.equiv_tmul, ← TensorProduct.one_def])
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

private theorem etale_tensor_descent
    (R : Type u) (S : Type v) (T : Type w) (D : Type t)
    [CommRing R] [CommRing S] [CommRing T] [CommRing D]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra R D] [Module.FaithfullyFlat R D]
    (h : (TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (AlgHom.id R D)).toRingHom.Etale) : Etale S T := by
  let f := (TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R D)).toRingHom
  let : Algebra (S ⊗[R] D) (T ⊗[R] D) := f.toAlgebra
  have : IsScalarTower S (S ⊗[R] D) (T ⊗[R] D) :=
    .of_algebraMap_eq' (by ext x; rfl)
  have : IsPushout S T (S ⊗[R] D) (T ⊗[R] D) :=
    IsPushout.tensorProduct_tensorProduct R D S T (by
      ext x
      change algebraMap S T 1 ⊗ₜ[R] x = 1 ⊗ₜ[R] x
      rw [map_one])
  let e : (S ⊗[R] D) ⊗[S] T ≃ₐ[S ⊗[R] D] T ⊗[R] D :=
    AlgEquiv.ofRingEquiv (f :=
      (TensorProduct.comm S (S ⊗[R] D) T).toRingEquiv.trans
        (IsPushout.equiv S T (S ⊗[R] D) (T ⊗[R] D)).toRingEquiv)
      (by intro x; simp [IsPushout.equiv_tmul, ← TensorProduct.one_def])
  have : Etale (S ⊗[R] D) (T ⊗[R] D) := h
  have : Etale (S ⊗[R] D) ((S ⊗[R] D) ⊗[S] T) := .of_equiv e.symm
  exact Etale.of_etale_tensorProduct_of_faithfullyFlat (S ⊗[R] D)

private theorem etale_spread_finite
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [IsNoetherianRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Module.Finite R S] [Algebra S T] [Module.Finite S T]
    [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) [p.IsPrime]
    (hp : (TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (AlgHom.id R (Localization.AtPrime p))).toRingHom.Etale) :
    ∃ h : R, h ∉ p ∧
      (TensorProduct.map (IsScalarTower.toAlgHom R S T)
        (AlgHom.id R (Localization.Away h))).toRingHom.Etale := by
  classical
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have : FinitePresentation S T := FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Finite R T := Module.Finite.trans S T
  have : Algebra.IsIntegral R T := .of_finite _ _
  let D := Localization.AtPrime p
  let f := (TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R D)).toRingHom
  let : Algebra (S ⊗[R] D) (T ⊗[R] D) := f.toAlgebra
  have : IsScalarTower S (S ⊗[R] D) (T ⊗[R] D) :=
    .of_algebraMap_eq' (by ext x; rfl)
  have : Etale (S ⊗[R] D) (T ⊗[R] D) := hp
  have : FormallyEtale S (S ⊗[R] D) :=
    FormallyEtale.of_isLocalization (Algebra.algebraMapSubmonoid S p.primeCompl)
  have : FormallyEtale S (T ⊗[R] D) := FormallyEtale.comp S (S ⊗[R] D) _
  have hgood := etale_locus_of_localization S T (T ⊗[R] D)
    (Algebra.algebraMapSubmonoid T p.primeCompl)
  let bad : Set (PrimeSpectrum R) :=
    PrimeSpectrum.comap (algebraMap R T) '' (etaleLocus S T)ᶜ
  have hbad : IsClosed bad :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R T)
      (algebraMap_isIntegral_iff.mpr inferInstance) _ isOpen_etaleLocus.isClosed_compl
  have hpmem : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ badᶜ := by
    rintro ⟨q, hq, hqp⟩
    apply hq
    apply hgood
    rw [PrimeSpectrum.localization_comap_range (T ⊗[R] D)
      (Algebra.algebraMapSubmonoid T p.primeCompl)]
    change Disjoint (Algebra.algebraMapSubmonoid T p.primeCompl : Set T)
      (q.asIdeal : Set T)
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxq
    have hx' : x ∈ (PrimeSpectrum.comap (algebraMap R T) q).asIdeal := hxq
    rw [hqp] at hx'
    exact hx hx'
  obtain ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, hph, hh⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpmem hbad.isOpen_compl
  refine ⟨h, hph, ?_⟩
  let Dh := Localization.Away h
  let : Algebra Dh (T ⊗[R] Dh) := TensorProduct.rightAlgebra
  let fh := (TensorProduct.map (IsScalarTower.toAlgHom R S T) (AlgHom.id R Dh)).toRingHom
  let : Algebra (S ⊗[R] Dh) (T ⊗[R] Dh) := fh.toAlgebra
  have : IsScalarTower S (S ⊗[R] Dh) (T ⊗[R] Dh) :=
    .of_algebraMap_eq' (by ext x; rfl)
  have hgoodh : Set.range (PrimeSpectrum.comap (algebraMap T (T ⊗[R] Dh))) ⊆
      etaleLocus S T := by
    rintro q ⟨q', rfl⟩
    by_contra hq
    apply hh (show PrimeSpectrum.comap (algebraMap R T)
      (PrimeSpectrum.comap (algebraMap T (T ⊗[R] Dh)) q') ∈
        PrimeSpectrum.basicOpen h from ?_) ⟨_, hq, rfl⟩
    change algebraMap T (T ⊗[R] Dh) (algebraMap R T h) ∉ q'.asIdeal
    have hu : IsUnit (algebraMap R (T ⊗[R] Dh) h) := by
      rw [TensorProduct.algebraMap_apply']
      exact (IsLocalization.Away.algebraMap_isUnit h).map
        (algebraMap Dh (T ⊗[R] Dh))
    rw [← IsScalarTower.algebraMap_apply R T]
    exact fun hmem ↦ q'.isPrime.ne_top (q'.asIdeal.eq_top_of_isUnit_mem hmem hu)
  have : FormallyEtale S (T ⊗[R] Dh) :=
    formallyEtale_of_localization_locus S T (T ⊗[R] Dh)
      (Algebra.algebraMapSubmonoid T (Submonoid.powers h)) hgoodh
  have : FormallyEtale (S ⊗[R] Dh) (T ⊗[R] Dh) :=
    FormallyEtale.of_restrictScalars (R := S)
  have : IsNoetherianRing (S ⊗[R] Dh) :=
    IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid S (Submonoid.powers h)) _
      inferInstance
  have : Module.Finite (S ⊗[R] Dh) (T ⊗[R] Dh) := finite_tensor_map R S T Dh
  exact ⟨inferInstance, FinitePresentation.of_finiteType.mp inferInstance⟩

private theorem etale_of_equiv_square
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type t}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (f' : R' →+* S') (e : R ≃+* R') (d : S ≃+* S')
    (hcomm : d.toRingHom.comp f = f'.comp e.toRingHom) (h : f'.Etale) : f.Etale := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R' S' := f'.toAlgebra
  let : Algebra R R' := e.toRingHom.toAlgebra
  let : Algebra R S' := (f'.comp e.toRingHom).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq' rfl
  have : Etale R R' := RingHom.Etale.of_bijective e.bijective
  have : Etale R' S' := h
  have : Etale R S' := Etale.comp R R' S'
  let d' : S ≃ₐ[R] S' := AlgEquiv.ofRingEquiv (f := d) (fun x ↦ congrArg (fun k ↦ k x) hcomm)
  exact Etale.of_equiv d'.symm

attribute [local instance] TensorProduct.rightAlgebra in
private noncomputable def tensor_rebase
    (R : Type u) (L : Type v) (S : Type w) (D : Type t)
    [CommRing R] [CommRing L] [CommRing S] [CommRing D]
    [Algebra R L] [Algebra R S] [Algebra R D] [Algebra L D] [IsScalarTower R L D] :
    (S ⊗[R] L) ⊗[L] D ≃+* S ⊗[R] D :=
  (TensorProduct.comm L (S ⊗[R] L) D).toRingEquiv.trans
    ((TensorProduct.congr (AlgEquiv.refl : D ≃ₐ[L] D)
      (TensorProduct.commRight R L S).symm).toRingEquiv.trans
      ((TensorProduct.cancelBaseChange R L D D S).toRingEquiv.trans
        (TensorProduct.comm R D S).toRingEquiv))

attribute [local instance] TensorProduct.rightAlgebra in
private theorem tensor_rebase_tmul
    (R : Type u) (L : Type v) (S : Type w) (D : Type t)
    [CommRing R] [CommRing L] [CommRing S] [CommRing D]
    [Algebra R L] [Algebra R S] [Algebra R D] [Algebra L D] [IsScalarTower R L D]
    (x : S) (y : L) (z : D) :
    tensor_rebase R L S D ((x ⊗ₜ[R] y) ⊗ₜ[L] z) = x ⊗ₜ[R] (y • z) := by
  simp [tensor_rebase]

/-- Finite normalization over a normal Noetherian algebra, its canonical open comparison,
and descent of strict-local etaleness to a principal base neighbourhood.

Source: Stacks Project, Tags 032L, 0CBF, 02VN and 07RP.
(blueprint: lem-sfb-normalization-strict-local-etale-spreading).

Proof:
1. By lem-weil-pbc-finite-algebra-noetherian, C is Noetherian. Apply
   lem-sc-affine-noetherian-underlying-space and
   lem-trf-normal-topologically-noetherian-components to Spec C. Its finitely many disjoint
   clopen integral normal components correspond to a finite product C = product C_j.
   Injectivity of multiplication by g makes every g_j nonzero on a nonzero component.
   The zero ring has an empty family of components.
2. Project the finite etale C_g-algebra F to each component. Etaleness is preserved by
   lem-weil-pbc-etale-scheme-base-change; projection of finite generators gives finiteness.
   Apply lem-sbc-finite-etale-open-integral-closure on each component and then
   lem-weil-pbc-finite-product-integral-closure. Component generators, extended by zero,
   generate the integral closure E over C.
3. These module generators also generate E as an algebra. Apply
   lem-weil-pbc-finite-type-noetherian-finite-presentation: E is finitely presented over C.
   Thus Spec E → Spec C is locally of finite presentation; all schemes here are affine qcqs.
4. The inclusion E → F extends over g, a unit in F. It remains injective after localization.
   By lem-weil-pbc-finite-iff-integral-lft every x in F satisfies a monic equation over C_g.
   Clear its finitely many denominators by g^N. If its degree is n, y = g^N x satisfies
   y^n + sum (a_i g^(N*(n-i-1))) y^i = 0. Hence y is in E and x = y/g^N.
   This is precisely the canonical localization universal property asserted below.
5. Injective multiplication by g makes C → C_g injective and D(g) dense on every component.
   Apply lem-sbc-normal-dense-open-integral-section to extend every integral section from
   D(g) to Spec C. Conversely every image element satisfies T-c, giving integralClosure = ⊥.
6. By lem-sc-strict-henselization-faithfully-flat, B_v → A is faithfully flat. Apply
   lem-weil-pbc-faithfully-flat-base-change,
   lem-weil-pbc-faithfully-flat-surjective-spectrum and
   lem-weil-pbc-flat-ring-map-iff-flat-affine. The affine map Spec(C tensor A) →
   Spec(C tensor B_v) is a singleton fpqc cover. Tensor associativity identifies its pullback
   of the model with the assumed etale map. Apply lem-galois-fpqc-descend-etale.
7. The local ring B_v is the filtered colimit of B[1/product J], for finite subsets J of
   B outside v: fractions and their equalities occur at finite stages. By
   lem-weil-pbc-limit-affine-transition the spectra have limit Spec B_v. Apply
   lem-weil-pbc-descend-etale to the finitely presented model from step 3 and the etaleness
   of step 6. Some stage is etale. Its product h lies outside the prime v, including h = 1
   for the empty subset.
8. Tensor the finite generating family of E with 1 to obtain finiteness of this model.
   Localization commutes with this scalar extension: (e tensor d)/g^n maps to
   (e/g^n) tensor d, with the reverse formula giving its inverse. Under step 4 the target
   is F tensor B[1/h]. The same formula on C identifies the base with C_g tensor B[1/h].
   Both structural maps send c tensor d to its specified image, so the restricted cover
   is exactly the base change of F → C_g. The final localization property uses this actual
   tensor inclusion, rather than an unspecified isomorphism. -/
theorem normalization_strictLocal_etale_spreading
    (B : Type u) (C : Type v) [CommRing B] [CommRing C] [IsNoetherianRing B]
    [Algebra B C] [Module.Finite B C]
    (hnormal : ∀ (p : Ideal C) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (g : C) (hg : Function.Injective (fun c : C ↦ g * c))
    (F : Type w) [CommRing F] [Algebra (Localization.Away g) F]
    [Algebra C F] [IsScalarTower C (Localization.Away g) F]
    [Algebra B F] [IsScalarTower B C F]
    [Module.Finite (Localization.Away g) F] [Algebra.Etale (Localization.Away g) F] :
    Module.Finite C (integralClosure C F) ∧
      Algebra.FinitePresentation C (integralClosure C F) ∧
      IsLocalization.Away (algebraMap C (integralClosure C F) g) F ∧
      Function.Injective (algebraMap C (Localization.Away g)) ∧
      integralClosure C (Localization.Away g) = ⊥ ∧
      ∀ (v : Ideal B) [v.IsPrime]
        (K A : Type (max u s)) [Field K] [CommRing A]
        [Algebra (IsLocalRing.ResidueField (Localization.AtPrime v)) K]
        [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime v)) K]
        [Algebra (Localization.AtPrime v) K]
        [IsScalarTower (Localization.AtPrime v)
          (IsLocalRing.ResidueField (Localization.AtPrime v)) K]
        [Algebra (Localization.AtPrime v) A]
        [Algebra B A] [IsScalarTower B (Localization.AtPrime v) A],
        Algebra.StrictHenselizationPresentationIn.{u, s} (Localization.AtPrime v) K A →
        (normalizationModelBaseChangeMap B C F A).Etale →
        (normalizationModelBaseChangeMap B C F (Localization.AtPrime v)).Etale ∧
        ∃ h : B, h ∉ v ∧
          (normalizationModelBaseChangeMap B C F (Localization.Away h)).Finite ∧
          (normalizationModelBaseChangeMap B C F (Localization.Away h)).Etale ∧
          @IsLocalization ((integralClosure C F) ⊗[B] (Localization.Away h)) _
            (Submonoid.powers
              ((algebraMap C (integralClosure C F) g) ⊗ₜ[B] (1 : Localization.Away h)))
            (F ⊗[B] (Localization.Away h)) _
            (normalizationCoverBaseChangeMap B C F (Localization.Away h)).toAlgebra := by
  have : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  have hloc : IsLocalization.Away (algebraMap C (integralClosure C F) g) F := by
    have hunit : IsUnit (algebraMap C F g) := by
      rw [IsScalarTower.algebraMap_apply C (Localization.Away g) F]
      exact (IsLocalization.Away.algebraMap_isUnit g).map _
    have : Algebra.IsIntegral (Localization.Away g) F := .of_finite _ _
    refine ⟨?_, fun a ↦ ?_, fun {x y} h ↦ ⟨1, by simpa using Subtype.ext h⟩⟩
    · rintro ⟨_, n, rfl⟩
      rw [map_pow, ← IsScalarTower.algebraMap_apply]
      exact hunit.pow n
    · obtain ⟨⟨_, n, rfl⟩, h⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
        (Submonoid.powers g) (Rₘ := Localization.Away g) a
        (Algebra.IsIntegral.isIntegral a)
      refine ⟨(⟨_, h⟩, ⟨algebraMap C _ g ^ n, n, rfl⟩), ?_⟩
      change a * algebraMap _ F (algebraMap C _ g ^ n) = (g ^ n) • a
      rw [map_pow, ← IsScalarTower.algebraMap_apply, Algebra.smul_def, map_pow, mul_comm]
  have hinj : Function.Injective (algebraMap C (Localization.Away g)) := by
    apply IsLocalization.injective (Localization.Away g) (M := Submonoid.powers g)
    apply Submonoid.powers_le.mpr
    exact (⟨hg, fun a b h ↦ hg ((mul_comm g a).trans (h.trans (mul_comm b g)))⟩ :
      IsRegular g).mem_nonZeroDivisors
  have hclosed : IsIntegrallyClosedIn C (FractionRing C) :=
    (isIntegrallyClosed_iff (FractionRing C)).mpr
      (fun {x} hx ↦ integral_totalFraction_mem_range_of_normal C hnormal x hx)
  have hunits : ∀ z : Submonoid.powers g,
      IsUnit ((Algebra.ofId C (FractionRing C)) z) := by
    intro z
    apply IsLocalization.map_units (FractionRing C)
      (⟨z, (Submonoid.powers_le.mpr
        (⟨hg, fun a b h ↦ hg ((mul_comm g a).trans (h.trans (mul_comm b g)))⟩ :
          IsRegular g).mem_nonZeroDivisors) z.property⟩ : nonZeroDivisors C)
  let j : Localization.Away g →ₐ[C] FractionRing C := IsLocalization.liftAlgHom hunits
  have hj : Function.Injective j := by
    apply (IsLocalization.lift_injective_iff hunits).mpr
    intro x y
    exact ⟨fun h ↦ by simpa only [AlgHom.commutes, Algebra.ofId] using congrArg j h,
      fun h ↦ congrArg (algebraMap C (Localization.Away g))
        (IsFractionRing.injective C (FractionRing C) h)⟩
  have hclosedAway : IsIntegrallyClosedIn C (Localization.Away g) :=
    j.isIntegrallyClosedIn hj hclosed
  have hbot : integralClosure C (Localization.Away g) = ⊥ :=
    (IsIntegrallyClosedIn.integralClosure_eq_bot_iff _ hinj).mpr hclosedAway
  have hfinite : Module.Finite C (integralClosure C F) := by
    classical
    have : IsReduced C := isReduced_ofLocalizationMaximal C fun p hp ↦ by
      have : p.IsMaximal := hp
      have : IsDomain (Localization.AtPrime p) := (hnormal p).1
      infer_instance
    obtain ⟨n, R, hR, ⟨e⟩⟩ :=
      (reduced_normal_iff_integrallyClosed_totalFractions C
        (minimalPrimes.finite_of_isNoetherianRing (R := C))).2.mp hclosed
    let (i : Fin n) : Algebra C (R i) :=
      ((Pi.evalRingHom (fun j ↦ R j) i).comp e.toRingHom).toAlgebra
    have (i : Fin n) : IsDomain (R i) := (hR i).1
    have (i : Fin n) : IsIntegrallyClosed (R i) := (hR i).2
    have hsurj (i : Fin n) : Function.Surjective (algebraMap C (R i)) :=
      (Pi.evalRingHom (fun j ↦ R j) i).surjective.comp e.surjective
    have (i : Fin n) : IsNoetherianRing (R i) :=
      isNoetherianRing_of_surjective C (R i) (algebraMap C (R i)) (hsurj i)
    have (i : Fin n) : Module.Finite C (R i) :=
      Module.Finite.of_surjective (Algebra.linearMap C (R i)) (hsurj i)
    let K (i : Fin n) := FractionRing (R i)
    have hgi (i : Fin n) : algebraMap C (R i) g ≠ 0 := by
      intro hz
      let x := e.symm (Pi.single i 1)
      have hx : g * x = 0 := by
        apply e.injective
        ext j
        by_cases hji : j = i
        · subst j
          simpa [x] using (show e g i = 0 from hz)
        · simp [x, Pi.single_eq_of_ne hji]
      have hxx : x = 0 := hg (hx.trans (mul_zero g).symm)
      have := congrFun (congrArg e hxx) i
      simp [x] at this
    let q (i : Fin n) : Localization.Away g →ₐ[C] K i :=
      IsLocalization.liftAlgHom (M := Submonoid.powers g)
        (fun z ↦ show IsUnit ((Algebra.ofId C (K i)) z) by
        obtain ⟨m, hm⟩ := z.property
        have hu : IsUnit (algebraMap C (K i) g) := by
          apply isUnit_iff_ne_zero.mpr
          simpa only [IsScalarTower.algebraMap_apply C (R i) (K i), map_zero] using
            (IsFractionRing.injective (R i) (K i)).ne (hgi i)
        change IsUnit (algebraMap C (K i) z)
        rw [← hm, map_pow]
        exact hu.pow m)
    let (i : Fin n) : Algebra (Localization.Away g) (K i) := (q i).toRingHom.toAlgebra
    have (i : Fin n) : IsScalarTower C (Localization.Away g) (K i) :=
      IsScalarTower.of_algebraMap_eq' (q i).comp_algebraMap.symm
    let D (i : Fin n) := K i ⊗[Localization.Away g] F
    have (i : Fin n) : Module.Finite (R i) (integralClosure (R i) (D i)) :=
      finite_closure_etale_fraction (R i) (K i) (D i)
    have (i : Fin n) : Module.Finite C (integralClosure (R i) (D i)) :=
      Module.Finite.trans (R i) _
    let f (i : Fin n) : F →ₐ[C] D i :=
      (Algebra.TensorProduct.includeRight : F →ₐ[Localization.Away g] D i).restrictScalars C
    have hq : Function.Injective (algebraMap (Localization.Away g) (∀ i, K i)) := by
      apply (IsLocalization.injective_iff_map_algebraMap_eq
        (Submonoid.powers g) _).mpr
      intro a b
      constructor
      · intro h
        exact congrArg (algebraMap (Localization.Away g) (∀ i, K i)) h
      · intro h
        apply congrArg (algebraMap C (Localization.Away g))
        apply e.injective
        funext i
        apply IsFractionRing.injective (R i) (K i)
        have hi := congrFun h i
        change (q i) (algebraMap C (Localization.Away g) a) =
          (q i) (algebraMap C (Localization.Away g) b) at hi
        have hi' : algebraMap C (K i) a = algebraMap C (K i) b := by
          simpa only [AlgHom.commutes] using hi
        change algebraMap (R i) (K i) (algebraMap C (R i) a) =
          algebraMap (R i) (K i) (algebraMap C (R i) b)
        simpa only [← IsScalarTower.algebraMap_apply C (R i) (K i)] using hi'
    have hf : Function.Injective (fun x : F ↦ fun i ↦ f i x) := by
      intro x y hxy
      apply Algebra.TensorProduct.includeLeft_injective (S := F) hq
      apply (Algebra.TensorProduct.piRight (Localization.Away g)
        (Localization.Away g) F K).injective
      ext i
      apply (Algebra.TensorProduct.comm (Localization.Away g) F (K i)).injective
      exact congrFun hxy i
    let f' : integralClosure C F →ₗ[C] ∀ i, integralClosure (R i) (D i) :=
      { toFun := fun x i ↦ ⟨f i x, (x.property.map (f i)).tower_top⟩
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp }
    apply Module.Finite.of_injective f'
    intro x y hxy
    apply Subtype.ext
    apply hf
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  have : Module.Finite C (integralClosure C F) := hfinite
  refine ⟨hfinite, Algebra.FinitePresentation.of_finiteType.mp inferInstance,
    hloc, hinj, hbot, ?_⟩
  intro p _ K A _ _ _ _ _ _ _ _ _ P hA
  let L := Localization.AtPrime p
  let E := integralClosure C F
  let : Algebra L (C ⊗[B] L) := TensorProduct.rightAlgebra
  let : Algebra L (E ⊗[B] L) := TensorProduct.rightAlgebra
  let : Algebra (C ⊗[B] L) (E ⊗[B] L) :=
    (normalizationModelBaseChangeMap B C F L).toAlgebra
  have : IsScalarTower L (C ⊗[B] L) (E ⊗[B] L) := .of_algebraMap_eq' (by
    ext x
    change 1 ⊗ₜ[B] x = algebraMap C E 1 ⊗ₜ[B] x
    rw [map_one])
  have : Module.FaithfullyFlat L A := strict_presentation_faithfullyFlat L K A P
  have hAL : (TensorProduct.map
      (IsScalarTower.toAlgHom L (C ⊗[B] L) (E ⊗[B] L))
      (AlgHom.id L A)).toRingHom.Etale := by
    apply etale_of_equiv_square _ (normalizationModelBaseChangeMap B C F A)
      (tensor_rebase B L C A) (tensor_rebase B L E A) ?_ hA
    apply RingHom.ext
    intro q
    induction q using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x z =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul x y =>
        change tensor_rebase B L E A
            ((algebraMap C E x ⊗ₜ[B] y) ⊗ₜ[L] z) =
          normalizationModelBaseChangeMap B C F A
            (tensor_rebase B L C A ((x ⊗ₜ[B] y) ⊗ₜ[L] z))
        rw [tensor_rebase_tmul, tensor_rebase_tmul]
        rfl
  have hL : (normalizationModelBaseChangeMap B C F L).Etale :=
    etale_tensor_descent L (C ⊗[B] L) (E ⊗[B] L) A hAL
  refine ⟨hL, ?_⟩
  obtain ⟨h, hhp, hhet⟩ := etale_spread_finite B C E p hL
  exact ⟨h, hhp, finite_tensor_map B C E (Localization.Away h), hhet,
    cover_tensor_localization B C F (Localization.Away h) g⟩

end Algebra
