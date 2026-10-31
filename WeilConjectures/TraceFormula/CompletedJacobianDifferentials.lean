/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.PiTopology
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.MvPowerSeries.Inverse
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import WeilConjectures.RingTheory.CompletionKaehlerDifferentialComparison
import WeilConjectures.RingTheory.FormalPowerSeriesContinuousDifferentials

/-!
# Jacobian presentation of completed Kähler differentials

Source: Stacks Project, Curves, Tag 0C4D, with the coefficient-field section of
Varieties, Tag 0C52 (blueprint: lem-trf-completed-jacobian-differentials).

The auxiliary completed-presentation comparison is the one recorded in the DAG;
Tag 0C4D itself states the polynomial Jacobian presentation.

## Main definitions

* `completedResidueMap`: reduction to the specified residue field `S/p`.
* `completedDifferentialTarget`: the written tensor target `Ω[A/k] ⊗[A] Â`.
* `IsCompletedDifferentialExtension`: continuity and the two characterizing identities.
* `completedJacobianMatrix` and `completedDifferentialCoordinateMap`: the explicit maps.

## Main statements

* `completedJacobianDifferentials`: the unique extension and its Jacobian cokernel isomorphism.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public noncomputable section

universe u v

open scoped BigOperators

namespace AlgebraicGeometry

/-- The localization `A = Sₚ`.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
abbrev completedLocalRing (S : Type v) [CommRing S] (p : Ideal S) [p.IsPrime] :=
  Localization.AtPrime p

/-- The maximal ideal `pA` of the localized ring.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
abbrev completedIdeal (S : Type v) [CommRing S] (p : Ideal S) [p.IsPrime] :=
  IsLocalRing.maximalIdeal (completedLocalRing S p)

/-- The maximal-ideal completion of `Sₚ`, with its canonical algebra map.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
abbrev completedRing (S : Type v) [CommRing S] (p : Ideal S) [p.IsPrime] :=
  AdicCompletion (completedIdeal S p) (completedLocalRing S p)

/-- The tensor product `Ω[A/k] ⊗[A] Â`, in the order specified in the node.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
def completedDifferentialTarget (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :=
  TensorProduct (completedLocalRing S p)
    (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)
deriving SMul k, AddCommGroup, Module k, SMul (completedLocalRing S p),
  Module (completedLocalRing S p)

/-- The action on the right tensor factor, transported through tensor symmetry.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable instance completedDifferentialTargetSMul
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :
    SMul (completedRing S p) (completedDifferentialTarget k S p) where
  smul c x :=
    (TensorProduct.comm (completedLocalRing S p)
      (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)).symm
      (c • (TensorProduct.comm (completedLocalRing S p)
        (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)) x)

/-- The completion-module structure on the written tensor target `Ω ⊗ Â`.
Source: Stacks Project, Curves, Tag 0C4D
(blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable instance completedDifferentialTargetModule
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :
    Module (completedRing S p) (completedDifferentialTarget k S p) :=
  let e : completedDifferentialTarget k S p ≃ₗ[completedLocalRing S p]
      TensorProduct (completedLocalRing S p) (completedRing S p)
        (KaehlerDifferential k (completedLocalRing S p)) :=
    TensorProduct.comm (completedLocalRing S p)
      (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)
  { Function.Injective.module (completedRing S p) e.toAddMonoidHom e.injective
      (fun _ _ ↦ e.apply_symm_apply _) with
    smul := (completedDifferentialTargetSMul k S p).smul }

/-- The canonical residue map: evaluate a compatible sequence modulo `pA`, then
identify `A/pA` with `S/p` by the localization residue-field equivalence.
Source: Stacks Project, Varieties, Tag 0C52
(blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable def completedResidueMap
    {S : Type v} [CommRing S]
    (p : Ideal S) [p.IsMaximal] [p.IsPrime] :
    completedRing S p →+* (S ⧸ p) :=
  ((IsLocalization.AtPrime.equivQuotMaximalIdeal p (completedLocalRing S p)).symm.toRingHom).comp
    (AdicCompletion.evalOneₐ (completedIdeal S p)).toRingHom

/-- A continuous extension of the universal derivation that vanishes on the coefficient field.
Continuity is the ideal-power criterion for the indicated adic ring and module topologies.
Source: Stacks Project, Curves, Tag 0C4D; More Algebra, Tag 0C34
(blueprint: lem-trf-completed-jacobian-differentials). -/
def IsCompletedDifferentialExtension
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime]
    (σ : (S ⧸ p) →ₐ[k] completedRing S p)
    (dhat : Derivation k (completedRing S p) (completedDifferentialTarget k S p)) : Prop :=
  (∀ r : ℕ, ∃ N : ℕ, ∀ z : completedRing S p,
      z ∈ (Ideal.map (algebraMap (completedLocalRing S p) (completedRing S p))
        (completedIdeal S p)) ^ N →
      dhat z ∈ (Ideal.map (algebraMap (completedLocalRing S p) (completedRing S p))
        (completedIdeal S p)) ^ r •
        (⊤ : Submodule (completedRing S p) (completedDifferentialTarget k S p))) ∧
  (∀ a : completedLocalRing S p,
      dhat (AdicCompletion.of (completedIdeal S p) (completedLocalRing S p) a) =
        TensorProduct.tmul (completedLocalRing S p)
          ((KaehlerDifferential.D k (completedLocalRing S p)) a) (1 : completedRing S p)) ∧
  (∀ c : S ⧸ p, dhat (σ c) = 0)

/-- The Jacobian matrix after a continuous formal-power-series presentation.

Source: Stacks Project, Curves, Tag 0C4D (blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable def completedJacobianMatrix
    {S : Type v} [CommRing S]
    (p : Ideal S) [p.IsPrime]
    (n s : ℕ) (f : Fin s → MvPowerSeries (Fin n) (S ⧸ p))
    (π : MvPowerSeries (Fin n) (S ⧸ p) →+* completedRing S p) :
    Matrix (Fin n) (Fin s) (completedRing S p) :=
  fun i j ↦ π ((MvPowerSeries.pderiv (S ⧸ p) i) (f j))

/-- The coordinate map sending the formal variables to their continuous differentials.

Source: Stacks Project, Curves, Tag 0C4D (blueprint: lem-trf-completed-jacobian-differentials). -/
noncomputable def completedDifferentialCoordinateMap
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime]
    (n : ℕ)
    (π : MvPowerSeries (Fin n) (S ⧸ p) →+* completedRing S p)
    (dhat : Derivation k (completedRing S p) (completedDifferentialTarget k S p)) :
    (Fin n → completedRing S p) →ₗ[completedRing S p]
      completedDifferentialTarget k S p :=
  Fintype.linearCombination _ (fun i ↦ dhat (π (MvPowerSeries.X i)))

private noncomputable def completedTensorComm
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :
    completedDifferentialTarget k S p ≃ₗ[completedRing S p]
      Algebra.CompletedDifferentials k (completedLocalRing S p) :=
  { TensorProduct.comm (completedLocalRing S p)
      (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p) with
    map_smul' := fun c x ↦ by
      change _ = c • _
      exact LinearEquiv.apply_symm_apply _ _ }

private instance completedTensorTower
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :
    IsScalarTower k (completedRing S p) (completedDifferentialTarget k S p) where
  smul_assoc a c x := by
    apply (completedTensorComm k S p).injective
    simp only [map_smul]
    change (a • c) • (TensorProduct.comm (completedLocalRing S p)
      (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p)) x =
      (TensorProduct.comm (completedLocalRing S p)
        (KaehlerDifferential k (completedLocalRing S p)) (completedRing S p))
        (a • (c • x))
    rw [smul_assoc, LinearMapClass.map_smul_of_tower]
    exact congrArg (fun y ↦ a • y) ((completedTensorComm k S p).map_smul c x).symm

private theorem completedTensorComm_tmul
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] (x : KaehlerDifferential k (completedLocalRing S p))
    (y : completedRing S p) :
    completedTensorComm k S p (TensorProduct.tmul (completedLocalRing S p) x y) =
      TensorProduct.tmul (completedLocalRing S p) y x := TensorProduct.comm_tmul _ _ _ _ _


private noncomputable def tensorDerivationEquiv
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime] :
    Derivation k (completedRing S p) (completedDifferentialTarget k S p) ≃ₗ[completedRing S p]
      Derivation k (completedRing S p)
        (Algebra.CompletedDifferentials k (completedLocalRing S p)) :=
  (completedTensorComm k S p).compDer

private theorem tensorDerivationEquiv_apply
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime]
    (D : Derivation k (completedRing S p) (completedDifferentialTarget k S p))
    (x : completedRing S p) :
    tensorDerivationEquiv k S p D x = completedTensorComm k S p (D x) := rfl

private theorem tensorDerivationEquiv_symm_apply
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (p : Ideal S) [p.IsPrime]
    (D : Derivation k (completedRing S p)
      (Algebra.CompletedDifferentials k (completedLocalRing S p))) (x : completedRing S p) :
    completedTensorComm k S p ((tensorDerivationEquiv k S p).symm D x) = D x :=
  (completedTensorComm k S p).apply_symm_apply _

attribute [irreducible] tensorDerivationEquiv completedTensorComm

private theorem linearEquiv_mem_ideal_smul
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) (I : Ideal R) (x : M) :
    e x ∈ I • (⊤ : Submodule R N) ↔ x ∈ I • (⊤ : Submodule R M) := by
  have he : (I • (⊤ : Submodule R M)).map e.toLinearMap = I • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  rw [← he, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact e.injective hxy ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

attribute [local irreducible] KaehlerDifferential.D KaehlerDifferential.map

private noncomputable def differentialMap
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F →+* G) (g : A →+* B)
    (h : g.comp (algebraMap F A) = (algebraMap G B).comp f) :
    KaehlerDifferential F A →ₛₗ[g] KaehlerDifferential G B := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := ((algebraMap G B).comp f).toAlgebra
  letI : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq' h.symm
  letI : IsScalarTower F G B := IsScalarTower.of_algebraMap_eq' rfl
  exact
    { toFun := KaehlerDifferential.map F G A B
      map_add' := map_add _
      map_smul' := fun a x ↦ (KaehlerDifferential.map F G A B).map_smul a x }

private theorem differentialMap_D
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F →+* G) (g : A →+* B)
    (h : g.comp (algebraMap F A) = (algebraMap G B).comp f) (x : A) :
    differentialMap f g h (KaehlerDifferential.D F A x) =
      KaehlerDifferential.D G B (g x) := by
  let := f.toAlgebra
  let := g.toAlgebra
  let := ((algebraMap G B).comp f).toAlgebra
  have : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq' h.symm
  have : IsScalarTower F G B := IsScalarTower.of_algebraMap_eq' rfl
  exact KaehlerDifferential.map_D F G A B x

attribute [irreducible] differentialMap

private theorem differential_induction
    {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
    {P : KaehlerDifferential F A → Prop}
    (hD : ∀ a, P (KaehlerDifferential.D F A a)) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (a : A) x, P x → P (a • x)) (x : KaehlerDifferential F A) : P x := by
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D F A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hD a
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => exact hsmul a x hx

private noncomputable def quotientMap
    {A B : Type*} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) (J : Ideal B) (h : I.map g ≤ J) (r : ℕ) :
    (A ⧸ I ^ r) →+* (B ⧸ J ^ r) :=
  Ideal.quotientMap (J ^ r) g (Ideal.map_le_iff_le_comap.mp
    ((Ideal.map_pow g I r).le.trans (pow_le_pow_left' h r)))

private noncomputable def quotientDifferentialMap
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F →+* G) (g : A →+* B)
    (h : g.comp (algebraMap F A) = (algebraMap G B).comp f)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map g ≤ J) (r : ℕ) :
    KaehlerDifferential F (A ⧸ I ^ r) →ₛₗ[g]
      KaehlerDifferential G (B ⧸ J ^ r) where
  toFun := differentialMap f (quotientMap g I J hIJ r) (by
    ext c
    exact congrArg (Ideal.Quotient.mk (J ^ r)) (RingHom.congr_fun h c))
  map_add' := map_add _
  map_smul' a x := by
    change differentialMap _ _ _ ((Ideal.Quotient.mk (I ^ r) a) • x) = _
    rw [map_smulₛₗ]
    rfl

private theorem quotientDifferentialMap_D
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F →+* G) (g : A →+* B)
    (h : g.comp (algebraMap F A) = (algebraMap G B).comp f)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map g ≤ J) (r : ℕ) (x : A) :
    quotientDifferentialMap f g h I J hIJ r
      (KaehlerDifferential.D F _ (Ideal.Quotient.mk _ x)) =
        KaehlerDifferential.D G _ (Ideal.Quotient.mk _ (g x)) :=
  differentialMap_D f (quotientMap g I J hIJ r) (by
    ext c
    exact congrArg (Ideal.Quotient.mk (J ^ r)) (RingHom.congr_fun h c))
    (Ideal.Quotient.mk _ x)

attribute [irreducible] quotientDifferentialMap

private theorem quotientDifferentialMap_transition
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F →+* G) (g : A →+* B)
    (h : g.comp (algebraMap F A) = (algebraMap G B).comp f)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map g ≤ J) (r : ℕ)
    (x : KaehlerDifferential F (A ⧸ I ^ (r + 2))) :
    KaehlerDifferential.adicTransition G B J r
      (quotientDifferentialMap f g h I J hIJ (r + 2) x) =
    quotientDifferentialMap f g h I J hIJ (r + 1)
      (KaehlerDifferential.adicTransition F A I r x) := by
  induction x using differential_induction with
  | hD a =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp only [quotientDifferentialMap_D, KaehlerDifferential.adicTransition,
      LinearMap.restrictScalars_apply, KaehlerDifferential.map_D]
    change KaehlerDifferential.D G _ (Ideal.Quotient.mk _ (g a)) =
      quotientDifferentialMap f g h I J hIJ (r + 1)
        (KaehlerDifferential.D F _ (Ideal.Quotient.mk _ a))
    exact (quotientDifferentialMap_D f g h I J hIJ (r + 1) a).symm
  | h0 => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul a x hx =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change KaehlerDifferential.adicTransition G B J r
      (quotientDifferentialMap f g h I J hIJ (r + 2) (a • x)) = _
    change KaehlerDifferential.adicTransition G B J r
      (quotientDifferentialMap f g h I J hIJ (r + 2) (a • x)) =
      quotientDifferentialMap f g h I J hIJ (r + 1)
        (KaehlerDifferential.adicTransition F A I r (a • x))
    simp only [map_smulₛₗ, hx, RingHom.id_apply]

private noncomputable def continuousDifferentialMap
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F →+* G) (g : A →+* B)
    (h : g.comp (algebraMap F A) = (algebraMap G B).comp f)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map g ≤ J) :
    KaehlerDifferential.Continuous F A I →ₛₗ[g] KaehlerDifferential.Continuous G B J where
  toFun x := ⟨fun r ↦ quotientDifferentialMap f g h I J hIJ (r + 1) (x.val r), by
    intro r
    rw [quotientDifferentialMap_transition, x.property r]⟩
  map_add' x y := by apply Subtype.ext; funext r; exact map_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    funext r
    exact (quotientDifferentialMap f g h I J hIJ (r + 1)).map_smulₛₗ a (x.val r)

private theorem continuousDifferentialMap_D
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F →+* G) (g : A →+* B)
    (h : g.comp (algebraMap F A) = (algebraMap G B).comp f)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map g ≤ J) (x : A) :
    continuousDifferentialMap f g h I J hIJ
      (KaehlerDifferential.continuousD F A I x) =
        KaehlerDifferential.continuousD G B J (g x) := by
  apply Subtype.ext
  funext r
  exact quotientDifferentialMap_D _ _ _ _ _ _ _ _

private theorem quotientDifferentialMap_inverse
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F ≃+* G) (g : A ≃+* B)
    (h : g.toRingHom.comp (algebraMap F A) = (algebraMap G B).comp f.toRingHom)
    (h' : g.symm.toRingHom.comp (algebraMap G B) =
      (algebraMap F A).comp f.symm.toRingHom)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map g.toRingHom ≤ J)
    (hJI : J.map g.symm.toRingHom ≤ I) (r : ℕ)
    (x : KaehlerDifferential F (A ⧸ I ^ r)) :
    quotientDifferentialMap f.symm.toRingHom g.symm.toRingHom h' J I hJI r
      (quotientDifferentialMap f.toRingHom g.toRingHom h I J hIJ r x) = x := by
  induction x using differential_induction with
  | hD a =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [quotientDifferentialMap_D, quotientDifferentialMap_D]
    exact congrArg (fun a ↦ KaehlerDifferential.D F _ (Ideal.Quotient.mk _ a))
      (g.symm_apply_apply a)
  | h0 => simp
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hsmul a x hx =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change quotientDifferentialMap _ _ _ _ _ _ _
      (quotientDifferentialMap _ _ _ _ _ _ _ (a • x)) = a • x
    simp only [map_smulₛₗ, hx]
    exact congrArg (fun a ↦ a • x) (g.symm_apply_apply a)

private instance ringEquivInvPair {A B : Type*} [CommRing A] [CommRing B]
    (g : A ≃+* B) : RingHomInvPair g.toRingHom g.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv g

private instance ringEquivInvPair' {A B : Type*} [CommRing A] [CommRing B]
    (g : A ≃+* B) : RingHomInvPair g.symm.toRingHom g.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm g

private noncomputable def continuousDifferentialEquiv
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F ≃+* G) (g : A ≃+* B)
    (h : g.toRingHom.comp (algebraMap F A) = (algebraMap G B).comp f.toRingHom)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map g.toRingHom = J) :
    LinearEquiv g.toRingHom (σ' := g.symm.toRingHom)
      (KaehlerDifferential.Continuous F A I) (KaehlerDifferential.Continuous G B J) := by
  have h' : g.symm.toRingHom.comp (algebraMap G B) =
      (algebraMap F A).comp f.symm.toRingHom := by
    ext c
    apply g.injective
    simpa using (RingHom.congr_fun h (f.symm c)).symm
  have hJI : J.map g.symm.toRingHom ≤ I := by
    rw [← hIJ, Ideal.map_map]
    simp
  exact
    { continuousDifferentialMap f.toRingHom g.toRingHom h I J hIJ.le with
      invFun := continuousDifferentialMap f.symm.toRingHom g.symm.toRingHom h' J I hJI
      left_inv := fun x ↦ by
        apply Subtype.ext
        funext r
        exact quotientDifferentialMap_inverse f g h h' I J hIJ.le hJI (r + 1) (x.val r)
      right_inv := fun x ↦ by
        apply Subtype.ext
        funext r
        exact quotientDifferentialMap_inverse f.symm g.symm h' h J I hJI hIJ.le
          (r + 1) (x.val r) }

private theorem continuousDifferentialEquiv_D
    {F G A B : Type*} [CommRing F] [CommRing G] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra G B] (f : F ≃+* G) (g : A ≃+* B)
    (h : g.toRingHom.comp (algebraMap F A) = (algebraMap G B).comp f.toRingHom)
    (I : Ideal A) (J : Ideal B) (hIJ : I.map g.toRingHom = J) (x : A) :
    continuousDifferentialEquiv f g h I J hIJ (KaehlerDifferential.continuousD F A I x) =
      KaehlerDifferential.continuousD G B J (g x) :=
  continuousDifferentialMap_D _ _ _ _ _ _ _

attribute [irreducible] continuousDifferentialEquiv continuousDifferentialMap

private noncomputable def positiveDifferentialEquiv
    (F A : Type*) [CommRing F] [CommRing A] [Algebra F A] (I : Ideal A) :
    KaehlerDifferential.adicContinuousDifferentials F A I ≃ₗ[A]
      KaehlerDifferential.Continuous F A I := by
  let q : KaehlerDifferential.adicContinuousDifferentials F A I →ₗ[A]
      KaehlerDifferential.Continuous F A I :=
    { toFun := fun x ↦ ⟨fun r ↦ x.val (r + 1), by
        intro r
        have hx := x.property
        simp only [KaehlerDifferential.adicContinuousDifferentials,
          Submodule.mem_iInf, LinearMap.mem_ker] at hx
        have hx := hx (r + 1)
        change KaehlerDifferential.adicTransition F A I r (x.val (r + 2)) -
          x.val (r + 1) = 0 at hx
        exact sub_eq_zero.mp hx⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hz : Subsingleton (KaehlerDifferential F (A ⧸ I ^ 0)) := by
    have : Subsingleton (A ⧸ I ^ 0) := by simp only [pow_zero, Ideal.one_eq_top]; infer_instance
    exact KaehlerDifferential.subsingleton_of_surjective F (A ⧸ I ^ 0)
      (fun x ↦ ⟨0, Subsingleton.elim _ _⟩)
  exact
    { q with
      invFun := fun x ↦ ⟨fun r ↦ match r with | 0 => 0 | r + 1 => x.val r, by
        simp only [KaehlerDifferential.adicContinuousDifferentials,
          Submodule.mem_iInf, LinearMap.mem_ker]
        intro r
        change KaehlerDifferential.adicTransitionZero F A I r _ - _ = 0
        cases r with
        | zero => exact Subsingleton.elim _ _
        | succ r => exact sub_eq_zero.mpr (x.property r)⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        funext r
        cases r with
        | zero => exact Subsingleton.elim _ _
        | succ r => rfl
      right_inv := fun x ↦ rfl }

private theorem positiveDifferentialEquiv_val
    (F A : Type*) [CommRing F] [CommRing A] [Algebra F A] (I : Ideal A)
    (x : KaehlerDifferential.adicContinuousDifferentials F A I) (r : ℕ) :
    (positiveDifferentialEquiv F A I x).val r = x.val (r + 1) := rfl

attribute [irreducible] positiveDifferentialEquiv

private theorem variables_eq_maximalIdeal (F : Type*) [Field F] (n : ℕ) :
    MvPowerSeries.coordinateIdeal F n =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) F) := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    not_not]
  have hx := power_series_mem_combined_ideal_pow_iff F (⊥ : Ideal F) n 1 x
  simpa only [Ideal.map_bot, bot_sup_eq, pow_one, MvPowerSeries.coordinateIdeal,
    Finsupp.degree_eq_zero_iff, Nat.lt_one_iff, forall_eq, tsub_zero, Ideal.mem_bot,
    map_zero, Nat.sub_zero,
    MvPowerSeries.coeff_zero_eq_constantCoeff] using hx

private noncomputable def finsuppTransport
    {R T : Type*} [CommRing R] [CommRing T] (e : R ≃+* T) (n : ℕ) :
    LinearEquiv e.toRingHom (σ' := e.symm.toRingHom) (Fin n →₀ R) (Fin n → T) :=
  { toFun := fun v i ↦ e (v i)
    invFun := fun v ↦ Finsupp.equivFunOnFinite.symm (fun i ↦ e.symm (v i))
    map_add' := by intro v w; funext i; exact map_add _ _ _
    map_smul' := by intro c v; funext i; exact map_mul _ _ _
    left_inv := by intro v; ext i; exact e.symm_apply_apply _
    right_inv := by intro v; funext i; exact e.apply_symm_apply _ }

private theorem finsuppTransport_single
    {R T : Type*} [CommRing R] [CommRing T] (e : R ≃+* T) (n : ℕ) (i : Fin n) :
    finsuppTransport e n (Finsupp.single i 1) = Pi.single i 1 := by
  classical
  ext j
  simp [finsuppTransport, Finsupp.single_apply, Pi.single_apply, eq_comm]

private theorem finsuppTransport_apply
    {R T : Type*} [CommRing R] [CommRing T] (e : R ≃+* T) (n : ℕ)
    (v : Fin n →₀ R) (i : Fin n) : finsuppTransport e n v i = e (v i) := rfl

attribute [irreducible] finsuppTransport

private noncomputable def transportLinearEquiv
    {R T M N P Q : Type*} [CommRing R] [CommRing T]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module T N] [Module R P] [Module T Q]
    (g : R ≃+* T)
    (a : LinearEquiv g.toRingHom (σ' := g.symm.toRingHom) M N)
    (e : M ≃ₗ[R] P)
    (b : LinearEquiv g.toRingHom (σ' := g.symm.toRingHom) P Q) : N ≃ₗ[T] Q where
  toFun x := b (e (a.symm x))
  invFun y := a (e.symm (b.symm y))
  left_inv x := by
    dsimp only
    rw [b.symm_apply_apply, e.symm_apply_apply, a.apply_symm_apply]
  right_inv y := by
    dsimp only
    rw [a.symm_apply_apply, e.apply_symm_apply, b.apply_symm_apply]
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    simp only [map_smulₛₗ]
    exact congrArg (fun c ↦ c • b (e (a.symm x))) (g.apply_symm_apply c)

private theorem transportLinearEquiv_apply
    {R T M N P Q : Type*} [CommRing R] [CommRing T]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module T N] [Module R P] [Module T Q]
    (g : R ≃+* T)
    (a : LinearEquiv g.toRingHom (σ' := g.symm.toRingHom) M N)
    (e : M ≃ₗ[R] P)
    (b : LinearEquiv g.toRingHom (σ' := g.symm.toRingHom) P Q) (x : N) :
    transportLinearEquiv g a e b x = b (e (a.symm x)) := rfl

private theorem transportLinearEquiv_apply_map
    {R T M N P Q : Type*} [CommRing R] [CommRing T]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module T N] [Module R P] [Module T Q]
    (g : R ≃+* T)
    (a : LinearEquiv g.toRingHom (σ' := g.symm.toRingHom) M N)
    (e : M ≃ₗ[R] P)
    (b : LinearEquiv g.toRingHom (σ' := g.symm.toRingHom) P Q) (x : M) :
    transportLinearEquiv g a e b (a x) = b (e x) := by
  rw [transportLinearEquiv_apply, a.symm_apply_apply]

attribute [irreducible] transportLinearEquiv

private theorem continuousD_val
    (F A : Type*) [CommRing F] [CommRing A] [Algebra F A] (I : Ideal A)
    (x : A) (r : ℕ) :
    (KaehlerDifferential.continuousD F A I x).val r =
      KaehlerDifferential.D F _ (Ideal.Quotient.mk (I ^ (r + 1)) x) := rfl

attribute [local irreducible] KaehlerDifferential.continuousD
attribute [local irreducible] completedDifferentialTargetModule

private noncomputable def presentationEquiv
    {F D B : Type*} [CommRing F] [CommRing D] [CommRing B]
    [Algebra F D] [Algebra F B] (π : D →ₐ[F] B) (hπ : Function.Surjective π)
    (I : Ideal D) (hI : RingHom.ker π.toRingHom = I) : (D ⧸ I) ≃ₐ[F] B :=
  (Ideal.quotientEquivAlgOfEq F hI.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ)

private theorem presentationEquiv_mk
    {F D B : Type*} [CommRing F] [CommRing D] [CommRing B]
    [Algebra F D] [Algebra F B] (π : D →ₐ[F] B) (hπ : Function.Surjective π)
    (I : Ideal D) (hI : RingHom.ker π.toRingHom = I) (x : D) :
    presentationEquiv π hπ I hI (Ideal.Quotient.mk I x) = π x := rfl

attribute [irreducible] presentationEquiv

private noncomputable def quotientTransport
    {R T M N : Type*} [CommRing R] [CommRing T]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module T N]
    (g : R ≃+* T) (P : Submodule R M) (Q : Submodule T N)
    (a : LinearEquiv g.toRingHom (σ' := g.symm.toRingHom) M N)
    (h : P.map a.toLinearMap = Q) :
    LinearEquiv g.toRingHom (σ' := g.symm.toRingHom) (M ⧸ P) (N ⧸ Q) :=
  Submodule.Quotient.equiv P Q a h

private theorem quotientTransport_mk
    {R T M N : Type*} [CommRing R] [CommRing T]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module T N]
    (g : R ≃+* T) (P : Submodule R M) (Q : Submodule T N)
    (a : LinearEquiv g.toRingHom (σ' := g.symm.toRingHom) M N)
    (h : P.map a.toLinearMap = Q) (x : M) :
    quotientTransport g P Q a h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (a x) := rfl

attribute [irreducible] quotientTransport

private theorem coordinateCombination
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (f : (Fin n → R) →ₗ[R] M) (w : Fin n → M)
    (h : ∀ i, f (Pi.single i 1) = w i) (v : Fin n → R) :
    f v = Fintype.linearCombination R w v := by
  classical
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : R) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Fintype.linearCombination_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [f.map_smul, h]

set_option maxHeartbeats 350000 in
-- The residue-field, inverse-limit and semilinear quotient transports compare module instances.
/-- **Jacobian presentation of completed Kähler differentials.**

Let `k` be a field, `S` a finitely generated `k`-algebra, and `p` a maximal ideal.
Put `A = Sₚ`, `F = S ⧸ p`, and complete `A` at its maximal ideal. Assume `F/k`
is finite separable and choose a coefficient-field section of the residue map. For a
continuous surjection from `F[[t₁,…,tₙ]]` with kernel generated by
`f₁,…,fₛ` in the variable ideal, the
completed Jacobian cokernel is identified with `Ω[A⁄k] ⊗[A] Â`; the class of `eᵢ`
maps to the continuous differential of `tᵢ`.

Source: Stacks Project, Curves, Tag 0C4D (blueprint: lem-trf-completed-jacobian-differentials).
Proof:
1. Transport the coefficient section from `S/p` to the canonical residue field of `A`.
The completion/Kähler comparison gives the unique continuous extension and identifies
its values with continuous relative differentials. Tensor symmetry gives the written
order of factors. Transport back to `S/p`; the relative derivation kills coefficients.
2. The surjection identifies the formal-power-series quotient with the completion.
The variable ideal is the maximal ideal, by the coefficient criterion at exponent one
and the power-series unit criterion. Surjectivity maps this maximal ideal onto that
of the completion, which is the extension of the maximal ideal of `A`.
3. Apply the formal-power-series continuous-differential Jacobian presentation. Shift
its inverse system from all powers to positive powers (the omitted zeroth module is
zero), and transport along the quotient algebra equivalence. The coefficientwise
semilinear map takes the relation columns to the displayed Jacobian columns, hence
induces an equivalence of cokernels.
4. Compose with the inverse completion comparison and tensor symmetry. Its value on
each standard basis vector is the extended differential of the variable image.
Expand every coordinate vector in the standard basis to obtain the stated map equality. -/
theorem completedJacobianDifferentials
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    (hfinite : RingHom.FiniteType (algebraMap k S))
    (p : Ideal S) [p.IsMaximal]
    [FiniteDimensional k (S ⧸ p)] [Algebra.IsSeparable k (S ⧸ p)]
    (n s : ℕ)
    (σ : (S ⧸ p) →ₐ[k] completedRing S p)
    (hsection : (completedResidueMap p).comp σ.toRingHom = RingHom.id (S ⧸ p))
    (f : Fin s → MvPowerSeries (Fin n) (S ⧸ p))
    (hf : ∀ j : Fin s, f j ∈ Ideal.span (Set.range (fun i : Fin n ↦
      (MvPowerSeries.X i : MvPowerSeries (Fin n) (S ⧸ p)))))
    (π : MvPowerSeries (Fin n) (S ⧸ p) →+* completedRing S p)
    (hπsurj : Function.Surjective π)
    (hπcontinuous : @Continuous (MvPowerSeries (Fin n) (S ⧸ p)) (completedRing S p)
      (@MvPowerSeries.WithPiTopology.instTopologicalSpace (Fin n) (S ⧸ p) ⊤)
      ((Ideal.map (algebraMap (completedLocalRing S p) (completedRing S p))
        (completedIdeal S p)).adicTopology) π)
    (hπcoeff : ∀ c : S ⧸ p, π (MvPowerSeries.C c) = σ c)
    (hkernel : RingHom.ker π = Ideal.span (Set.range f)) :
    ∃ dhat : Derivation k (completedRing S p) (completedDifferentialTarget k S p),
      IsCompletedDifferentialExtension p σ dhat ∧
      (∀ dhat' : Derivation k (completedRing S p) (completedDifferentialTarget k S p),
        IsCompletedDifferentialExtension p σ dhat' → dhat' = dhat) ∧
      ∃ e : ((Fin n → completedRing S p) ⧸
        LinearMap.range
          ((Matrix.toLin' (completedJacobianMatrix (S := S) p n s f π)) :
            (Fin s → completedRing S p) →ₗ[completedRing S p]
              (Fin n → completedRing S p))) ≃ₗ[completedRing S p]
          completedDifferentialTarget k S p,
        ∀ v : Fin n → completedRing S p,
          e ((LinearMap.range
            ((Matrix.toLin' (completedJacobianMatrix (S := S) p n s f π)) :
              (Fin s → completedRing S p) →ₗ[completedRing S p]
                (Fin n → completedRing S p))).mkQ v) =
            completedDifferentialCoordinateMap p n π dhat v := by
  classical
  have _hcontinuity := hπcontinuous
  let A := completedLocalRing S p
  let B := completedRing S p
  let F := S ⧸ p
  let : Field F := Ideal.Quotient.field p
  let K := p.ResidueField
  let +nondep (eq := heFdef) eF : F ≃ₐ[k] K :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k F K)
      (Ideal.bijective_algebraMap_quotient_residueField p)
  have heF : eF.toRingEquiv =
      IsLocalization.AtPrime.equivQuotMaximalIdeal p A := by
    rw [heFdef]
    apply RingEquiv.toRingHom_injective
    apply Ideal.Quotient.ringHom_ext
    ext a
    exact (IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk p A a).symm
  let : Algebra F B := σ.toAlgebra
  have : IsScalarTower k F B := IsScalarTower.of_algebraMap_eq' σ.comp_algebraMap.symm
  let σK : K →ₐ[k] B := σ.comp eF.symm.toAlgHom
  let : Algebra K B := σK.toAlgebra
  have : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' σK.comp_algebraMap.symm
  have : FiniteDimensional k K := FiniteDimensional.of_injective eF.symm.toLinearMap
    eF.symm.injective
  have : Algebra.IsSeparable k K := AlgEquiv.Algebra.isSeparable eF
  have hσ : ∀ c : K, AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)
      (algebraMap K B c) = c := by
    intro c
    apply eF.symm.injective
    have hc := RingHom.congr_fun hsection (eF.symm c)
    change (IsLocalization.AtPrime.equivQuotMaximalIdeal p A).symm
      (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A) (σ (eF.symm c))) =
      eF.symm c at hc
    change eF.toRingEquiv.symm
      (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A) (σ (eF.symm c))) = _
    rw [heF]
    exact hc
  obtain ⟨D, hD, hunique, Φ, hΦA, hΦunique, hΦ⟩ :=
    Algebra.completion_kahler_differential_comparison hfinite p hσ
  clear hΦA hΦunique _hcontinuity hπcontinuous hsection
  let J : Ideal B := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  let κ : KaehlerDifferential.Continuous K B J ≃ₗ[B]
      KaehlerDifferential.Continuous F B J :=
    continuousDifferentialEquiv eF.symm.toRingEquiv (RingEquiv.refl B) (by
      ext c
      rfl) J J (by simp)
  let +nondep (eq := hΦFdef) ΦF := Φ.trans κ
  have hΦF (x : B) : ΦF (D x) = KaehlerDifferential.continuousD F B J x := by
    rw [hΦFdef]
    exact (congrArg κ (hΦ x)).trans
      (continuousDifferentialEquiv_D eF.symm.toRingEquiv (RingEquiv.refl B) _ J J _ x)
  let +nondep (eq := hCdef) C := completedTensorComm k S p
  let T := tensorDerivationEquiv k S p
  let dhat := T.symm D
  have hcomm (x : B) : C (dhat x) = D x := by
    rw [hCdef]
    exact tensorDerivationEquiv_symm_apply k S p D x
  have hvanish (c : F) : dhat (σ c) = 0 := by
    apply C.injective
    rw [map_zero, hcomm]
    apply ΦF.injective
    rw [map_zero, hΦF]
    exact (KaehlerDifferential.continuousD F B J).map_algebraMap c
  have hhat : IsCompletedDifferentialExtension p σ dhat := by
    refine ⟨?_, ?_, hvanish⟩
    · intro r
      obtain ⟨N, hN⟩ := hD.2 r
      refine ⟨N, fun z hz ↦ ?_⟩
      apply (linearEquiv_mem_ideal_smul C (J ^ r) (dhat z)).mp
      rw [hcomm]
      exact hN z hz
    · intro a
      apply C.injective
      rw [hcomm]
      change D (algebraMap A B a) = _
      rw [hD.1]
      rw [hCdef]
      exact (completedTensorComm_tmul k S p _ _).symm
  refine ⟨dhat, hhat, ?_, ?_⟩
  · intro dhat' h'
    change (∀ r : ℕ, ∃ N : ℕ, ∀ z : B, z ∈ J ^ N →
      dhat' z ∈ J ^ r • (⊤ : Submodule B (completedDifferentialTarget k S p))) ∧
      (∀ a : A, dhat' (algebraMap A B a) =
        TensorProduct.tmul A (KaehlerDifferential.D k A a) (1 : B)) ∧
      (∀ c : F, dhat' (σ c) = 0) at h'
    apply T.injective
    have hCD : T dhat = D := T.apply_symm_apply D
    rw [hCD]
    apply hunique
    refine ⟨?_, ?_⟩
    · intro a
      rw [tensorDerivationEquiv_apply]
      rw [h'.2.1]
      exact completedTensorComm_tmul k S p _ _
    · intro r
      obtain ⟨N, hN⟩ := h'.1 r
      refine ⟨N, fun z hz ↦ ?_⟩
      rw [tensorDerivationEquiv_apply]
      rw [← hCdef]
      apply (linearEquiv_mem_ideal_smul C (J ^ r) (dhat' z)).mpr
      exact hN z hz
  · clear hD hunique hhat hvanish
    have : Algebra.FiniteType k S := RingHom.finiteType_algebraMap.mp hfinite
    have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
    have : IsNoetherianRing A := inferInstance
    let V := MvPowerSeries.coordinateIdeal F n
    let I := MvPowerSeries.relationIdeal F f
    let R := MvPowerSeries (Fin n) F ⧸ MvPowerSeries.relationIdeal F f
    let πF : MvPowerSeries (Fin n) F →ₐ[F] B :=
      { π with commutes' := hπcoeff }
    let +nondep (eq := hEdef) E : R ≃ₐ[F] B :=
      presentationEquiv πF hπsurj I hkernel
    have hE (x : MvPowerSeries (Fin n) F) : E (Ideal.Quotient.mk I x) = π x :=
      by
        rw [hEdef]
        exact presentationEquiv_mk πF hπsurj I hkernel x
    have hV : V.map π = J := by
      rw [show V = IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) F) from
        variables_eq_maximalIdeal F n, IsLocalRing.map_maximalIdeal_of_surjective π hπsurj]
      exact AdicCompletion.maximalIdeal_eq_map
    let W : Ideal R := V.map (Ideal.Quotient.mk I)
    have hW : W.map E.toRingHom = J := by
      change (V.map (Ideal.Quotient.mk I)).map E.toRingHom = J
      have hcomp : E.toRingHom.comp (Ideal.Quotient.mk I) = π := RingHom.ext hE
      rw [Ideal.map_map, hcomp]
      exact hV
    let +nondep (eq := hHdef) H := continuousDifferentialEquiv (RingEquiv.refl F) E.toRingEquiv
      (RingHom.ext (fun c ↦ E.commutes c)) W J hW
    obtain ⟨d, hd, e, he⟩ :=
      MvPowerSeries.exists_quotientJacobian_equiv_adicContinuousDifferentials F n s f hf
    let +nondep (eq := hLdef) L := finsuppTransport E.toRingEquiv n
    have hL : (LinearMap.range (MvPowerSeries.quotientJacobian F f)).map L.toLinearMap =
        LinearMap.range (Matrix.toLin' (completedJacobianMatrix p n s f π)) := by
      rw [MvPowerSeries.quotientJacobian, Finsupp.range_linearCombination, Submodule.map_span,
        Matrix.range_toLin', ← Set.range_comp]
      apply congrArg (Submodule.span B)
      apply congrArg Set.range
      funext j
      apply funext
      intro i
      change L (∑ k : Fin n, Finsupp.single k
        (Ideal.Quotient.mk I (MvPowerSeries.pderiv F k (f j)))) i = _
      rw [hLdef, finsuppTransport_apply]
      change E ((∑ k : Fin n, Finsupp.single k
        (Ideal.Quotient.mk I (MvPowerSeries.pderiv F k (f j)))) i) =
          π (MvPowerSeries.pderiv F i (f j))
      simp only [Finsupp.finsetSum_apply, Finsupp.single_apply,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hE _
    let +nondep (eq := hQdef) Q := quotientTransport E.toRingEquiv _ _ L hL
    let epos := e.trans (positiveDifferentialEquiv F R W)
    let Ψ := transportLinearEquiv E.toRingEquiv Q epos H
    let result := Ψ.trans (ΦF.symm.trans C.symm)
    refine ⟨result, ?_⟩
    intro v
    have hsingle (i : Fin n) :
        result ((Matrix.toLin' (completedJacobianMatrix p n s f π)).range.mkQ
          (Pi.single i 1)) = dhat (π (MvPowerSeries.X i)) := by
      change C.symm (ΦF.symm (Ψ _)) = _
      apply C.symm_apply_eq.mpr
      apply ΦF.symm_apply_eq.mpr
      rw [hcomm, hΦF]
      have hQ := quotientTransport_mk E.toRingEquiv _ _ L hL
        (Finsupp.single i (1 : R))
      rw [← hQdef] at hQ
      conv_rhs at hQ => rw [hLdef, finsuppTransport_single]
      change Ψ (Submodule.Quotient.mk (Pi.single i (1 : B))) = _
      refine (congrArg Ψ hQ.symm).trans ?_
      refine (transportLinearEquiv_apply_map E.toRingEquiv Q epos H _).trans ?_
      change H (positiveDifferentialEquiv F R W (e _)) = _
      rw [he]
      have hdp : positiveDifferentialEquiv F R W
          (d (Ideal.Quotient.mk I (MvPowerSeries.X i))) =
            KaehlerDifferential.continuousD F R W
              (Ideal.Quotient.mk I (MvPowerSeries.X i)) := by
        apply Subtype.ext
        funext r
        rw [positiveDifferentialEquiv_val, continuousD_val]
        exact hd _ (r + 1)
      rw [hdp, hHdef, continuousDifferentialEquiv_D]
      exact congrArg (KaehlerDifferential.continuousD F B J) (hE (MvPowerSeries.X i))
    set_option backward.isDefEq.respectTransparency false in
    exact coordinateCombination n
      (result.toLinearMap.comp (Matrix.toLin' (completedJacobianMatrix p n s f π)).range.mkQ)
      (fun i ↦ dhat (π (MvPowerSeries.X i))) hsingle v

end AlgebraicGeometry
