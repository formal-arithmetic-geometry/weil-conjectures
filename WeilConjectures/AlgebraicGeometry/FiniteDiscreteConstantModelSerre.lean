/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!
# Serre closure for finite discrete condensed scalar models

Source: the current blueprint, `det-brown-hypotheses-small`, proof, Thick paragraph,
finite discrete coefficient heart closure on a common refinement; Stacks Tags 093U(3)
and 03RZ(3) (blueprint: lem-weil-constructible-coefficient-serre).

The coefficient ring is the continuous-function condensed ring with the discrete topology.
Constructibility is the existing finite scalar-model predicate, including its affine-local
convention on schemes that are not qcqs.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem finiteModel_stratified_iff (A : Type u) [CommRing A]
    (T : Scheme.{u})
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    FiniteDiscreteOrdinary.ordinaryStratified A T M ↔
      IsConstructible (ULift.{u + 1} A) M := by
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩),
      fun i ↦ hC i.down⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦
      h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)⟩

private theorem finiteModel_ordinary_closure
    (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    (∀ (M N : Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) (f : M ⟶ N),
      FiniteDiscreteOrdinary.ordinaryConstructible A T M →
      FiniteDiscreteOrdinary.ordinaryConstructible A T N →
      FiniteDiscreteOrdinary.ordinaryConstructible A T (kernel f) ∧
      FiniteDiscreteOrdinary.ordinaryConstructible A T (cokernel f)) ∧
    (∀ S : ShortComplex (Sheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))),
      S.ShortExact → FiniteDiscreteOrdinary.ordinaryConstructible A T S.X₁ →
      FiniteDiscreteOrdinary.ordinaryConstructible A T S.X₃ →
      FiniteDiscreteOrdinary.ordinaryConstructible A T S.X₂) := by
  classical
  constructor
  · intro M N f hM hN
    unfold FiniteDiscreteOrdinary.ordinaryConstructible at hM hN ⊢
    split_ifs at hM hN ⊢ with hT
    · obtain ⟨hk, hc⟩ := Scheme.CoefficientSerre.fixed_kernel_cokernel
        T (ULift.{u + 1} A) M N f
        ((finiteModel_stratified_iff A T M).mp hM)
        ((finiteModel_stratified_iff A T N).mp hN)
      exact ⟨(finiteModel_stratified_iff A T _).mpr hk,
        (finiteModel_stratified_iff A T _).mpr hc⟩
    · constructor
      all_goals
        intro U hU
        let F := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U.ι
        obtain ⟨hk, hc⟩ := Scheme.CoefficientSerre.fixed_kernel_cokernel
          U.toScheme (ULift.{u + 1} A) (F.obj M) (F.obj N) (F.map f)
          ((finiteModel_stratified_iff A U.toScheme _).mp (hM U hU))
          ((finiteModel_stratified_iff A U.toScheme _).mp (hN U hU))
      · exact (finiteModel_stratified_iff A U.toScheme _).mpr
          (isConstructible_of_iso (PreservesKernel.iso F f).symm hk)
      · exact (finiteModel_stratified_iff A U.toScheme _).mpr
          (isConstructible_of_iso (PreservesCokernel.iso F f).symm hc)
  · intro S hS h₁ h₃
    unfold FiniteDiscreteOrdinary.ordinaryConstructible at h₁ h₃ ⊢
    split_ifs at h₁ h₃ ⊢ with hT
    · exact (finiteModel_stratified_iff A T _).mpr
        (Scheme.CoefficientSerre.fixed_extension T (ULift.{u + 1} A) S hS
          ((finiteModel_stratified_iff A T _).mp h₁)
          ((finiteModel_stratified_iff A T _).mp h₃))
    · intro U hU
      let F := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) U.ι
      exact (finiteModel_stratified_iff A U.toScheme _).mpr
        (Scheme.CoefficientSerre.fixed_extension U.toScheme (ULift.{u + 1} A)
          (S.map F) (hS.map_of_exact F)
          ((finiteModel_stratified_iff A U.toScheme _).mp (h₁ U hU))
          ((finiteModel_stratified_iff A U.toScheme _).mp (h₃ U hU)))

/-- Constructible internal modules over a finite discrete condensed ring are closed under
ambient kernels, cokernels and extensions, for every scheme.

Source: current blueprint `det-brown-hypotheses-small`, proof, Thick paragraph;
Stacks Tag 093U(3), `sites-modules.tex`, lemma-kernel-finite-locally-constant, and
Tag 03RZ(3), `etale-cohomology.tex`, lemma-constructible-abelian.
(blueprint: lem-weil-constructible-coefficient-serre).

Proof:
1. Choose the normalized additive coefficient encoding and use its constructibility
   comparison with ordinary module-valued sheaves. Equivalences preserve kernels,
   cokernels and short exact sequences.
2. Identify the ordinary finite-model stratified predicate with the established
   constructibility predicate. Lift covering index universes in one direction and
   shrink pro-etale covers in the other direction.
3. Reuse the proved ordinary-sheaf kernel, cokernel and extension closure lemmas.
   These follow from constructible etale origins and exact comparison with the
   etale constructible Serre subcategory.
4. On a scheme that is not qcqs apply this result on every affine open; inverse
   image is exact and preserves the relevant kernels and cokernels. Transport
   the result back through the encoding comparison. The argument allows empty
   schemes, empty covers and the zero coefficient ring.
-/
theorem finiteDiscreteConstantModel_exactClosure
    (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    (∀ (M N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj A) T)) (f : M ⟶ N),
      IsConstantModelConstructible (Profinite.continuousCoefficientRingObj A) T M →
      IsConstantModelConstructible (Profinite.continuousCoefficientRingObj A) T N →
      IsConstantModelConstructible (Profinite.continuousCoefficientRingObj A) T (kernel f) ∧
        IsConstantModelConstructible (Profinite.continuousCoefficientRingObj A) T (cokernel f)) ∧
    (∀ S : ShortComplex (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousCoefficientRingObj A) T)),
      S.ShortExact →
      IsConstantModelConstructible (Profinite.continuousCoefficientRingObj A) T S.X₁ →
      IsConstantModelConstructible (Profinite.continuousCoefficientRingObj A) T S.X₃ →
      IsConstantModelConstructible (Profinite.continuousCoefficientRingObj A) T S.X₂) := by
  classical
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := discreteTopology_bot A
  let e := (FiniteDiscreteOrdinary.encoding_exists A T).some
  let F := e.ordinary.functor ⋙ e.fixed.functor
  have cmp := FiniteDiscreteOrdinary.constructible_comparison A T e
  obtain ⟨hk, he⟩ := finiteModel_ordinary_closure A T
  constructor
  · intro M N f hM hN
    obtain ⟨hker, hcoker⟩ := hk (F.obj M) (F.obj N) (F.map f)
      ((cmp M).mp hM) ((cmp N).mp hN)
    exact ⟨(cmp _).mpr ((FiniteDiscreteOrdinary.constructible_iso A T
        (PreservesKernel.iso F f).symm).mp hker),
      (cmp _).mpr ((FiniteDiscreteOrdinary.constructible_iso A T
        (PreservesCokernel.iso F f).symm).mp hcoker)⟩
  · intro S hS h₁ h₃
    exact (cmp _).mpr (he (S.map F) (hS.map_of_exact F)
      ((cmp _).mp h₁) ((cmp _).mp h₃))

end AlgebraicGeometry.ProEtale
