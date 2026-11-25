/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import WeilConjectures.RingTheory.LimitModuleFinitePresentation
import WeilConjectures.RingTheory.IntegerApproximationFlatPointStage

/-!
# Noetherian approximation at a flat point

If a finitely presented module `M` over a finitely presented `R`-algebra `S` is flat over `R`
at a prime `q` of `S`, then the data has a Noetherian model (finite type over `ℤ`) that is flat
at the contraction of `q`.

## Implementation details

The data is written as a limit of finite type integer models. After localizing the systems at
the contracted primes, the localized module colimit is `M_q`; the local criterion along a
filtered system then gives a stage flat at the contracted prime. If the input universes
differ, everything is lifted to a common universe and the conclusion transported back.

## References

* [Stacks, Tag 00RC], reduction to finite-type integer models
* [Stacks, Tag 00R1]
* [Stacks, Tag 00R6]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module

/-- A flat point of a finitely presented module descends to a Noetherian model: if `M_q` is
flat over `R`, then `R → S` and `M` are base changes of a finitely presented model `A → B`, `N`
over a finite type `ℤ`-algebra `A` with `N` flat at the contraction of `q`.

This gives flatness at one contracted point only, not a flat neighbourhood. -/
theorem exists_noetherian_model_flat_at_prime
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S M]
    (q : PrimeSpectrum S)
    (hq : Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)) :
    ∃ (A B N : Type (max u v w)) (_ : CommRing A) (_ : CommRing B)
      (_ : Algebra A B) (_ : Algebra A R) (_ : Algebra B S) (_ : Algebra A S)
      (_ : IsScalarTower A B S) (_ : IsScalarTower A R S)
      (_ : AddCommGroup N) (_ : Module A N) (_ : Module B N)
      (_ : IsScalarTower A B N),
      IsNoetherianRing A ∧ Algebra.FiniteType A B ∧ Module.Finite B N ∧
      Algebra.IsPushout A R B S ∧ Nonempty (S ⊗[B] N ≃ₗ[S] M) ∧
      Module.Flat A
        (LocalizedModule (q.asIdeal.comap (algebraMap B S)).primeCompl N) := by
  classical
  let R' := ULift.{max u v w} R
  let S' := ULift.{max u v w} S
  let M' := ULift.{max u v w} M
  let : Algebra R' S' := ULift.algebra' R S'
  have : Algebra.FinitePresentation R' S' := by
    apply RingHom.finitePresentation_algebraMap.mp
    exact (RingHom.FinitePresentation.of_bijective
      (f := (ULift.ringEquiv : S' ≃+* S).symm.toRingHom)
      (ULift.ringEquiv.symm.bijective)).comp
      ((RingHom.finitePresentation_algebraMap.mpr
        (inferInstance : Algebra.FinitePresentation R S)).comp
        (RingHom.FinitePresentation.of_bijective
          (f := (ULift.ringEquiv : R' ≃+* R).toRingHom) ULift.ringEquiv.bijective))
  let : Algebra S' S := ULift.algebra' S S
  have : Module.FinitePresentation S' S := by
    let e : S' ≃ₗ[S'] S :=
      { ULift.ringEquiv.toAddEquiv with
        map_smul' := fun _ _ ↦ rfl }
    exact Module.FinitePresentation.of_equiv e
  have : Module.FinitePresentation S' M := Module.FinitePresentation.trans S' M S
  have : Module.FinitePresentation S' M' :=
    Module.FinitePresentation.of_equiv (ULift.moduleEquiv.symm)
  obtain ⟨Λ, hpo, hne, hdir, A, B, η, π, κ, D, ν, hmod, hmodel⟩ :=
    Algebra.limitModuleFinitePresentation R' S' M'
  let := hpo
  let := hne
  let := hdir
  let := hmod
  rcases hmodel with ⟨hAcol, hBcol, hDcol, hcomm, hscalar, hν, hAft, hBft,
    hDfin, htransB, htransD, hfinalB, hfinalD, _⟩
  obtain ⟨i, hflat⟩ := Algebra.exists_flat_integer_approximation_stage_at_prime R S M
    A B η π κ D ν
    ⟨hAcol, hBcol, hDcol, hcomm, hscalar, hν, hAft, hBft,
      hDfin, htransB, htransD⟩ q hq
  let : Algebra (A.obj i) (B.obj i) := (η.app i).hom.toAlgebra
  let : Algebra (A.obj i) R :=
    (ULift.ringEquiv.toRingHom.comp (π.app i).hom).toAlgebra
  let : Algebra (B.obj i) S :=
    (ULift.ringEquiv.toRingHom.comp (κ.app i).hom).toAlgebra
  let : Algebra (A.obj i) S := ((algebraMap R S).comp (algebraMap (A.obj i) R)).toAlgebra
  have : IsScalarTower (A.obj i) R S := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (A.obj i) (B.obj i) S := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    exact congrArg ULift.down (CategoryTheory.ConcreteCategory.congr_hom (hcomm i).symm a)
  let : Module (A.obj i) (D.obj i) := Module.compHom (D.obj i) (η.app i).hom
  have : IsScalarTower (A.obj i) (B.obj i) (D.obj i) :=
    IsScalarTower.of_compHom _ _ _
  have : Algebra.FiniteType ℤ (A.obj i) := hAft i
  have hnoeth : IsNoetherianRing (A.obj i) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hft : Algebra.FiniteType (A.obj i) (B.obj i) := hBft i
  have hfin : Module.Finite (B.obj i) (D.obj i) := hDfin i
  refine ⟨A.obj i, B.obj i, D.obj i, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hnoeth, hft, hfin, ?_, ?_,
    hflat⟩
  · let : Algebra (A.obj i) R' := (π.app i).hom.toAlgebra
    obtain ⟨er, her⟩ := hfinalB i
    let eLift := Algebra.TensorProduct.congr (AlgEquiv.refl (R := A.obj i) (A₁ := B.obj i))
      (ULift.algEquiv (R := A.obj i) (A := R))
    let er' := eLift.symm.toRingEquiv.trans (er.trans ULift.ringEquiv)
    let ec := (Algebra.TensorProduct.comm (A.obj i) R (B.obj i)).toRingEquiv.trans er'
    have hec (r : R) (b : B.obj i) :
        ec (r ⊗ₜ[A.obj i] b) = algebraMap R S r * algebraMap (B.obj i) S b := by
      change (er (b ⊗ₜ[A.obj i] (ULift.up r))).down = _
      rw [her]
      change _ * algebraMap R S r = algebraMap R S r * _
      exact mul_comm _ _
    let e : R ⊗[A.obj i] B.obj i ≃ₐ[R] S :=
      { ec with commutes' := fun r ↦ by simpa using hec r 1 }
    constructor
    apply IsBaseChange.of_equiv e.toLinearEquiv
    intro b
    change ec ((1 : R) ⊗ₜ[A.obj i] b) = algebraMap (B.obj i) S b
    simpa using hec 1 b
  · let : Algebra (B.obj i) S' := (κ.app i).hom.toAlgebra
    have : IsScalarTower (B.obj i) S S' := IsScalarTower.of_algebraMap_eq' (by
      ext b
      rfl)
    obtain ⟨em, _⟩ := hfinalD i
    let eLift := TensorProduct.congr (ULift.moduleEquiv (R := B.obj i) (M := S))
      (LinearEquiv.refl (B.obj i) (D.obj i))
    let eLiftS : S' ⊗[B.obj i] D.obj i ≃ₗ[S] S ⊗[B.obj i] D.obj i :=
      { eLift.toAddEquiv with
        map_smul' := fun s x ↦ by
          induction x using TensorProduct.inductionOn with
          | add x y hx hy =>
              change eLift (s • (x + y)) = s • eLift (x + y)
              change eLift (s • x) = s • eLift x at hx
              change eLift (s • y) = s • eLift y at hy
              rw [smul_add, map_add, map_add, smul_add, hx, hy]
          | tmul t n => rfl }
    exact ⟨eLiftS.symm.trans ((em.restrictScalars S).trans (ULift.moduleEquiv (R := S)))⟩

end Module
