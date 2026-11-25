/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Ring.Shrink
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Artinian.Module

/-!
# A small carrier for a local essentially smooth algebra

## Implementation details

The smooth model `P` is of finite type, hence small, so its localizations are small as well;
both the algebra and its smooth model are moved into `Type (max u w)` using `Shrink`.

## References

* Stacks Project, Algebra, Definition 00QM, and Lemma 07FJ, step 25
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- A local Artinian essentially smooth algebra has a representative in the base universe: it is
isomorphic over `R` to a local Artinian essentially smooth `R`-algebra in `Type (max u w)`. -/
theorem exists_essentiallySmooth_small_local_model
    {R : Type u} [CommRing R] (D : Type v) [CommRing D] [Algebra R D]
    [IsLocalRing D] [IsArtinianRing D] (hsmooth : EssentiallySmooth R D) :
    ∃ (D' : Type (max u w)) (_ : CommRing D') (_ : Algebra R D')
      (_ : IsLocalRing D') (_ : IsArtinianRing D'),
      EssentiallySmooth R D' ∧ Nonempty (D ≃ₐ[R] D') := by
  classical
  obtain ⟨P, hP, hRP, hPsmooth, S, ⟨eD⟩⟩ := hsmooth
  let : CommRing P := hP
  let : Algebra R P := hRP
  have : Smooth R P := hPsmooth
  have : Small.{max u w} R := inferInstance
  have : Small.{max u w} P := FiniteType.small (R := R)
  have : Small.{max u w} (Localization S) :=
    small_of_surjective (IsLocalization.mk'_surjective S)
  have : Small.{max u w} D := small_of_surjective eD.symm.surjective
  let D' := Shrink.{max u w} D
  let er : D ≃+* D' := (Shrink.ringEquiv D).symm
  let : Algebra R D' := (er.toRingHom.comp (algebraMap R D)).toAlgebra
  let e : D ≃ₐ[R] D' := AlgEquiv.ofRingEquiv (f := er) (fun _ ↦ rfl)
  have : IsLocalRing D' := er.isLocalRing
  have : IsArtinianRing D' := er.isArtinianRing
  refine ⟨D', inferInstance, inferInstance, inferInstance, inferInstance, ?_, ⟨e⟩⟩
  let Q := Shrink.{max u w} P
  let ePr : Q ≃+* P := Shrink.ringEquiv P
  let : Algebra R Q := (ePr.symm.toRingHom.comp (algebraMap R P)).toAlgebra
  let eP : Q ≃ₐ[R] P := AlgEquiv.ofRingEquiv (f := ePr) (fun r ↦ by
    change ePr (ePr.symm (algebraMap R P r)) = algebraMap R P r
    exact ePr.apply_symm_apply _)
  have hQ : Smooth R Q := Smooth.of_equiv eP.symm
  let U := S.comap eP.toRingEquiv.toMonoidHom
  have hU : U.map eP.toRingEquiv.toMonoidHom = S :=
    Submonoid.map_comap_eq_of_surjective eP.surjective S
  let eLr : Localization U ≃+* Localization S :=
    IsLocalization.ringEquivOfRingEquiv (Localization U) (Localization S)
      eP.toRingEquiv hU
  let eL : Localization U ≃ₐ[R] Localization S :=
    AlgEquiv.ofRingEquiv (f := eLr) (fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R Q (Localization U)]
      change IsLocalization.ringEquivOfRingEquiv (Localization U) (Localization S)
        eP.toRingEquiv hU (algebraMap Q (Localization U) (algebraMap R Q r)) = _
      rw [IsLocalization.ringEquivOfRingEquiv_eq]
      change algebraMap P (Localization S) (eP (algebraMap R Q r)) = _
      rw [eP.commutes, ← IsScalarTower.algebraMap_apply R P (Localization S)])
  exact ⟨Q, inferInstance, inferInstance, hQ, U,
    ⟨(e.symm.trans eD).trans eL.symm⟩⟩

end Algebra
