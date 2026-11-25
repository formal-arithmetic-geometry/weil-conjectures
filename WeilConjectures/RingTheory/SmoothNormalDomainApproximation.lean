/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.Algebra.Ring.ULift
import WeilConjectures.RingTheory.NormalFiniteTypeSubalgebraExtension
import WeilConjectures.RingTheory.DirectedSubalgebraTensorColimit

/-!
# Noetherian approximation of smooth algebras over normal domains

A smooth algebra over a normal domain is a filtered colimit of smooth algebras whose base
rings are Noetherian normal domains.

## References

* [Stacks, Tag 033C], proof, third paragraph
* [Stacks, Tag 00TP]
* [Stacks, Tag 0335]
* [Stacks, Tag 00DD]
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace RingHom.Smooth

/-- A smooth algebra over a normal domain is a filtered colimit of smooth algebras
whose base rings are Noetherian and normal. -/
theorem exists_noetherian_normal_model_colimit
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsIntegrallyClosed R] {f : R →+* S} (hf : f.Smooth) :
    ∃ (I : Type (max u v)) (_ : SmallCategory I) (_ : IsFiltered I)
      (F : I ⥤ CommRingCat.{max u v}) (_ : HasColimit F),
      Nonempty ((colimit F : CommRingCat.{max u v}) ≃+* S) ∧
      ∀ i : I, ∃ (A : Type (max u v)) (_ : CommRing A) (_ : IsNoetherianRing A)
        (g : A →+* F.obj i), g.Smooth ∧
        ∀ (p : Ideal A) [p.IsPrime],
          IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let R' := ULift.{v} R
  let eR : R' ≃+* R := ULift.ringEquiv
  have : IsDomain R' := eR.injective.isDomain eR
  have : IsIntegrallyClosed R' := IsIntegrallyClosed.of_equiv eR.symm
  let f' : R' →+* S := f.comp eR.toRingHom
  have hf' : f'.Smooth := (of_bijective eR.bijective).comp hf
  let : Algebra R' S := f'.toAlgebra
  have : Algebra.Smooth R' S := hf'
  obtain ⟨A0, B, cB, aB, hfg, hsm, ⟨e⟩⟩ :=
    Algebra.Smooth.exists_subalgebra_fg ℤ R' S
  let P : Set (Subalgebra ℤ R') :=
    {A | A0 ≤ A ∧ A.FG ∧ IsIntegrallyClosed A}
  have hne : P.Nonempty := by
    obtain ⟨A, hle, hA, hnA⟩ := A0.exists_fg_integrallyClosed_extension hfg
    exact ⟨A, hle, hA, hnA⟩
  have hdir : DirectedOn (· ≤ ·) P := by
    intro A hA C hC
    obtain ⟨D, hD, hfgD, hnD⟩ :=
      (A ⊔ C).exists_fg_integrallyClosed_extension (hA.2.1.sup hC.2.1)
    exact ⟨D, ⟨hA.1.trans (le_sup_left.trans hD), hfgD, hnD⟩,
      le_sup_left.trans hD, le_sup_right.trans hD⟩
  have hcover : ∀ x : R', ∃ A ∈ P, x ∈ A := by
    intro x
    have hxfg : (Algebra.adjoin ℤ ({x} : Set R')).FG :=
      Subalgebra.fg_def.mpr ⟨{x}, Set.finite_singleton x, rfl⟩
    obtain ⟨A, hA, hfgA, hnA⟩ :=
      (A0 ⊔ Algebra.adjoin ℤ {x}).exists_fg_integrallyClosed_extension (hfg.sup hxfg)
    exact ⟨A, ⟨le_sup_left.trans hA, hfgA, hnA⟩,
      (show Algebra.adjoin ℤ {x} ≤ A from le_sup_right.trans hA)
        (Algebra.subset_adjoin (Set.mem_singleton x))⟩
  obtain ⟨I, cI, hI, F, hF, ⟨eF⟩, hstages⟩ :=
    A0.exists_tensorProduct_colimit_of_directed_cover B P hne hdir hcover
      (fun _ hA ↦ hA.1)
  refine ⟨I, cI, hI, F, hF, ⟨eF.trans e.symm.toRingEquiv⟩, ?_⟩
  intro i
  obtain ⟨A, hA, aA, ⟨eA⟩⟩ := hstages i
  have : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).mp hA.2.1
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have : IsIntegrallyClosed A := hA.2.2
  have hg : (algebraMap A (TensorProduct A0 A B)).Smooth :=
    RingHom.smooth_algebraMap.mpr inferInstance
  refine ⟨A, inferInstance, inferInstance,
    eA.toRingHom.comp (algebraMap A (TensorProduct A0 A B)),
    hg.comp (of_bijective eA.bijective), ?_⟩
  intro p hp
  exact ⟨inferInstance, isIntegrallyClosed_of_isLocalization (Localization.AtPrime p)
    p.primeCompl p.primeCompl_le_nonZeroDivisors⟩

end RingHom.Smooth
