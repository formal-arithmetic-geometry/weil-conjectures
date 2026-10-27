/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.ParameterRootAlgebra
public import Sheaf.RingTheory.LocalizationColimit
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.Etale
import Sheaf.AlgebraicGeometry.UnitBinomialFiniteEtale
import Mathlib.RingTheory.Localization.Module
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Localizing simultaneous root algebras

Source: Stacks 00G3, 00UB, 00UC, 03PL and the localization universal property.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace Algebra.ParameterRoot

variable {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (n : ℕ)

/-- An arbitrary root quotient of units is etale when the degree is a unit. -/
theorem etale_of_units (hn : 0 < n) (hnR : IsUnit (n : R)) (ht : ∀ i, IsUnit (t i)) :
    Algebra.Etale R (Ring t n) := by
  induction r with
  | zero => exact Algebra.Etale.of_equiv (emptyEquiv n t).symm
  | succ r ih =>
    let t' : Fin r → R := fun i ↦ t i.succ
    let A := Ring t' n
    let P : Polynomial A := Polynomial.X ^ n - Polynomial.C (algebraMap R A (t 0))
    have : Algebra.Etale R A := ih t' (fun i ↦ ht i.succ)
    obtain ⟨v, hv⟩ := (ht 0).map (algebraMap R A)
    have hnA : IsUnit (n : A) := by simpa using hnR.map (algebraMap R A)
    have he := (AlgebraicGeometry.unitBinomial_finite_surjective_etale A n hn hnA v).2.2.2
    rw [hv] at he
    have : Algebra.Etale A (AdjoinRoot P) := by
      exact RingHom.etale_algebraMap.mp
        ((AlgebraicGeometry.HasRingHomProperty.Spec_iff
          (P := @AlgebraicGeometry.Etale)).mp he)
    have : Algebra.Etale R (AdjoinRoot P) := Algebra.Etale.comp R A _
    exact Algebra.Etale.of_equiv (succEquiv n t).symm

/-- The polynomial root quotient over the localized coefficient ring. -/
abbrev localizedRoots (s : R) :=
  Ring (fun i ↦ algebraMap R (Localization.Away s) (t i)) n

/-- The root quotient over localized coefficients is the localization of the root quotient. -/
def localizationEquiv (s : R) :
    Localization.Away (algebraMap R (Ring t n) s) ≃+* localizedRoots t n s := by
  let A := Ring t n
  let L := Localization.Away s
  let B := localizedRoots t n s
  let C := Localization.Away (algebraMap R A s)
  let f : A →+* B := ringLift t n (algebraMap R B) (root _ n) (by
    intro i
    rw [root_pow, ← IsScalarTower.algebraMap_apply])
  have hf (a : R) : f (algebraMap R A a) = algebraMap R B a := ringLift_algebraMap ..
  let f' : C →+* B := IsLocalization.Away.lift (g := f) (algebraMap R A s)
    (by
      rw [hf, IsScalarTower.algebraMap_apply R L B]
      exact (IsLocalization.Away.algebraMap_isUnit (S := L) s).map (algebraMap L B))
  let g0 : L →+* C := IsLocalization.Away.map L C (algebraMap R A) s
  have hg0 (a : R) : g0 (algebraMap R L a) = algebraMap A C (algebraMap R A a) :=
    IsLocalization.map_eq _ _
  let g : B →+* C := ringLift (fun i ↦ algebraMap R L (t i)) n g0
    (fun i ↦ algebraMap A C (root t n i)) (by
      intro i
      rw [← map_pow, root_pow]
      exact (hg0 (t i)).symm)
  have hga (a : L) : g (algebraMap L B a) = g0 a := ringLift_algebraMap ..
  have hgr (i : Fin r) : g (root (fun i ↦ algebraMap R L (t i)) n i) =
      algebraMap A C (root t n i) := ringLift_root ..
  have hfa (a : A) : f' (algebraMap A C a) = f a := IsLocalization.Away.lift_eq _ _ a
  have hfr (i : Fin r) : f (root t n i) =
      root (fun i ↦ algebraMap R L (t i)) n i := ringLift_root ..
  refine RingEquiv.ofRingHom f' g ?_ ?_
  · apply ringHom_ext
    · apply IsLocalization.ringHom_ext (Submonoid.powers s)
      ext a
      change f' (g (algebraMap L B (algebraMap R L a))) = algebraMap R B a
      rw [hga, hg0, hfa, hf]
    · intro i
      change f' (g (root _ n i)) = root _ n i
      rw [hgr, hfa, hfr]
  · apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A s))
    apply ringHom_ext
    · ext a
      change g (f' (algebraMap A C (algebraMap R A a))) = algebraMap A C (algebraMap R A a)
      rw [hfa, hf]
      change g (algebraMap L B (algebraMap R L a)) = _
      rw [hga, hg0]
    · intro i
      change g (f' (algebraMap A C (root t n i))) = algebraMap A C (root t n i)
      rw [hfa, hfr, hgr]

@[simp] theorem localizationEquiv_coeff (s : R) (a : R) :
    localizationEquiv t n s
      (algebraMap (Ring t n) (Localization.Away (algebraMap R (Ring t n) s))
        (algebraMap R (Ring t n) a)) =
      algebraMap R (localizedRoots t n s) a := by
  simp only [localizationEquiv, RingEquiv.ofRingHom_apply, IsLocalization.Away.lift_eq,
    ringLift_algebraMap]

@[simp] theorem localizationEquiv_root (s : R) (i : Fin r) :
    localizationEquiv t n s (algebraMap _ _ (root t n i)) =
      root (fun i ↦ algebraMap R (Localization.Away s) (t i)) n i := by
  simp only [localizationEquiv, RingEquiv.ofRingHom_apply, IsLocalization.Away.lift_eq,
    ringLift_root]

/-- The localized structural map, specified by the localization universal property. -/
def localizedMap (s : R) :
    Localization.Away s →+* Localization.Away (algebraMap R (Ring t n) s) :=
  IsLocalization.Away.map (Localization.Away s)
    (Localization.Away (algebraMap R (Ring t n) s)) (algebraMap R (Ring t n)) s

theorem localizationEquiv_map (s : R) (a : Localization.Away s) :
    localizationEquiv t n s (localizedMap t n s a) =
      algebraMap (Localization.Away s) (localizedRoots t n s) a := by
  have h : (localizationEquiv t n s).toRingHom.comp (localizedMap t n s) =
      algebraMap (Localization.Away s) (localizedRoots t n s) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    change localizationEquiv t n s (localizedMap t n s (algebraMap R _ a)) = _
    rw [show localizedMap t n s (algebraMap R _ a) =
      algebraMap (Ring t n) _ (algebraMap R (Ring t n) a) from
        IsLocalization.map_eq (S := Localization.Away s)
          (Q := Localization.Away (algebraMap R (Ring t n) s))
          (Submonoid.le_comap_map _) a,
      localizationEquiv_coeff]
    rfl
  exact RingHom.congr_fun h a

/-- Localization preserves the finite faithfully flat root presentation. -/
theorem localized_finite_faithfullyFlat (s : R) (hn : 0 < n) :
    (localizedMap t n s).Finite ∧ (localizedMap t n s).FaithfullyFlat := by
  let C := Localization.Away (algebraMap R (Ring t n) s)
  let L := Localization.Away s
  let : Algebra L C := (localizedMap t n s).toAlgebra
  let e : C ≃ₐ[L] localizedRoots t n s :=
    { localizationEquiv t n s with commutes' := localizationEquiv_map t n s }
  obtain ⟨b, _⟩ := exists_basis (fun i ↦ algebraMap R L (t i)) n hn
  let b' := b.map e.symm.toLinearEquiv
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hfin : Module.Finite L C := Module.Finite.of_basis b'
  have hff : Module.FaithfullyFlat L C := Module.FaithfullyFlat.of_linearEquiv L _ b'.repr
  exact ⟨hfin, hff⟩

/-- Inverting the parameter product makes every parameter a unit. -/
theorem punctured_etale (hn : 0 < n) (hnR : IsUnit (n : R)) :
    (localizedMap t n (∏ i, t i)).Etale := by
  let s := ∏ i, t i
  let L := Localization.Away s
  let C := Localization.Away (algebraMap R (Ring t n) s)
  let : Algebra L C := (localizedMap t n s).toAlgebra
  let e : C ≃ₐ[L] localizedRoots t n s :=
    { localizationEquiv t n s with commutes' := localizationEquiv_map t n s }
  have hnL : IsUnit (n : L) := by simpa using hnR.map (algebraMap R L)
  have ht : ∀ i, IsUnit (algebraMap R L (t i)) := by
    intro i
    exact IsLocalization.Away.isUnit_of_dvd s (Finset.dvd_prod_of_mem t (Finset.mem_univ i))
  have : Algebra.Etale L (localizedRoots t n s) := etale_of_units _ n hn hnL ht
  have : Algebra.Etale L C := Algebra.Etale.of_equiv e.symm
  exact RingHom.etale_algebraMap.mpr this

/-- Localization preserves the finite nonempty basis of a refinement. -/
theorem localized_transition_finite_faithfullyFlat (s : R) (m : ℕ) (h : n ∣ m)
    (hq : 0 < m / n) :
    (Algebra.LocalizationColimit.map s (transition t n m h)).Finite ∧
      (Algebra.LocalizationColimit.map s (transition t n m h)).FaithfullyFlat := by
  let f := transition t n m h
  let A := Ring t n
  let B := Ring t m
  let L := Localization.Away (algebraMap R A s)
  let C := Localization.Away (algebraMap R B s)
  have : IsLocalization.Away (f (algebraMap R A s)) C := by
    rw [f.commutes]
    infer_instance
  obtain ⟨b, _⟩ := exists_transition_basis t n m h hq
  let : Algebra A B := f.toRingHom.toAlgebra
  have : Module.Finite A B := Module.Finite.of_basis b
  have : Nonempty (Fin (m / n)) := ⟨⟨0, hq⟩⟩
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_linearEquiv A _ b.repr
  have he : Algebra.LocalizationColimit.map s f =
      IsLocalization.Away.map L C f.toRingHom (algebraMap R A s) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A s))
    apply RingHom.ext
    intro a
    change Algebra.LocalizationColimit.map s f (algebraMap A _ a) =
      IsLocalization.Away.map L C f.toRingHom (algebraMap R A s) (algebraMap A _ a)
    rw [Algebra.LocalizationColimit.map_apply]
    exact (IsLocalization.map_eq (S := L) (Q := C)
      (Submonoid.le_comap_map _) a).symm
  rw [he]
  exact ⟨RingHom.finite_localizationPreserves.away _ _ _ _ ‹Module.Finite A B›,
    RingHom.FaithfullyFlat.isStableUnderBaseChange.localizationPreserves.away
      _ _ _ _ ‹Module.FaithfullyFlat A B›⟩

/-- Maps between the punctured étale levels are étale over the common base. -/
theorem punctured_transition_etale (m : ℕ) (h : n ∣ m)
    (hn : 0 < n) (hm : 0 < m) (hnR : IsUnit (n : R)) (hmR : IsUnit (m : R)) :
    (Algebra.LocalizationColimit.map (∏ i, t i) (transition t n m h)).Etale := by
  let s := ∏ i, t i
  let L := Localization.Away s
  let A := Localization.Away (algebraMap R (Ring t n) s)
  let B := Localization.Away (algebraMap R (Ring t m) s)
  let f := Algebra.LocalizationColimit.map s (transition t n m h)
  let : Algebra L A := (localizedMap t n s).toAlgebra
  let : Algebra L B := (localizedMap t m s).toAlgebra
  let : Algebra A B := f.toAlgebra
  have : IsScalarTower L A B := IsScalarTower.of_algebraMap_eq' (by
    exact (Algebra.LocalizationColimit.map_base s (transition t n m h)).symm)
  have : Algebra.Etale L A := RingHom.etale_algebraMap.mp (punctured_etale t n hn hnR)
  have : Algebra.Etale L B := RingHom.etale_algebraMap.mp (punctured_etale t m hm hmR)
  exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_restrictScalars L A B)

end Algebra.ParameterRoot
