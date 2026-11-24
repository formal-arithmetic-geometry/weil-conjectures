/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

import WeilConjectures.Algebra.Homology.ResidueConnectiveProjectiveOpcycles
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Cancelling the negative tail of a residue-connective projective complex

## References

* Stacks Project, Tag 00O0, finite-projective cancellation argument.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Universal vanishing in negative degrees gives a connective bounded projective model,
without any condition on degree-zero homology. -/
theorem universalConnective_projective_model
    (R : Type v) [CommRing R]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite R (P.X n))
    (hp : ∀ n : ℤ, Module.Projective R (P.X n))
    (hnegative : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      ∀ i : ℤ, i < 0 → IsZero (PB.homology i)) :
    ∃ Q : CochainComplex (ModuleCat.{v} R) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Q.X n)) ∧
      (∀ n : ℤ, Module.Finite R (Q.X n)) ∧
      (∀ n : ℤ, Module.Projective R (Q.X n)) ∧
      (∀ n : ℤ, n < 0 → IsZero (Q.X n)) ∧
      Nonempty (HomotopyEquiv P Q) := by
  classical
  let Q := P.truncGE 0
  have hneg (n : ℤ) (hn : n < 0) : IsZero (Q.X n) :=
    Q.isZero_of_isStrictlyGE 0 n hn
  obtain ⟨hfinite, hprojective⟩ := residueConnective_projective_opcycles R P hb hf hp
    (fun p _ ↦ hnegative p.ResidueField (algebraMap R p.ResidueField))
  have hterms (n : ℤ) : Module.Finite R (Q.X n) ∧ Module.Projective R (Q.X n) := by
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · have := ModuleCat.subsingleton_of_isZero (hneg n hn)
      exact ⟨inferInstance, inferInstance⟩
    · let e := (P.truncGEXIsoOpcycles 0).toLinearEquiv
      have := hfinite
      have := hprojective
      exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
    · let e := (P.truncGEXIso 0 n hn).toLinearEquiv
      have := hf n
      have := hp n
      exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
  obtain ⟨a, b, hbound⟩ := hb
  have hupper (n : ℤ) (hn : max b 0 < n) : IsZero (Q.X n) :=
    (hbound n (Or.inr (by omega))).of_iso (P.truncGEXIso 0 n (by omega))
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).mpr
    (fun n hn ↦ hbound n (Or.inr hn))
  have : Q.IsStrictlyLE (max b 0) := (Q.isStrictlyLE_iff _).mpr hupper
  have (n : ℤ) : CategoryTheory.Projective (P.X n) := by
    have := hp n
    infer_instance
  have (n : ℤ) : CategoryTheory.Projective (Q.X n) := by
    have := (hterms n).2
    infer_instance
  have : P.IsKProjective := isKProjective_of_projective P b
  have : Q.IsKProjective := isKProjective_of_projective Q (max b 0)
  let eId := (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{v} R) (.up ℤ)).app P
  have : P.IsGE 0 := (P.isGE_iff 0).mpr (fun n hn ↦ by
    rw [P.exactAt_iff_isZero_homology]
    exact (hnegative R (RingHom.id R) n hn).of_iso
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso eId).symm)
  obtain ⟨e, _⟩ := (IsKProjective.quasiIso_iff (P.πTruncGE 0)).mp inferInstance
  exact ⟨Q, ⟨0, max b 0, fun n hn ↦ hn.elim (hneg n) (hupper n)⟩,
    fun n ↦ (hterms n).1, fun n ↦ (hterms n).2, hneg, ⟨e⟩⟩

end CochainComplex
