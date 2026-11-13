/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceTensorAdd
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceTensorInverse
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Mathlib.Tactic.LinearCombination
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierScalars
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear
import WeilConjectures.Mathlib.CategoryTheory.Conj
import Mathlib.Algebra.GroupWithZero.Units.Basic
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierRootCharts
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedCharacterRootEvaluation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-! # Character decomposition with condensed Artin–Schreier coefficients

The coefficient ring is the recorded pulled-back condensed ring, not a discrete
constant ring. The projectors, pullbacks and degree-q sheaves are specializations
of the constructions in ArtinSchreierTraceComparison. The coproduct comparison is
specified by its actual image inclusions, which fixes the canonical decomposition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

/-- Regard a Qbar-valued character as a character into the global sections of the
condensed coefficient ring, using its canonical constant-section ring homomorphism. -/
abbrev qlbarCharacter (ℓ : ℕ) [Fact ℓ.Prime] {G : Type v} [AddMonoid G]
    (χ : AddChar G (PadicAlgCl ℓ)) :
    AddChar G (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) :=
  (Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar χ

/-- The degree-`q` Artin–Schreier sheaf `ProEtale.condensedArtinSchreierSheafOf`, with its
condensed `Q̄_ℓ` coefficients and the character `Ψ` composed with the field trace. -/
abbrev qlbarTraceSheafOf (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Ψ : AddChar (ZMod p) (PadicAlgCl ℓ))
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :=
  ProEtale.condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k X
    ((qlbarCharacter ℓ Ψ).compTrace k) f

/-- Tensor addition and the tensor inverse, with inverse-character identification,
for the trace character psi=Psi o Tr. Both tensor orders express the inverse object. -/
theorem qlbar_artinSchreier_trace_tensor_properties
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod p) k]
    (Ψ : AddChar (ZMod p) (PadicAlgCl ℓ)) (hΨ : Ψ ≠ 1)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f g : Γ(X, ⊤)) :
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ X f ⊗ qlbarTraceSheafOf p ℓ k Ψ X g ≅
      qlbarTraceSheafOf p ℓ k Ψ X (f + g)) ∧
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ X f ⊗ qlbarTraceSheafOf p ℓ k Ψ X (-f) ≅
      Mod.regular (ProEtale.padicAlgClRingObj X ℓ)) ∧
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ X (-f) ⊗ qlbarTraceSheafOf p ℓ k Ψ X f ≅
      Mod.regular (ProEtale.padicAlgClRingObj X ℓ)) ∧
    Nonempty (qlbarTraceSheafOf p ℓ k Ψ⁻¹ X f ≅ qlbarTraceSheafOf p ℓ k Ψ X (-f))   := by
  letI : CharP k p := (Algebra.charP_iff (ZMod p) k p).mp inferInstance
  have hq : IsUnit (Fintype.card k : MonObj.Γ (Profinite.padicAlgClRingObj ℓ)) := by
    have hk : IsUnit (Fintype.card k : PadicAlgCl ℓ) := by
      apply isUnit_iff_ne_zero.mpr
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card k ≠ 0)
    simpa only [map_natCast] using (Profinite.PadicAlgCl.constRingHom ℓ).isUnit_map hk
  letI : Nontrivial (MonObj.Γ (Profinite.padicAlgClRingObj ℓ)) :=
    ⟨⟨1, 0, fun h ↦ Profinite.PadicAlgCl.one_ne_zero_end_regular ℓ
      (by rw [← map_one Mod.regularEndRingHom, h, map_zero])⟩⟩
  have hχ : qlbarCharacter ℓ Ψ ≠ 1 := by
    intro h
    apply hΨ
    ext a
    apply (Profinite.PadicAlgCl.constRingHom ℓ).injective
    have ha := congrArg (fun c : AddChar (ZMod p)
        (MonObj.Γ (Profinite.padicAlgClRingObj ℓ)) ↦ c a) h
    simpa [qlbarCharacter] using ha
  have hΨ' : (qlbarCharacter ℓ Ψ).compTrace k ≠ 1 :=
    AddChar.compTrace_ne_one hχ
  have hadd := condensedArtinSchreier_tensor_add_generic
    (Profinite.padicAlgClRingObj ℓ) k ((qlbarCharacter ℓ Ψ).compTrace k) hΨ' hq
    X f g
  have hinv := condensedArtinSchreier_tensor_inverse_generic
    (Profinite.padicAlgClRingObj ℓ) k ((qlbarCharacter ℓ Ψ).compTrace k) hΨ' hq X f
  rcases hinv with ⟨hinv, hneg, hchar⟩
  have hinvchar : (qlbarCharacter ℓ Ψ⁻¹).compTrace k =
      ((qlbarCharacter ℓ Ψ).compTrace k)⁻¹ := by
    ext x
    simp [qlbarCharacter, AddChar.compTrace_apply, AddChar.inv_apply]
  have hchar' : Nonempty (qlbarTraceSheafOf p ℓ k Ψ⁻¹ X f ≅
      qlbarTraceSheafOf p ℓ k Ψ X (-f)) := by
    obtain ⟨e⟩ := hchar
    change Nonempty (ProEtale.condensedArtinSchreierSheafOf
      (Profinite.padicAlgClRingObj ℓ) k X ((qlbarCharacter ℓ Ψ⁻¹).compTrace k) f ≅
      ProEtale.condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k X ((qlbarCharacter ℓ Ψ).compTrace k) (-f))
    rw [hinvchar]
    exact ⟨e⟩
  exact ⟨hadd, hinv, hneg, hchar'⟩

end AlgebraicGeometry.ArtinSchreierTrace
