/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierCharacters
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierTraceBridge
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceTensorInverse

/-! Inverse and inverse-character clauses for the condensed Artin--Schreier sheaf.
Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/lem-fd-as-lisse.md
(blueprint: lem-fd-as-lisse). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local instance] ZMod.algebra
namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry.ArtinSchreierTrace

set_option maxHeartbeats 5000000 in
-- The four-way categorical tensor transport needs extra elaboration heartbeats.
/-- Tensor inverse and inverse-character identifications.

Apply lem-fd-as-trace-tensor-inverse to the p-adic algebraic closure coefficient
ring. Its cardinality is a unit by the constant-ring homomorphism. The first
conjunct is the tensor inverse; invert the third isomorphism for the requested
negative-function-to-inverse-character direction.
(blueprint: lem-fd-as-lisse-inverse). -/
theorem condensedArtinSchreierSheafOf_inverse
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀ ≠ ℓ)] (X₀ : Scheme.{u})
    [X₀.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (hψ : ψ ≠ 1) (f : Γ(X₀, ⊤)) :
    Nonempty (condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f ⊗
      condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ (-f) ≅
      Mod.regular (condensedRingObj
        (Profinite.padicAlgClRingObj ℓ) X₀)) ∧
    Nonempty (condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ (-f) ≅
      condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ⁻¹ f) := by
  classical
  have hq : IsUnit (Fintype.card k₀ : MonObj.Γ
      (Profinite.padicAlgClRingObj.{u} ℓ)) := by
    have hq0 : IsUnit (Fintype.card k₀ : PadicAlgCl ℓ) := by
      apply isUnit_iff_ne_zero.mpr
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card k₀ ≠ 0)
    simpa only [map_natCast] using
      (Profinite.PadicAlgCl.constRingHom ℓ).isUnit_map hq0
  obtain ⟨hinv, _, ⟨hchar⟩⟩ :=
    AlgebraicGeometry.ArtinSchreierTrace.condensedArtinSchreier_tensor_inverse_generic
      (Profinite.padicAlgClRingObj ℓ) k₀ ψ hψ hq X₀ f
  exact ⟨hinv, ⟨hchar.symm⟩⟩

end AlgebraicGeometry.ProEtale
