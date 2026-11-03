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
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceTensorAdd

/-! Tensor addition clause for the condensed Artin--Schreier sheaf.

Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/lem-fd-as-lisse.md
(blueprint: lem-fd-as-lisse).

The recorded `qlbarTraceSheafOf` is an abbreviation for the target condensed
Artin--Schreier sheaf.  The qlbar trace tensor theorem supplies the coherence map;
the only remaining input is the explicit trace comparison bridge for an arbitrary
character.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local instance] ZMod.algebra

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry.ArtinSchreierTrace

/-- Tensor addition for the condensed Artin--Schreier sheaf.

Proof source: lem-fd-as-trace-tensor-add.  Apply the generic condensed theorem
with the p-adic algebraic closure coefficient ring; its cardinality-unit
hypothesis follows from the constant-ring equivalence.
(blueprint: lem-fd-as-lisse-tensor-addition).
-/
theorem condensedArtinSchreierSheafOf_tensor_addition
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀ ≠ ℓ)] (X₀ : Scheme.{u})
    [X₀.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (hψ : ψ ≠ 1) (f g : Γ(X₀, ⊤)) :
    Nonempty (condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ f ⊗
      condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ g ≅
      condensedArtinSchreierSheafOf
        (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ (f + g)) := by
  classical
  have hq : IsUnit (Fintype.card k₀ : MonObj.Γ
      (Profinite.padicAlgClRingObj.{u} ℓ)) := by
    have hq0 : IsUnit (Fintype.card k₀ : PadicAlgCl ℓ) := by
      apply isUnit_iff_ne_zero.mpr
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card k₀ ≠ 0)
    simpa only [map_natCast] using
      (Profinite.PadicAlgCl.constRingHom ℓ).isUnit_map hq0
  exact AlgebraicGeometry.ArtinSchreierTrace.condensedArtinSchreier_tensor_add_generic
    (Profinite.padicAlgClRingObj ℓ) k₀ ψ hψ hq X₀ f g

end AlgebraicGeometry.ProEtale
