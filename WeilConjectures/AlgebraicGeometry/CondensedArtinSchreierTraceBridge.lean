/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierCharacters
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison

/-! Comparison data reducing an arbitrary finite-field character to a trace character.

Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/lem-fd-as-lisse.md
(blueprint: lem-fd-as-lisse).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local instance] ZMod.algebra

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry.ArtinSchreierTrace

/-! The comparison is deliberately only comparison data.  The lisse and tensor
clauses are obtained from the qlbar trace statements after this bridge. -/
/-- Every nontrivial condensed character is compared with one qlbar trace character.

Proof source: lem-wft-as-comparison (1)--(2).  Choose a nontrivial character
`Ψ` of `ZMod (ringChar k₀)` with values in `PadicAlgCl ℓ`, apply the character
classification to its constant global-section character, and use the unique
nonzero shift `a`.  The second part of lem-wft-as-comparison transports the
degree-cardinality projector to the prime-degree trace projector.  The same
comparison is natural in the function and for the inverse character.  This
statement records precisely that transport data; it does not include any
lissity, tensor, or inverse conclusion.
(blueprint: lem-fd-as-lisse). -/
theorem condensedArtinSchreier_trace_bridge
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀).Prime] [Fact (ringChar k₀ ≠ ℓ)]
    [Algebra (ZMod (ringChar k₀)) k₀] (X₀ : Scheme.{u})
    [X₀.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (hψ : ψ ≠ 1) :
    ∃ (Ψ : AddChar (ZMod (ringChar k₀)) (PadicAlgCl ℓ)),
      ∃ (a : k₀ˣ),
        (Ψ ≠ 1) ∧
        (ψ = ((qlbarCharacter ℓ Ψ).compTrace k₀).mulShift (a : k₀)) ∧
      (∀ h : Γ(X₀, ⊤),
        Nonempty (condensedArtinSchreierSheafOf
            (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ h ≅
          qlbarTraceSheafOf (ringChar k₀) ℓ k₀ Ψ X₀
            (scalar k₀ X₀ (a : k₀) * h))) ∧
      (∀ h : Γ(X₀, ⊤),
        Nonempty (condensedArtinSchreierSheafOf
            (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ⁻¹ h ≅
          qlbarTraceSheafOf (ringChar k₀) ℓ k₀ Ψ⁻¹ X₀
            (scalar k₀ X₀ (a : k₀) * h))) := by
  sorry

end AlgebraicGeometry.ProEtale
