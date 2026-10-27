/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.VectorPurityFiniteReduction
import Sheaf.Paper.FiniteTateScalarSourceExistence

/-! # Existence of the normalized scalar Tate line comparison.

The comparison is the degree-one member of the uniquely normalized finite Tate scalar
source system.  This intermediate statement isolates that construction from the vector
purity compatibility calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- A coefficient map admits the normalized degree-one Tate line comparison needed for
scalar reduction.

Source: current blueprint `sec-smooth-purity/sk-prop-an`,
`cor-pur-vector-bundle-purity.proof.md`, paragraph 2, Kummer normalization.

Proof: the finite Tate scalar source normalization supplies a compatible family of Tate
line comparisons.  Its degree-one component is the required comparison, and the generator
normalization is exactly `PurityScalarLineNormalization`.  The annihilator in the target
coefficient ring is transported by the coefficient homomorphism, while the stalkwise
unit condition follows from the given unit on global sections.  No vector purity or
compactification data is used in this construction.
(blueprint: lem-pur-normalized-vector-purity-scalar-line-witness). -/
theorem exists_purityScalarLineNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B]
    (hB : IsUnit (N : Γ(B, ⊤)))
    (A' : Type (u + 1)) [CommRing A'] [Finite A'] (φ : A →+* A') :
    ∃ hA' : (N : A') = 0,
    ∃ c : (Etale.purityScalarSheaf φ B).obj
        (Scheme.finiteEtaleTateLine B N A hA) ≅
      Scheme.finiteEtaleTateLine B N A' hA',
    PurityScalarLineNormalization φ N hA hA' B c := by
  have hA' : (N : A') = 0 := by
    simpa only [map_natCast, map_zero] using congrArg φ hA
  have hstalk : ∀ x : B, IsUnit (N : B.presheaf.stalk x) := by
    intro x
    simpa only [map_natCast] using hB.map (B.presheaf.germ ⊤ x (by trivial)).hom
  obtain ⟨β, hβ, _⟩ :=
    finite_tate_scalar_source_normalization_exists φ N hN hA hA' B hstalk
  refine ⟨hA', β 1, ?_⟩
  intro U a z
  rw [Adjunction.homEquiv_apply]
  change ((β 1).hom.hom.app U)
      (((Etale.purityScalarSheafAdjunction φ B).unit.app
        (Scheme.finiteEtaleTateTwist B N A hA 1)).hom.app U
          (Scheme.finiteEtaleTateOneGenerator A N B hA U a z)) = _
  have hgen := hβ.1 1 U a 1 (fun _ ↦ z)
  simpa only [one_smul, mul_one, id_eq, Scheme.finiteTateEtalePowerGenerator] using hgen

end WeilConjectures.PurityFiniteSetting
