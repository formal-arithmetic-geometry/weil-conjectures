/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriek

/-!
# Reduction modulo `ℓⁿ` commutes with `Rf_!` and `Rf^!` along closed immersions

For a closed immersion `f`, the reduction modulo `ℓⁿ` read on the small étale site
(`ProEtale.CondensedRing.etaleReduction`) commutes with `Rf_!` through an isomorphism `γ`
(`ProEtale.CondensedRing.etaleReductionLowerShriekIsoOfIsClosedImmersion`), and the transpose of
any such `γ` under `Rf_! ⊣ Rf^!` is an isomorphism
(`ProEtale.CondensedRing.isIso_mateEquiv_etaleReduction_of_isClosedImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- Blueprint `det-prop-scalar-six-exceptional` (with the compact-support comparison `γ^!` of
`det-prop-scalar-six-compact-support`), for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the
étale site (`sk-def-sf-categories`), for a closed immersion `f`. **Reduction modulo `ℓⁿ`
commutes with `Rf_!` and with `Rf^!`**: there is an isomorphism `γ^! : (Rf_! K)_{𝒪_E ⧸ ℓⁿ} ≅
Rf_! (K_{𝒪_E ⧸ ℓⁿ})` whose transpose `β : (Rf^! K)_{𝒪_E ⧸ ℓⁿ} ⟶ Rf^! (K_{𝒪_E ⧸ ℓⁿ})` under
`Rf_! ⊣ Rf^!` is an isomorphism.

This is weaker than the blueprint node, and enough for its use in the trace formula: it covers
only closed immersions `f` (the case used by the trace formula: the supports of graphs of
correspondences), and it only asserts that some isomorphism `γ` with invertible transpose
exists, without identifying `γ` with the canonical `γ^!` of the blueprint (nor `β` with its
canonical comparison). -/
theorem exists_etaleReductionLowerShriekIso (f : Z ⟶ Y) [IsClosedImmersion f.left] :
    ∃ γ : boundedConstructibleLowerShriek (Profinite.padicIntegersRingObj ℓ E) ℓ f ⋙
        etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n Z ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left,
      IsIso (mateEquiv (boundedConstructibleUpperShriekAdjunction _ ℓ f)
        (Etale.rightDerivedUpperShriekAdjunction _ f.left) (TwoSquare.mk _ _ _ _ γ.inv)) :=
  ⟨etaleReductionLowerShriekIsoOfIsClosedImmersion ℓ E n f,
    isIso_mateEquiv_etaleReduction_of_isClosedImmersion ℓ E n f _⟩

end AlgebraicGeometry.ProEtale.CondensedRing
