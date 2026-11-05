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

end AlgebraicGeometry.ProEtale.CondensedRing
