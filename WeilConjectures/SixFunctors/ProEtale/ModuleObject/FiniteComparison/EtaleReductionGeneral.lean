/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionOpenImmersion

/-!
# Reduction modulo `ℓⁿ` commutes with `Rf_!` and `Rf^!`

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). Every morphism `f : X ⟶ Y` of separated
`k`-schemes of finite type has a reduction comparison for `Rf_!` and `Rf^!`
(`ProEtale.CondensedRing.hasEtaleReductionLowerShriekIso`): `f` is an open immersion followed by
a proper morphism (any compactification of `f`), open immersions and proper morphisms have one
(`ProEtale.CondensedRing.hasEtaleReductionLowerShriekIso_of_isOpenImmersion` and
`ProEtale.CondensedRing.exists_etaleReductionLowerShriekIso`), and the property is stable under
composition (`ProEtale.CondensedRing.HasEtaleReductionLowerShriekIso.comp`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
