/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CoefficientChangeComponents

/-!
# The unit and counit of `Lf^* ⊣ Rf_*` on bounded constructible `𝒪_E`-complexes

The adjunction `Lf^* ⊣ Rf_*` on bounded constructible complexes with coefficients in `𝒪̲_E`
(`ProEtale.CondensedRing.PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction`)
is the restriction of the ambient adjunction
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`: its unit and counit are, on the
ambient derived categories, those of the ambient adjunction. This is the `𝒪_E` case of the
corresponding lemmas for `ℚ̄_ℓ` and `E` in
`CoefficientChangeComponents`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

/-- Blueprint `proposition-six-operations-dctf--16`, the coefficient ring `𝒪_E`: on the ambient
derived category, the unit of `Lf^* ⊣ Rf_*` on bounded constructible complexes is the unit of
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_unit_app_hom'
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).unit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f.left).unit.app
        K.obj :=
  restrictFullyFaithful_derivedUpperStarLowerStarAdjunction_unit_app_hom ℓ f _ K

/-- Blueprint `proposition-six-operations-dctf--16`, the coefficient ring `𝒪_E`: on the ambient
derived category, the counit of `Lf^* ⊣ Rf_*` on bounded constructible complexes is the counit
of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`. -/
lemma boundedConstructibleUpperStarLowerStarAdjunction_counit_app_hom'
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    ((boundedConstructibleUpperStarLowerStarAdjunction ℓ E f).counit.app K).hom =
      (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E) f.left).counit.app
        K.obj :=
  restrictFullyFaithful_derivedUpperStarLowerStarAdjunction_counit_app_hom ℓ f _ K

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
