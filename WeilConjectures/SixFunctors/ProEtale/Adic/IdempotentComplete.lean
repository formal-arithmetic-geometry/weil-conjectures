/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Retract
public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.KaroubianSubcategory
public import WeilConjectures.SixFunctors.ClosedImmersionStages
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization

/-!
# Idempotent completeness of `Dᵇc(Y, ℚ̄_ℓ)`

Blueprint `lem-weil-qbar-idempotent-complete`: the common-stage coefficient category
`C_Y = Dᵇc(Y, ℚ̄_ℓ)` is idempotent complete, and the canonical functor `C_Y ⥤ Kar(C_Y)` into its
Karoubi envelope is an exact equivalence.

In the repository `Dᵇc(Y, ℚ̄_ℓ)` is realised in the Bhatt–Scholze model
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`): the bounded objects of
the derived category of `ℓ`-adic pro-étale sheaves with constructible cohomology sheaves. Its
objects are bounded for the standard t-structure, so their idempotents split in the ambient
derived category (`CategoryTheory.Triangulated.TStructure.isSplit_of_bounded`, the Karoubian
theorem for bounded t-structures `thm-weil-karoubian-bounded-t`), and the summands lie again in
`Dᵇc(Y, ℚ̄_ℓ)`: their cohomology sheaves are retracts of constructible sheaves, which are
constructible because constructible sheaves are closed under kernels.

## Implementation notes

The blueprint proves the lemma by filtered retract descent from the finite stages
`Dᵇc(Y, E)`. In the Bhatt–Scholze model the category `Dᵇc(Y, ℚ̄_ℓ)` is not a `2`-colimit of
the finite stages, and the bounded t-structure argument applies directly.

The scheme `Y` is assumed locally noetherian: closure of constructible `ℓ`-adic sheaves under
kernels, hence under retracts, and the triangulated structure of `Dᵇc(Y, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.DerivedCategory.isTriangulated_boundedConstructibleAdic`) are only
available there. All the schemes of the blueprint are of finite type over a field.
-/

@[expose] public section

universe u

open CategoryTheory Limits Idempotents

namespace AlgebraicGeometry

open Scheme

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [IsLocallyNoetherian Y]

/-- On a locally noetherian scheme, constructible `ℓ`-adic sheaves are stable under retracts,
being closed under kernels. -/
instance ProEtale.isStableUnderRetracts_adicConstructibleSheaf :
    (ProEtale.adicConstructibleSheaf l Y).IsStableUnderRetracts :=
  ObjectProperty.isStableUnderRetracts_of_isClosedUnderKernels _

/-- On a locally noetherian scheme, `Dᵇc(Y, ℚ̄_ℓ)` is stable under retracts: the cohomology
sheaves of a retract are retracts of constructible sheaves. -/
instance ProEtale.isStableUnderRetracts_boundedConstructibleAdic :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).IsStableUnderRetracts where
  of_retract e h := ⟨_root_.DerivedCategory.TStructure.t.bounded.prop_of_retract e h.1,
    (_root_.DerivedCategory.homologyProperty _).prop_of_retract e h.2⟩

/-- Blueprint `lem-weil-qbar-idempotent-complete`: Idempotent completeness of the common-stage
category.

The category `C_Y = Dᵇc(Y, ℚ̄_ℓ)` is idempotent complete. Its objects are bounded, so their
idempotents split in the derived category of `ℓ`-adic sheaves
(`CategoryTheory.Triangulated.TStructure.isSplit_of_bounded`), through retracts which again
lie in `Dᵇc(Y, ℚ̄_ℓ)`. -/
theorem ProEtale.isIdempotentComplete_boundedConstructibleAdic :
    IsIdempotentComplete (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory :=
  _root_.DerivedCategory.TStructure.t.isIdempotentComplete_fullSubcategory_of_le_bounded _
    fun _ h ↦ h.1

/-- Blueprint `lem-weil-qbar-idempotent-complete`: Idempotent completeness of the common-stage
category.

The canonical functor `C_Y ⥤ Kar(C_Y)` from `C_Y = Dᵇc(Y, ℚ̄_ℓ)` into its Karoubi envelope is an
exact equivalence: it is an equivalence since `C_Y` is idempotent complete
(`AlgebraicGeometry.ProEtale.isIdempotentComplete_boundedConstructibleAdic`), and it is a
triangulated functor for the triangulated structure of the Karoubi envelope
(`CategoryTheory.Idempotents.Karoubi.pretriangulated`). -/
theorem ProEtale.isEquivalence_toKaroubi_boundedConstructibleAdic :
    (toKaroubi
        (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory).IsEquivalence ∧
      (toKaroubi
        (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory).IsTriangulated :=
  have := ProEtale.isIdempotentComplete_boundedConstructibleAdic l Y
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
