/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence

/-!

# The exceptional projection morphism of a proper morphism

For a proper morphism `f`, the exceptional projection morphism
`PF^!_{f,T,M} : Rf_! T ⊗ᴸ M ⟶ Rf_! (T ⊗ᴸ Lf^* M)` is the projection morphism of the adjunction
`Lf^* ⊣ Rf_!` (the adjunction `Lf^* ⊣ Rf_*` transported along `Rf_! ≅ Rf_*`): its adjoint is
`Lf^* (Rf_! T ⊗ᴸ M) ≅ Lf^* Rf_! T ⊗ᴸ Lf^* M ⟶ T ⊗ᴸ Lf^* M`, the counit tensored with
`Lf^* M`.

## Sorried input

- `ProEtale.CondensedRing.upperStar_map_exceptionalProjection_comp_counit`: the clause
  "identification with the direct-image projection formula through `Rf_! ≅ Rf_*` for proper `f`"
  of blueprint `prop-sf-pf-coherence` (section `sec-six-functors`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- **The exceptional projection morphism of a proper morphism is the projection morphism of
`Lf^* ⊣ Rf_!`** (blueprint `prop-sf-pf-coherence`, the identification with the direct-image
projection formula through `Rf_! ≅ Rf_*` for proper `f`): the adjoint of `PF^!_{f,T,M}` for
`Lf^* ⊣ Rf_!` is the counit at `T` tensored with `Lf^* M`, read through the tensor structure of
`Lf^*`. -/
theorem upperStar_map_exceptionalProjection_comp_counit (f : X ⟶ Y) [IsProper f.left]
    (T : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ f).map
        (boundedConstructibleExceptionalProjectionMorphism _ ℓ f T M) ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).counit.app
        (T ⊗ (boundedConstructibleUpperStar _ ℓ f).obj M) =
    Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ f)
        ((boundedConstructibleLowerShriek _ ℓ f).obj T) M ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).counit.app T ▷
        (boundedConstructibleUpperStar _ ℓ f).obj M :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
