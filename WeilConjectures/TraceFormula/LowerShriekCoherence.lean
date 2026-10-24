/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange

/-!

# Coherence of the projection formula

This file records standard coherences of the canonical isomorphisms of the six-functor
formalism on the bounded constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` (SGA 4, Exposé XVII,
§5), stated for the existing projection morphism
`ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism`
(`PF_f : Rf_! K ⊗ᴸ B ⟶ Rf_! (K ⊗ᴸ Lf^* B)`) and the composition isomorphisms
`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`
(`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!`) and `ProEtale.CondensedRing.boundedConstructibleUpperStarComp`
(`L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`).

The companion coherence of compact-support base change with the pasting of cartesian squares
(blueprint `fix-lem-exchanges`, clause (2)) is
`ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert`
(`WeilConjectures.TraceFormula.BaseChangeCoherence`).

## Sorried input

- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_comp`: the
  projection formula is compatible with composition (blueprint `prop-sf-pf-coherence`; SGA 4,
  Exposé XVII, 5.2.2).
- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_baseChange`: the
  projection formula is compatible with compact-support base change (blueprint
  `prop-sf-pf-coherence`).
- `ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_counit`: for `f`
  proper, the projection formula is the projection morphism of `Lf^* ⊣ Rf_!` (blueprint
  `prop-sf-pf-coherence`, `def-exchange-projection`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
  [IsSeparated S.hom]

/-- **The projection formula is compatible with composition** (blueprint `prop-sf-pf-coherence`,
the associativity pentagon; SGA 4, Exposé XVII, 5.2.2): for `f : X ⟶ Y` and `g : Y ⟶ S`, the
projection morphism of `f ≫ g`, followed by the composition isomorphisms
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` and `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, is the composite
```
R(f ≫ g)_! K ⊗ B ≅ Rg_! (Rf_! K) ⊗ B --PF_g--> Rg_! (Rf_! K ⊗ Lg^* B)
  --Rg_! PF_f--> Rg_! Rf_! (K ⊗ Lf^* Lg^* B).
``` -/
theorem boundedConstructibleExceptionalProjectionMorphism_comp (f : X ⟶ Y) (g : Y ⟶ S)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    boundedConstructibleExceptionalProjectionMorphism _ ℓ (f ≫ g) K B ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app
          (K ⊗ (boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj B) ≫
        (boundedConstructibleLowerShriek _ ℓ g).map ((boundedConstructibleLowerShriek _ ℓ f).map
          (K ◁ (boundedConstructibleUpperStarComp _ ℓ f g).hom.app B)) =
      (boundedConstructibleLowerShriekComp_padicAlgCl ℓ f g).hom.app K ▷ B ≫
        boundedConstructibleExceptionalProjectionMorphism _ ℓ g
          ((boundedConstructibleLowerShriek _ ℓ f).obj K) B ≫
        (boundedConstructibleLowerShriek _ ℓ g).map
          (boundedConstructibleExceptionalProjectionMorphism _ ℓ f K
            ((boundedConstructibleUpperStar _ ℓ g).obj B)) :=
  sorry

/-- **The projection formula of a proper morphism is that of `Lf^* ⊣ Rf_!`** (blueprint
`prop-sf-pf-coherence` and `def-exchange-projection`: for `f` proper, `PF^!` is represented by
the projection morphism of the compactification `f = f ∘ 𝟙`, which is the projection morphism of
the adjunction `Lf^* ⊣ Rf_*`; SGA 4, Exposé XVII, 5.2.2 and 5.2.9): the composite of `Lf^*` of
`PF_f`, with the counit of `Lf^* ⊣ Rf_!`, is the comultiplication of the monoidal functor `Lf^*`
followed by the counit,
```
Lf^* (Rf_! K ⊗ B) ⟶ Lf^* Rf_! (K ⊗ Lf^* B) ⟶ K ⊗ Lf^* B
  =  Lf^* (Rf_! K ⊗ B) ≅ Lf^* Rf_! K ⊗ Lf^* B ⟶ K ⊗ Lf^* B.
```
Equivalently `PF_f` is the mate of the comultiplication of `Lf^*`, which makes it compatible with
the tensor products (the associativity pentagon of `prop-sf-pf-coherence`). -/
theorem boundedConstructibleExceptionalProjectionMorphism_counit (f : X ⟶ Y) [IsProper f.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ f).map
        (boundedConstructibleExceptionalProjectionMorphism _ ℓ f K B) ≫
      (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).counit.app
        (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B) =
    Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar _ ℓ f)
        ((boundedConstructibleLowerShriek _ ℓ f).obj K) B ≫
      ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).counit.app K ▷
        (boundedConstructibleUpperStar _ ℓ f).obj B) :=
  sorry

section BaseChange

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The projection formula is compatible with base change** (blueprint `prop-sf-pf-coherence`,
the base change square; SGA 4, Exposé XVII, 5.2.2 and 5.2.9): for a cartesian square
`g' ≫ f = f' ≫ g`, under compact-support base change `Ex_! : Rf_! ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!`, the
monoidal structures of `Lg^*`, `Lg'^*` and the identification `θ : Lg'^* Lf^* ≅ Lf'^* Lg^*`,
`Lg^*` of the projection morphism of `f` is the projection morphism of `f'`:
```
Lg^* (Rf_! K ⊗ B) ⟶ Lg^* Rf_! (K ⊗ Lf^* B) ⟶ Rf'_! Lg'^* (K ⊗ Lf^* B)
  ≅ Rf'_! (Lg'^* K ⊗ Lg'^* Lf^* B) ≅ Rf'_! (Lg'^* K ⊗ Lf'^* Lg^* B)
=  Lg^* (Rf_! K ⊗ B) ≅ Lg^* Rf_! K ⊗ Lg^* B ⟶ Rf'_! Lg'^* K ⊗ Lg^* B
  ⟶ Rf'_! (Lg'^* K ⊗ Lf'^* Lg^* B).
```
(`CategoryTheory.ProjectionBaseChange.PFBaseChange`, with `K` and `B` the variables of the formula
and `θ = boundedConstructiblePullbackSquareComparison`). -/
theorem boundedConstructibleExceptionalProjectionMorphism_baseChange (sq : IsPullback g' f' f g) :
    ProjectionBaseChange.PFBaseChange (boundedConstructibleUpperStar _ ℓ g)
      (boundedConstructibleUpperStar _ ℓ g')
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)
      (boundedConstructiblePullbackSquareComparison _ ℓ sq.toCommSq)
      (boundedConstructibleExceptionalProjection _ ℓ f)
      (boundedConstructibleExceptionalProjection _ ℓ f') :=
  sorry

end BaseChange

end AlgebraicGeometry.ProEtale.CondensedRing
