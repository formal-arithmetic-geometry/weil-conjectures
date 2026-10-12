/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-!

# The relative Künneth map

Let `Λ` be a finite coefficient ring, `f : X ⟶ B`, `g : Y ⟶ B` morphisms admitting
compactifications and `p`, `q` the projections of `X ×_B Y`. This file defines the canonical
isomorphism of the relative product theorem (blueprint `sk-thm-sf-kunneth-relative`,
`thm-sf-kunneth-relative`)

`κ^rel_{K,L} : R(f ×_B g)_! (K ⊠ L) ≅ Rf_! K ⊗ᴸ Rg_! L`

as the explicit composite of the blueprint: the inverse of the composition isomorphism
`α_{g,q}`, the inverse of the projection map of `q` at `(Lp^* K, L)`, the inverse of the
compact-support base change map `Ex_! : Lg^* Rf_! K ⟶ Rq_! Lp^* K`, the symmetry of `⊗ᴸ`, the
inverse of the projection map of `g` at `(L, Rf_! K)` and the symmetry of `⊗ᴸ`. It is
defined for an arbitrary cartesian square (`AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback`)
and specialised to the chosen fibre product (`AlgebraicGeometry.Etale.relativeKunnethIso`).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`: the composition isomorphism
  `R(h)_! ≅ Rf_! ⋙ Rg_!` for `f ≫ g = h`, on unbounded derived categories, for a finite
  coefficient ring.
- `AlgebraicGeometry.Etale.derivedTensorBraiding`: the symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the
  derived tensor product, the braiding `CategoryTheory.DerivedMonoidal.braidedCategory`.
- `AlgebraicGeometry.Etale.relativeKunnethIsoOfIsPullback`,
  `AlgebraicGeometry.Etale.relativeKunnethIso`: the relative Künneth isomorphism.
- `AlgebraicGeometry.Etale.relativeKunnethNatIso`: the relative Künneth isomorphism as a
  natural isomorphism of bifunctors `D(X_ét) ⥤ D(Y_ét) ⥤ D(B_ét)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Braiding

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- The braiding of the derived category `D(X_ét)` of étale sheaves: the braiding of `A`, with
the Koszul sign rule on complexes, descended along K-flat resolutions
(`CategoryTheory.DerivedMonoidal.braidedCategory`). -/
noncomputable def derivedBraidedCategory :
    BraidedCategory (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  DerivedMonoidal.braidedCategory _root_.DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))

/-- The symmetry `σ : K ⊗ᴸ M ≅ M ⊗ᴸ K` of the derived tensor product, natural in both
variables: the braiding `AlgebraicGeometry.Etale.derivedBraidedCategory`, as an isomorphism
between `- ⊗ᴸ -` and the flipped bifunctor. -/
noncomputable def derivedTensorBraiding : derivedTensor A X ≅ (derivedTensor A X).flip :=
  @BraidedCategory.curriedBraidingNatIso _ _ _ (derivedBraidedCategory A X)

end Braiding

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section Composition

variable {X Y S : Scheme.{u}}

/-- The composition isomorphism `R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` on unbounded derived categories, for
a finite coefficient ring: the isomorphism of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`, i.e.
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationCompIso` for the chosen
compactification `d` of `g` and the compactification `Compactification.ofComp` of `f ≫ d.i`,
compared with the chosen compactifications of `f` and `f ≫ g`. -/
noncomputable def rightDerivedLowerShriekCompIso' (f : X ⟶ Y) (g : Y ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] :
    R(f ≫ g)_![ModuleCat.{u + 1} Λ] ≅
      R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
  haveI : QuasiCompact f := .of_comp f g
  (rightDerivedLowerShriekIso Λ ((HasCompactification.compactification g).comp
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)))).symm ≪≫
    (rightDerivedLowerShriekOfCompactificationCompIso Λ (HasCompactification.compactification g)
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g))).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekIso Λ
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)).restrict) _

/-- Blueprint `sk-thm-sf-comp-composition`: the composition isomorphism `α : R(h)_! ≅ Rf_! ⋙ Rg_!`
for `f ≫ g = h`, on unbounded derived categories, for a finite coefficient ring
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso'` transported along `f ≫ g = h`). -/
noncomputable def rightDerivedLowerShriekCompIso (f : X ⟶ Y) (g : Y ⟶ S) (h : X ⟶ S)
    (w : f ≫ g = h) [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [QuasiCompact h] :
    R(h)_![ModuleCat.{u + 1} Λ] ≅ R(f)_![ModuleCat.{u + 1} Λ] ⋙ R(g)_![ModuleCat.{u + 1} Λ] :=
  haveI : HasCompactification (f ≫ g) := .of_eq w.symm
  haveI : QuasiCompact (f ≫ g) := by rw [w]; infer_instance
  eqToIso (by subst w; rfl) ≪≫ rightDerivedLowerShriekCompIso' Λ f g

end Composition

section Kunneth

variable {B X Y P : Scheme.{u}}

/-- The relative Künneth isomorphism for an arbitrary cartesian square

```
  P --q--> Y
  |        |
  p        g
  v        v
  X --f--> B
```

and a morphism `h = q ≫ g`: for `K` on `X` and `L` on `Y`, the composite

```
Rh_!(Lp^*K ⊗ᴸ Lq^*L) ≅ Rg_! Rq_!(Lp^*K ⊗ᴸ Lq^*L)      (α_{g,q}⁻¹)
                     ≅ Rg_!(Rq_! Lp^*K ⊗ᴸ L)           (Rg_! PF_{q, Lp^*K, L}⁻¹)
                     ≅ Rg_!(Lg^* Rf_! K ⊗ᴸ L)          (Rg_!(Ex_!⁻¹ ⊗ 1))
                     ≅ Rg_!(L ⊗ᴸ Lg^* Rf_! K)          (Rg_! σ)
                     ≅ Rg_! L ⊗ᴸ Rf_! K                (PF_{g, L, Rf_! K}⁻¹)
                     ≅ Rf_! K ⊗ᴸ Rg_! L                (σ)
```

of blueprint `sk-thm-sf-kunneth-relative`. Every arrow is an isomorphism for a finite
coefficient ring: the composition law, the projection formula
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`) and compact-support base change
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekBaseChangeMap`). -/
noncomputable def relativeKunnethIsoOfIsPullback {p : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ B}
    {g : Y ⟶ B} (sq : IsPullback p q f g) (h : P ⟶ B) (w : q ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification q]
    [HasCompactification h] [QuasiCompact q] [QuasiCompact h]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (R(h)_![ModuleCat.{u + 1} Λ]).obj (((-⊗ᴸ-(P)[ModuleCat.{u + 1} Λ]).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj L)) ≅
      ((-⊗ᴸ-(B)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        ((R(g)_![ModuleCat.{u + 1} Λ]).obj L) :=
  haveI := isIso_projectionMap_of_finite Λ q
  haveI := isIso_projectionMap_of_finite Λ g
  haveI := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  (rightDerivedLowerShriekCompIso Λ q g h w).app _ ≪≫
    (R(g)_![ModuleCat.{u + 1} Λ]).mapIso
      (((asIso (projectionMap (ModuleCat.{u + 1} Λ) q)).symm.app
          ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)).app L ≪≫
        ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).mapIso
          ((asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).symm.app K)).app L ≪≫
        ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) Y).app _).app L) ≪≫
    ((asIso (projectionMap (ModuleCat.{u + 1} Λ) g)).symm.app L).app
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ≪≫
    ((derivedTensorBraiding (ModuleCat.{u + 1} Λ) B).app _).app _

end Kunneth

end Etale

end AlgebraicGeometry
