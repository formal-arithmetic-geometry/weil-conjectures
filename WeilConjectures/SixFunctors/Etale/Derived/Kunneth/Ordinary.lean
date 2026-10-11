/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

/-!
# The Künneth map in ordinary étale cohomology

Let `A` be a monoidal Grothendieck abelian coefficient category. For a commutative square of
schemes

```
  W --q--> Y
  |        |
  p        g
  v        v
  X --f--> S
```

with diagonal `c = p ≫ f = q ≫ g`, the *Künneth map* is the morphism

`κ_{E,K} : Rf_* E ⊗ᴸ Rg_* K ⟶ Rc_* (Lp^* E ⊗ᴸ Lq^* K)`

in `D(S_ét)`, adjoint to `Lc^*(Rf_* E ⊗ᴸ Rg_* K) ≅ Lp^* Lf^* Rf_* E ⊗ᴸ Lq^* Lg^* Rg_* K ⟶
Lp^* E ⊗ᴸ Lq^* K`. The variant needed for the proof of the Künneth formula is the
*base change map for a pushforward tensored with a complex*: for a commutative square
`h ≫ f' = e ≫ g` it is the morphism

`A' ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* A' ⊗ᴸ Le^* F)`,

adjoint to `Lh^*(A' ⊗ᴸ Lf'^* Rg_* F) ≅ Lh^* A' ⊗ᴸ Le^* Lg^* Rg_* F ⟶ Lh^* A' ⊗ᴸ Le^* F`.

This file also introduces the constant complex functor `D(Λ) ⥤ D(X_ét, Λ)` and the (torsion
étale) cohomological dimension, and states the inputs of the Künneth formula (Stacks, Section
0F0Y and following).

## Main definitions

- `AlgebraicGeometry.Etale.kunnethMap` (`def-kun-kunneth-map`): the Künneth map.
- `AlgebraicGeometry.Etale.tensorBaseChangeMap`: the map of `lem-kun-0f1j` and `lem-kun-0f1n`.
- `AlgebraicGeometry.Etale.constantFunctor` (`def-kun-constant-sheaf`): `K ↦ K_X`.
- `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimension`,
  `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimensionMorphism` (`def-kun-cd`).

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Maps

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {S X Y W : Scheme.{u}}

/-- Blueprint `def-kun-kunneth-map`: the Künneth map.

For a commutative square `p ≫ f = c = q ≫ g` (with `p : W ⟶ X`, `q : W ⟶ Y`, `f : X ⟶ S`,
`g : Y ⟶ S`) and `E ∈ D(X_ét)`, `K ∈ D(Y_ét)`, the Künneth map

`κ_{E,K} : Rf_* E ⊗ᴸ Rg_* K ⟶ Rc_* (Lp^* E ⊗ᴸ Lq^* K)`

is the transpose along `Lc^* ⊣ Rc_*` of the composite

`Lc^*(Rf_* E ⊗ᴸ Rg_* K) ≅ Lc^* Rf_* E ⊗ᴸ Lc^* Rg_* K ≅ Lp^* Lf^* Rf_* E ⊗ᴸ Lq^* Lg^* Rg_* K
  ⟶ Lp^* E ⊗ᴸ Lq^* K`

of the monoidality of `Lc^*`, the composition isomorphisms `Lc^* ≅ Lp^* Lf^*`,
`Lc^* ≅ Lq^* Lg^*`, and the counits of `Lf^* ⊣ Rf_*` and `Lg^* ⊣ Rg_*`. -/
noncomputable def kunnethMap (p : W ⟶ X) (q : W ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (c : W ⟶ S)
    (hp : p ≫ f = c) (hq : q ≫ g = c)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((-⊗ᴸ-(S)[A]).obj (R((f)_*[A]).obj E)).obj (R((g)_*[A]).obj K) ⟶
      R((c)_*[A]).obj (((-⊗ᴸ-(W)[A]).obj (L((p)^*[A]).obj E)).obj (L((q)^*[A]).obj K)) :=
  (derivedUpperStarLowerStarAdjunction A c).homEquiv _ _
    (((leftDerivedUpperStarTensorComparison A c).app _).app _ ≫
      ((-⊗ᴸ-(W)[A]).map ((leftDerivedUpperStarComp A p f c hp.symm).hom.app _ ≫
          L((p)^*[A]).map ((derivedUpperStarLowerStarAdjunction A f).counit.app E))).app _ ≫
      ((-⊗ᴸ-(W)[A]).obj _).map ((leftDerivedUpperStarComp A q g c hq.symm).hom.app _ ≫
          L((q)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app K)))

variable {X' S' T : Scheme.{u}}

/-- The base change map for a pushforward tensored with a complex (`lem-kun-0f1j`,
`lem-kun-0f1n`): for a commutative square `h ≫ f' = e ≫ g` (with `h : Y ⟶ X'`, `e : Y ⟶ T`,
`f' : X' ⟶ S'`, `g : T ⟶ S'`) and `M ∈ D(X'_ét)`, `F ∈ D(T_ét)`, the morphism

`M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)`

is the transpose along `Lh^* ⊣ Rh_*` of the composite

`Lh^*(M ⊗ᴸ Lf'^* Rg_* F) ≅ Lh^* M ⊗ᴸ Lh^* Lf'^* Rg_* F ≅ Lh^* M ⊗ᴸ Le^* Lg^* Rg_* F
  ⟶ Lh^* M ⊗ᴸ Le^* F`

of the monoidality of `Lh^*`, the composition isomorphisms through `L(h ≫ f')^*` and the counit
of `Lg^* ⊣ Rg_*`. -/
noncomputable def tensorBaseChangeMap (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
    (w : h ≫ f' = e ≫ g) (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    ((-⊗ᴸ-(X')[A]).obj M).obj (L((f')^*[A]).obj (R((g)_*[A]).obj F)) ⟶
      R((h)_*[A]).obj (((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M)).obj (L((e)^*[A]).obj F)) :=
  (derivedUpperStarLowerStarAdjunction A h).homEquiv _ _
    (((leftDerivedUpperStarTensorComparison A h).app _).app _ ≫
      ((-⊗ᴸ-(Y)[A]).obj _).map ((leftDerivedUpperStarComp A h f').inv.app _ ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app _ ≫
          L((e)^*[A]).map ((derivedUpperStarLowerStarAdjunction A g).counit.app F)))

end Maps

section Constant

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The constant sheaf functor preserves finite limits: it is the constant presheaf functor
followed by sheafification. -/
instance preservesFiniteLimits_constantSheaf :
    PreservesFiniteLimits (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  comp_preservesFiniteLimits (Functor.const _) (presheafToSheaf _ _)

/-- Blueprint `def-kun-constant-sheaf`: constant sheaves and constant complexes.

The constant complex functor `D(Λ) ⥤ D(X_ét, Λ)`, `K ↦ K_X`: the functor induced on derived
categories by the exact constant sheaf functor `M ↦ M_X`. -/
noncomputable def constantFunctor :
    DerivedCategory (ModuleCat.{u + 1} Λ) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapDerivedCategory

/-- Blueprint `def-kun-cd` (for sheaves of `Λ`-modules): the scheme `X` has *finite
cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with `H^q(X, F) = 0` for
every étale sheaf `F` of `Λ`-modules and every `q > d`. For a torsion ring `Λ` every such sheaf
is a torsion abelian sheaf, so this follows from finiteness of the torsion étale cohomological
dimension `cd(X)` of the blueprint. -/
def HasFiniteCohomologicalDimension : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))

variable {X} in
/-- Blueprint `def-kun-cd` (for morphisms, and sheaves of `Λ`-modules): the morphism `f` has
*finite cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with
`R^q f_* F = 0` for every étale sheaf `F` of `Λ`-modules and every `q > d`. -/
def HasFiniteCohomologicalDimensionMorphism {Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F)))

end Constant

end Etale

end AlgebraicGeometry
