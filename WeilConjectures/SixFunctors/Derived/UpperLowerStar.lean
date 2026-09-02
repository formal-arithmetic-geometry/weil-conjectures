/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived Upper Star and Lower Star

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerStar` : total right derived of lower star, with
  scoped notation `R(g)_*[A]`, prefixing the notation `(g)_*[A]` of the underived
  pushforward by `R`.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` : total right derived of lower star on
  bounded below derived category, with scoped notation `R(g)_*[A]+`.

- `AlgebraicGeometry.Etale.leftDerivedUpperStar` : total left derivation of upper star, with
  scoped notation `L(g)^*[A]`, prefixing the notation `(g)^*[A]` of the underived pullback
  by `L`.

- `AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory` : the derived
  pullback `Lg^*` is the functor `(g)^*[A].mapDerivedCategory` induced levelwise by the
  exact functor `g^*`.

- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` : the composition isomorphism
  `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`.

- `AlgebraicGeometry.Etale.leftDerivedUpperStarHomologyFunctorIso` : the derived pullback
  commutes with the homology functors, `H^n ⋙ g^* ≅ Lg^* ⋙ H^n`.

- `AlgebraicGeometry.Etale.singleFunctorCompLeftDerivedUpperStarIso` : the derived
  pullback of a sheaf placed in degree `0` is the pullback of the sheaf placed in degree
  `0`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerStar

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctor

@[inherit_doc rightDerivedLowerStar]
scoped notation "R(" g ")_*[" A "]" =>
  rightDerivedLowerStar A g

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on the
*bounded below* derived categories of étale sheaves. -/
noncomputable def rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctorPlus

@[inherit_doc rightDerivedLowerStarPlus]
scoped notation "R(" g ")_*[" A "]+" =>
  rightDerivedLowerStarPlus A g

end Etale

end DerivedLowerStar

section DerivedUpperStar

/-!
## The derived pullback `Lg^*`

The pullback `g^* = Etale.upperStar` is left derived using the K-flat left
derivability structure of `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`.
This requires the source sheaf category `Sheaf Y.smallEtaleTopology A` to carry a
preadditive monoidal structure whose tensor product preserves colimits, to have countable
coproducts and exact `ℤ`-indexed colimits, and to admit functorial flat resolutions.
These inputs are stated as hypotheses on the coefficient category `A` only; they are
supplied for the sheaf categories by the instances of the folder
`WeilConjectures.CategoryTheory.GrothendieckAbelian`, with the monoidal structure and its
compatibility with colimits provided by its `Monoidal` subfolder, and its preadditivity
by `CategoryTheory.Sheaf.monoidalPreadditive`, which holds for any sheaf category.

Two of those instances are still `sorry`ed, so everything below depends on them:
`AlgebraicGeometry.Etale.preservesColimitsOfSize_tensorLeft_sheaf` (tensoring an étale
sheaf preserves colimits) and `AlgebraicGeometry.Etale.hasFunctorialFlatResolution_sheaf`
(functorial flat resolutions of étale sheaves). Both are discussed in the module
docstrings of the files that state them.

The additivity and exactness of `g^*` are `Etale.additive_upperStar`,
`Etale.preservesFiniteLimits_upperStar` and `Etale.preservesHomology_upperStar` of
`WeilConjectures.SixFunctors.UpperLowerStar.Etale`; the left exactness there rests on the
sorried `HasSheafify` instance for the small étale site of `Z` and on left exactness of
the left Kan extension along the opposite of base change, both global instances of the
folder `WeilConjectures.CategoryTheory.GrothendieckAbelian` (for an étale `g` the latter
is proved, not sorried). Since `g^*` is exact, it preserves in particular all K-flat
quasi-isomorphisms, which is the input needed by the derivability-structure machinery.
-/

open MonoidalCategory Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/- The preadditive monoidal structure on the coefficient category. It is assumed closed
and braided (as is the intended application `A = ModuleCat.{u + 1} Λ` for a commutative
ring `Λ`, which is even symmetric monoidal closed): that is what makes the class of
sheafification-inverting morphisms of presheaves monoidal, hence what lets the monoidal
structure descend to the étale sheaf categories, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`. Closedness moreover
makes tensoring by a fixed object preserve colimits, which is what the tensor product of
complexes needs; no further tensor-colimit hypothesis on `A` is required. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A] [MonoidalClosed A]

/- Functorial flat resolutions on the coefficient category; they induce functorial flat
resolutions of étale sheaves via `Etale.hasFunctorialFlatResolution_sheaf`. -/
variable [Abelian.HasFunctorialFlatResolution A]

namespace Etale

/-- The total left derived functor `Lg^* : D(Y_ét) ⥤ D(Z_ét)` of the pullback `g^*`
along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of étale
sheaves, defined via the K-flat left derivability structure: `Lg^*` is computed by
applying `g^*` to a K-flat resolution.

Since `g^*` is exact, the counit `Lg^* ∘ Q ⟶ Q ∘ g^*` is in fact an isomorphism
everywhere; the construction via the derivability structure is uniform in the functor
and applies verbatim once `g^*` is replaced by a non-exact functor (e.g. the pullback
of sheaves of modules over a varying sheaf of rings). -/
noncomputable def leftDerivedUpperStar :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  (g)^*[A].leftDerivedFunctor

@[inherit_doc leftDerivedUpperStar]
scoped notation "L(" g ")^*[" A "]" =>
  leftDerivedUpperStar A g

/-- The compatibility of the derived pullback with the levelwise functor: the total left
derived functor `Lg^*`, computed via K-flat resolutions, is canonically isomorphic to
the functor induced by the exact functor `g^*` on the derived categories.

```
                        Lg^*
                 -------------------->
        D(Y_ét)            ≅             D(Z_ét)
                 -------------------->
          (g)^*[A].mapDerivedCategory
```

This is `Functor.leftDerivedFunctorIsoMapDerivedCategory` at `g^*`, restated in terms of
the notation `L(g)^*[A]`, which the general statement does not mention. -/
noncomputable def leftDerivedUpperStarIsoMapDerivedCategory :
    L(g)^*[A] ≅ (g)^*[A].mapDerivedCategory :=
  (g)^*[A].leftDerivedFunctorIsoMapDerivedCategory

/-- The composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ∘ Lg₁^*` of derived pullbacks,
obtained from the underived composition isomorphism `Etale.upperStarComp` and the
compatibility of left derivation with `mapDerivedCategory` for exact functors.

```
                 L(g₁ ≫ g₂)^*
D(R_ét) -------------------------------> D(T_ét)
      |                                    ^
      |                                    |
      +---------> D(S_ét) -----------------+
        L(g₂)^*            L(g₁)^*
```
-/
noncomputable def leftDerivedUpperStarComp {T S R : Scheme.{u}}
    (g₁ : T ⟶ S) (g₂ : S ⟶ R) :
    L(g₁ ≫ g₂)^*[A] ≅ L(g₂)^*[A] ⋙ L(g₁)^*[A] :=
  Functor.leftDerivedFunctorNatIso _ (Etale.upperStarComp A g₁ g₂) ≪≫
    Functor.leftDerivedFunctorCompIso (g₂)^*[A] (g₁)^*[A]

/-- The exactness comparison `H^n ∘ g^* ≅ g^* ∘ H^n`: since the underived pullback `g^*`
on étale sheaves is exact, applying it to the `n`-th homology sheaf of an object of the
derived category computes the `n`-th homology sheaf of the derived pullback.

```
                H^n
D(Y_ét) -----------------> Sh(Y_ét)
   |                           |
 L(g)^*                      (g)^*
   |                           |
   v                           v
D(Z_ét) -----------------> Sh(Z_ét)
                H^n
```

This is `Functor.leftDerivedFunctorHomologyFunctorIso` at `g^*`, restated in terms of the
notation `L(g)^*[A]`, which the general statement does not mention. -/
noncomputable def leftDerivedUpperStarHomologyFunctorIso (n : ℤ) :
    DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology A) n ⋙ (g)^*[A] ≅
      L(g)^*[A] ⋙ DerivedCategory.homologyFunctor (Sheaf Z.smallEtaleTopology A) n :=
  (g)^*[A].leftDerivedFunctorHomologyFunctorIso n

/-- The single-degree comparison for the derived pullback: since the underived pullback
`g^*` on étale sheaves is exact, the derived pullback of a sheaf placed in degree `0` is
the pullback of the sheaf placed in degree `0`, `Lg^*(F[0]) ≅ (g^* F)[0]`.

```
                (-)[0]
Sh(Y_ét) -----------------> D(Y_ét)
    |                           |
  (g)^*                      L(g)^*
    |                           |
    v                           v
Sh(Z_ét) -----------------> D(Z_ét)
                (-)[0]
```

This is `Functor.singleFunctorCompLeftDerivedFunctorIso` at `g^*`, restated in terms of
the notation `L(g)^*[A]`, which the general statement does not mention. -/
noncomputable def singleFunctorCompLeftDerivedUpperStarIso :
    DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology A) 0 ⋙ L(g)^*[A] ≅
      (g)^*[A] ⋙ DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology A) 0 :=
  (g)^*[A].singleFunctorCompLeftDerivedFunctorIso

end Etale

end DerivedUpperStar

end AlgebraicGeometry
