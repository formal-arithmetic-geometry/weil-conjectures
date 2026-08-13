/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.DerivedFunctors.Full

/-!

# The derived base-change morphism of a cartesian square

Fix a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : CommSq g' f' f g` (the base-change theorems will additionally require the
square to be cartesian, `IsPullback g' f' f g`, but no such hypothesis enters the
*construction* of the base-change morphism).

Using the derived functors of `WeilConjectures.SixFunctors.DerivedFunctors.Full` — the
derived pullbacks `Lg^*` (isomorphic to the exact `g^*` levelwise) and the derived
pushforwards `Rf_*` on the unbounded derived categories of étale sheaves — together with
the derived adjunctions `Lf^* ⊣ Rf_*`, this file constructs the *derived base-change
morphism*

`BC_sq : Lg^* ⋙ Rf'_* ⟶ Rf'_* ∘ Lg'^*`, i.e. `Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`
(in diagrammatic `⋙`-order),

as the composite of three named transformations, following the reference:

- *unit insertion* `u_sq`, inserting the unit of `Lf'^* ⊣ Rf'_*`;
- *square transport* `s_sq`, transporting along the pullback comparison
  `θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` of the square;
- *counit contraction* `c_sq`, contracting with the counit of `Lf^* ⊣ Rf_*`.

Proper base change and smooth base change are two different theorems asserting that this
single morphism is an isomorphism under two different sets of geometric hypotheses; the
hypotheses are therefore *not* built into the definition.

The file also constructs the cohomological base-change morphism
`g^* H^q(Rf_* K) ⟶ H^q(Rf'_* Lg'^* K)` (using that the underived `g^*` is exact) and its
classical sheaf-level form `g^* R^q f_* F ⟶ R^q f'_* g'^* F` for the higher direct images
`R^q f_* F := H^q(Rf_*(F[0]))`.

## Main definitions

- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp`: the composition isomorphism
  `L(h₁ ≫ h₂)^* ≅ Lh₁^* ∘ Lh₂^*` of derived pullbacks (infrastructure input, sorried).
- `AlgebraicGeometry.Etale.pullbackSquareComparison`: the pullback comparison `θ_sq` of a
  commutative square.
- `AlgebraicGeometry.Etale.baseChangeUnitStep`, `Etale.baseChangeSquareStep`,
  `Etale.baseChangeCounitStep`: the three steps of the construction.
- `AlgebraicGeometry.Etale.baseChange`: the derived base-change morphism `BC_sq`.
- `AlgebraicGeometry.Etale.cohomologicalBaseChange`: the cohomological base-change
  morphism `BC^q_sq`.
- `AlgebraicGeometry.Etale.higherDirectImage`: the higher direct image `R^q f_*`.
- `AlgebraicGeometry.Etale.sheafBaseChange`: the classical base-change morphism
  `g^* R^q f_* F ⟶ R^q f'_* g'^* F` on sheaves.

-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

/- Sheafification, pointwise left Kan extensions and chosen localized derived categories
for the small étale sites of all schemes at once, following the convention of
`WeilConjectures.ConstructibleSheaf.Defs`. -/
variable [∀ (T : Scheme.{u}), HasWeakSheafify T.smallEtaleTopology A]
  [∀ (T S : Scheme.{u}) (φ : T ⟶ S) (F : S.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension F]
  [∀ (T : Scheme.{u}), HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology A)]

/- The preadditive monoidal structure with its compatibilities with coproducts and
`ℤ`-indexed colimits, and functorial flat resolutions, on the étale sheaf categories of
all schemes at once: the K-flat resolution package needed for the derived pullbacks, as
in the sections `DerivedUpperStar` and `DerivedUpperLowerStarAdjunction` of
`WeilConjectures.SixFunctors.DerivedFunctors.Full`. -/
variable [∀ (T : Scheme.{u}), MonoidalCategory (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}), MonoidalPreadditive (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}) (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j}))
    (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}) (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf T.smallEtaleTopology A)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (T : Scheme.{u}) (X₁ X₂ X₃ : GradedObject ℤ (Sheaf T.smallEtaleTopology A)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (T : Scheme.{u}) (X₁ X₂ X₃ : GradedObject ℤ (Sheaf T.smallEtaleTopology A)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (T : Scheme.{u}), HasColimitsOfShape ℤ (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}), HasExactColimitsOfShape ℤ (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology A),
    PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf T.smallEtaleTopology A)).obj F)]
  [∀ (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology A),
    PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf T.smallEtaleTopology A)).flip.obj F)]
  [∀ (T : Scheme.{u}), Abelian.HasFunctorialFlatResolution (Sheaf T.smallEtaleTopology A)]

section PullbackComposition

/-- The composition isomorphism `L(h₁ ≫ h₂)^* ≅ Lh₁^* ∘ Lh₂^*` of derived pullbacks.

Mathematically, this comes from the corresponding composition isomorphism of the
underived pullbacks `(h₁ ≫ h₂)^* ≅ h₁^* ∘ h₂^*` — which follows from uniqueness of left
adjoints, since the pushforwards compose via the pseudofunctoriality
`MorphismProperty.Over.pullback` of base change on the étale sites — together with the
fact that all functors involved are exact, so that the total left derived functor of a
composition is the composition of the total left derived functors. Its formalization is
part of the pending pseudofunctoriality infrastructure for the derived functors (see also
the composition TODO in `WeilConjectures.SixFunctors.LowerShriek.Etale`) and is not yet
available. -/
noncomputable def Etale.leftDerivedUpperStarComp {T S R : Scheme.{u}}
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    Etale.leftDerivedUpperStar A (h₁ ≫ h₂) ≅
      Etale.leftDerivedUpperStar A h₂ ⋙ Etale.leftDerivedUpperStar A h₁ :=
  sorry

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The pullback comparison `θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` of a commutative square
`g' ≫ f = f' ≫ g` of schemes: the canonical natural isomorphism between the two derived
pullbacks along the two composites from `X'` to `Y`, obtained from the composition
isomorphisms of `Etale.leftDerivedUpperStarComp` and the commutativity of the square.
This comparison is the only square-specific categorical ingredient in the construction of
the base-change morphism. -/
noncomputable def Etale.pullbackSquareComparison (sq : CommSq g' f' f g) :
    Etale.leftDerivedUpperStar A g ⋙ Etale.leftDerivedUpperStar A f' ≅
      Etale.leftDerivedUpperStar A f ⋙ Etale.leftDerivedUpperStar A g' :=
  (Etale.leftDerivedUpperStarComp A f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫ Etale.leftDerivedUpperStarComp A g' f

end PullbackComposition

section BaseChangeTransformation

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *unit insertion* step `u_sq` of the base-change morphism: the natural
transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lf'^* ∘ Lg^* ∘ Rf_*` obtained by inserting the
unit of the derived adjunction `Lf'^* ⊣ Rf'_*`. -/
noncomputable def Etale.baseChangeUnitStep :
    Etale.rightDerivedLowerStar A f ⋙ Etale.leftDerivedUpperStar A g ⟶
      (Etale.rightDerivedLowerStar A f ⋙ Etale.leftDerivedUpperStar A g) ⋙
        (Etale.leftDerivedUpperStar A f' ⋙ Etale.rightDerivedLowerStar A f') :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (Etale.rightDerivedLowerStar A f ⋙ Etale.leftDerivedUpperStar A g)
      (Etale.derivedUpperStarLowerStarAdjunction A f').unit

/-- The *square transport* step `s_sq` of the base-change morphism: the natural
transformation obtained by transporting along the pullback comparison `θ_sq` of the
square under `Rf'_*`. -/
noncomputable def Etale.baseChangeSquareStep (sq : CommSq g' f' f g) :
    (Etale.rightDerivedLowerStar A f ⋙ Etale.leftDerivedUpperStar A g) ⋙
        (Etale.leftDerivedUpperStar A f' ⋙ Etale.rightDerivedLowerStar A f') ⟶
      Etale.rightDerivedLowerStar A f ⋙
        ((Etale.leftDerivedUpperStar A f ⋙ Etale.leftDerivedUpperStar A g') ⋙
          Etale.rightDerivedLowerStar A f') :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Etale.rightDerivedLowerStar A f)
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Etale.pullbackSquareComparison A sq).hom
          (Etale.rightDerivedLowerStar A f'))

/-- The *counit contraction* step `c_sq` of the base-change morphism: the natural
transformation `Rf'_* ∘ Lg'^* ∘ Lf^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` obtained by contracting
with the counit of the derived adjunction `Lf^* ⊣ Rf_*`. -/
noncomputable def Etale.baseChangeCounitStep :
    Etale.rightDerivedLowerStar A f ⋙
        ((Etale.leftDerivedUpperStar A f ⋙ Etale.leftDerivedUpperStar A g') ⋙
          Etale.rightDerivedLowerStar A f') ⟶
      Etale.leftDerivedUpperStar A g' ⋙ Etale.rightDerivedLowerStar A f' :=
  Functor.whiskerLeft (Etale.rightDerivedLowerStar A f) (Functor.associator _ _ _).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Etale.derivedUpperStarLowerStarAdjunction A f).counit
      (Etale.leftDerivedUpperStar A g' ⋙ Etale.rightDerivedLowerStar A f') ≫
    (Functor.leftUnitor _).hom

/-- The *derived base-change morphism* `BC_sq : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a
commutative square `g' ≫ f = f' ≫ g` of schemes, assembled as the composite of the unit
insertion, the square transport, and the counit contraction.

Proper base change and smooth base change assert that this single morphism is an
isomorphism under two different sets of geometric hypotheses (see
`WeilConjectures.SixFunctors.ProperBaseChange.Proper` and
`WeilConjectures.SixFunctors.ProperBaseChange.Smooth`); no such hypothesis is built into
the definition. -/
noncomputable def Etale.baseChange (sq : CommSq g' f' f g) :
    Etale.rightDerivedLowerStar A f ⋙ Etale.leftDerivedUpperStar A g ⟶
      Etale.leftDerivedUpperStar A g' ⋙ Etale.rightDerivedLowerStar A f' :=
  Etale.baseChangeUnitStep A ≫ Etale.baseChangeSquareStep A sq ≫ Etale.baseChangeCounitStep A

end BaseChangeTransformation

section CohomologicalBaseChange

/-- The exactness comparison `κ : h^* ∘ H^n ≅ H^n ∘ Lh^*`: since the underived pullback
`h^*` on étale sheaves is exact, applying it to the `n`-th homology sheaf of an object of
the derived category computes the `n`-th homology sheaf of the derived pullback.

Mathematically this is immediate from the exactness of `h^*`
(`Etale.preservesFiniteLimits_upperStar` together with the colimit preservation from the
adjunction): an exact functor commutes with homology, and `Lh^*` is computed by applying
`h^*` levelwise. Its formalization requires the compatibility of
`Etale.leftDerivedUpperStar` with the homology functors of the derived categories, which
is part of the pending derived-functor infrastructure and not yet available. -/
noncomputable def Etale.homologyLeftDerivedUpperStarIso {T S : Scheme.{u}}
    (h : T ⟶ S) (n : ℤ) :
    DerivedCategory.homologyFunctor (Sheaf S.smallEtaleTopology A) n ⋙ Etale.upperStar A h ≅
      Etale.leftDerivedUpperStar A h ⋙
        DerivedCategory.homologyFunctor (Sheaf T.smallEtaleTopology A) n :=
  sorry

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *cohomological base-change morphism* `BC^n_sq` of a commutative square: the
natural transformation `g^* H^n(Rf_* K) ⟶ H^n(Rf'_* Lg'^* K)`, obtained by composing the
exactness comparison `κ` for `g` with the `n`-th homology of the derived base-change
morphism `BC_sq`. -/
noncomputable def Etale.cohomologicalBaseChange (sq : CommSq g' f' f g) (n : ℤ) :
    (Etale.rightDerivedLowerStar A f ⋙
        DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology A) n) ⋙
      Etale.upperStar A g ⟶
      (Etale.leftDerivedUpperStar A g' ⋙ Etale.rightDerivedLowerStar A f') ⋙
        DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology A) n :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Etale.rightDerivedLowerStar A f)
      (Etale.homologyLeftDerivedUpperStarIso A g n).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Etale.baseChange A sq)
      (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology A) n)

end CohomologicalBaseChange

section SheafBaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The higher direct image `R^n f_* : Sh(X_ét) ⥤ Sh(Y_ét)`: the `n`-th homology sheaf of
the derived pushforward of a sheaf placed in degree `0`,
`R^n f_* F := H^n(Rf_*(F[0]))`. -/
noncomputable def Etale.higherDirectImage (n : ℤ) :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙
    Etale.rightDerivedLowerStar A f ⋙
      DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology A) n

/-- The single-degree comparison for the derived pullback: since the underived pullback
`h^*` on étale sheaves is exact, the derived pullback of a sheaf placed in degree `0` is
the pullback of the sheaf placed in degree `0`, `Lh^*(F[0]) ≅ (h^* F)[0]`.

As for `Etale.homologyLeftDerivedUpperStarIso`, this is mathematically immediate from the
exactness of `h^*`; its formalization is part of the pending derived-functor
infrastructure and not yet available. -/
noncomputable def Etale.singleCompLeftDerivedUpperStarIso {T S : Scheme.{u}} (h : T ⟶ S) :
    DerivedCategory.singleFunctor (Sheaf S.smallEtaleTopology A) 0 ⋙
        Etale.leftDerivedUpperStar A h ≅
      Etale.upperStar A h ⋙
        DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology A) 0 :=
  sorry

variable {X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The classical *base-change morphism on sheaves*
`g^* R^n f_* F ⟶ R^n f'_* g'^* F` of a commutative square, obtained from the
cohomological base-change morphism evaluated on sheaves placed in degree `0`. -/
noncomputable def Etale.sheafBaseChange (sq : CommSq g' f' f g) (n : ℤ) :
    Etale.higherDirectImage A f n ⋙ Etale.upperStar A g ⟶
      Etale.upperStar A g' ⋙ Etale.higherDirectImage A f' n :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0)
      (Etale.cohomologicalBaseChange A sq n) ≫
    Functor.whiskerLeft (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0)
      (Functor.associator _ _ _).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Etale.singleCompLeftDerivedUpperStarIso A g').hom
      (Etale.rightDerivedLowerStar A f' ⋙
        DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology A) n) ≫
    (Functor.associator _ _ _).hom

end SheafBaseChange

end AlgebraicGeometry
