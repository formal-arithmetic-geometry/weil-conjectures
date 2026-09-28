/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek

/-!
# Coefficients and the geometric operation package of the trace formula

The Lefschetz-Verdier trace formula is developed in the blueprint over an *axiomatised*
package of the six operations: the sketch fixes the data of the functors together with
their adjunctions, composition isomorphisms, base change, the projection formula and the
identification `Rf_* = Rf_!` for proper `f`, and quotes their geometric realisation from
the six operations chapter.

This file formalises that specification. The four functors themselves are **not** redefined:
the fields of `AlgebraicGeometry.ProEtale.GeometricOperations` are exactly the comparison
data which this project has not yet built, stated for the pro-étale functors that it has.

## Main definitions

- `AlgebraicGeometry.ProEtale.GeometricCoefficients`: the coefficient stage, carrying
  `Dᵇctf(X, A)`.
- `AlgebraicGeometry.ProEtale.verdierDual`: the Verdier dual `D_X K = RHom(K, ω_X)`.
- `AlgebraicGeometry.ProEtale.GeometricOperations`: the geometric operation package.
- `AlgebraicGeometry.ProEtale.GeometricOperations.upperShriekId`: the identity isomorphism
  `(𝟙 X)^! ≃ 𝟭`, conjugate to the field `lowerShriekId`.

## Implementation notes

The blueprint's `Λ`-valued pro-étale six operations are rendered by the functors this
project has:

* `Lf^*` is `(AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor`,
* `Rf_*` is `(AlgebraicGeometry.ProEtale.lowerStar A f).rightDerivedFunctor`,
* `Rf_!` is `AlgebraicGeometry.ProEtale.rightDerivedLowerShriek A f`,
* `f^!` is `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A f`,
* `⊗ᴸ` and `RHom` are the monoidal structure and internal hom of
  `DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)`, which is monoidal closed, so
  `A_X` is `𝟙_ _` and `RHom(K, L)` is `(ihom K).obj L`;
* the two adjunctions are `derivedUpperStarLowerStarAdjunction` and
  `rightDerivedUpperShriekAdjunction`.

The coefficients are an arbitrary Grothendieck abelian monoidal closed category `A` rather
than the blueprint's finite ring `𝒪_E/ϖⁿ`; the intended instantiation is
`A = ModuleCat (𝒪_E/ϖⁿ)`. Constructibility on the pro-étale site is not available, so the
subcategory `Dᵇctf(X, A) ⊆ D(X, A)` of bounded constructible objects of finite Tor
amplitude is carried as data by `GeometricCoefficients`.

Two limitations of the package as stated. The comparison isomorphisms `properComparison`
and `openPurity` are *not* pinned to the canonical natural transformations `Rf_! ⟶ Rf_*`
and `f^! ⟶ Lf^*`, because this project constructs neither at the level of derived
categories; and apart from the unit axioms of `lowerShriekId` and `upperStarUnit`, no
coherence between the comparison isomorphisms themselves — for instance between
`baseChange` and `lowerShriekComp` — is imposed. Both are part of the six operations
chapter rather than of this block.

The dualizing complex `ω_X = a_X^! A` *is* constructible when `a_X` admits a
compactification, but it is needed for morphisms whose compactification is not in scope, so
it is carried as a field and tied to its construction by `dualizingIso`; `dualizingBase`
normalises `ω_s` to `A_s`, which is what makes `End (A_s)` the coefficient ring in which
integrals and local terms take their values.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Coefficients and geometric categories: a choice, for every scheme `X`, of the
subcategory `Dᵇctf(X, A) ⊆ D(X, A)` of bounded constructible objects of finite Tor
amplitude, triangulated and stable under `Lf^*` and `Rf_!`
(blueprint: `sk-d-setup`). -/
structure GeometricCoefficients where
  /-- `Dᵇctf(X, A)`, the bounded constructible objects of finite Tor amplitude. -/
  ctf (X : Scheme.{u}) : ObjectProperty (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
  /-- `Dᵇctf(X, A)` is a triangulated subcategory of `D(X, A)`. -/
  isTriangulated_ctf (X : Scheme.{u}) : (ctf X).IsTriangulated
  /-- `Dᵇctf` is stable under `Lf^*`. -/
  ctf_upperStar {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) (hK : ctf Y K) :
    ctf X (((upperStar A f).leftDerivedFunctor).obj K)
  /-- `Dᵇctf` is stable under `Rf_!`. -/
  ctf_lowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : ctf X K) :
    ctf Y ((rightDerivedLowerShriek A f).obj K)

instance (G : GeometricCoefficients A) (X : Scheme.{u}) : (G.ctf X).IsTriangulated :=
  G.isTriangulated_ctf X

section VerdierDual

variable {A}

/-- The Verdier dual `D_X K = RHom(K, ω)` of `K` with respect to a dualizing complex `ω`
(part of blueprint `sk-d-six`). -/
noncomputable def verdierDual {X : Scheme.{u}}
    (ω K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (ihom K).obj ω

end VerdierDual

/-- The geometric operation package over a base `s`: the comparison data of the six
operations that the blueprint fixes, namely the dualizing complex `ω_X = a_X^! A` with its
composition `f^! ω_Y ≃ ω_X`, the identification `Rf_* = Rf_!` for proper `f`, composition
of exceptional direct images, `!`-base change, the projection formula, open-immersion
purity, the closed-immersion unit `1 ≃ Ri^! Ri_*`, the pullback `Lf^* A_Y ≃ A_X` of the
constant sheaf, and biduality `K ≃ D_X D_X K` on `Dᵇctf`. The identity isomorphism
`R(𝟙 X)_! ≃ 𝟭` and the pullback of the constant sheaf are tied to `lowerShriekComp` and to
`leftDerivedUpperStarId` by unit axioms.

The functors and the two adjunctions are *not* fields: they are the pro-étale functors of
`WeilConjectures.SixFunctors.ProEtale`, listed in the module docstring
(blueprint: `sk-d-six`). -/
structure GeometricOperations (s : Scheme.{u}) extends GeometricCoefficients A where
  /-- the dualizing complex `ω_X = a_X^! A` of a geometric scheme `a : X ⟶ s`. -/
  dualizing {X : Scheme.{u}} (a : X ⟶ s) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)
  /-- `ω_X` is `a_X^! A` whenever `a_X` admits a compactification. -/
  dualizingIso {X : Scheme.{u}} (a : X ⟶ s) [HasCompactification a] :
    dualizing a ≅ (rightDerivedUpperShriek A a).obj (𝟙_ _)
  /-- the normalisation `ω_s ≃ A_s` of the dualizing complex of the base. -/
  dualizingBase :
    dualizing (𝟙 s) ≅ 𝟙_ (DerivedCategory (Sheaf (Scheme.ProEt.topology s) A))
  /-- dualizing composition: `f^! ω_Y ≃ ω_X`. -/
  dualizingComp {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Y ⟶ s) [HasCompactification f] :
    (rightDerivedUpperShriek A f).obj (dualizing a) ≅ dualizing (f ≫ a)
  /-- `Rf_* = Rf_!` for proper `f`. -/
  properComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [IsProper f] :
    rightDerivedLowerShriek A f ≅ (lowerStar A f).rightDerivedFunctor
  /-- composition of the exceptional direct images: `Rf_! ⋙ Rg_! ≃ R(f ≫ g)_!`. -/
  lowerShriekComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f]
      [HasCompactification g] [HasCompactification (f ≫ g)] :
    rightDerivedLowerShriek A f ⋙ rightDerivedLowerShriek A g ≅
      rightDerivedLowerShriek A (f ≫ g)
  /-- the identity isomorphism of the exceptional direct image: `R(𝟙 X)_! ≃ 𝟭`. -/
  lowerShriekId (X : Scheme.{u}) :
    rightDerivedLowerShriek A (𝟙 X) ≅ 𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
  /-- left unit axiom: `lowerShriekComp (𝟙 X) f` is `lowerShriekId X` whiskered by `Rf_!`. -/
  lowerShriekComp_id_left {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
      [HasCompactification (𝟙 X ≫ f)] :
    lowerShriekComp (𝟙 X) f = Functor.isoWhiskerRight (lowerShriekId X) _ ≪≫
      Functor.leftUnitor _ ≪≫ rightDerivedLowerShriekCongr A (Category.id_comp f).symm
  /-- right unit axiom: `lowerShriekComp f (𝟙 Y)` is `lowerShriekId Y` whiskered by
  `Rf_!`. -/
  lowerShriekComp_id_right {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
      [HasCompactification (f ≫ 𝟙 Y)] :
    lowerShriekComp f (𝟙 Y) = Functor.isoWhiskerLeft _ (lowerShriekId Y) ≪≫
      Functor.rightUnitor _ ≪≫ rightDerivedLowerShriekCongr A (Category.comp_id f).symm
  /-- `!`-base change along a Cartesian square: `Lg^* Rf_! ≃ Rf'_! Lg'^*`, for

  ```
     X' ──g'──→ X
     │          │
   f'│          │f
     ↓          ↓
     Y' ──g───→ Y
  ```
  -/
  baseChange {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] :
    rightDerivedLowerShriek A f ⋙ (upperStar A g).leftDerivedFunctor ≅
      (upperStar A g').leftDerivedFunctor ⋙ rightDerivedLowerShriek A f'
  /-- the projection formula `Rf_! K ⊗ᴸ L ≃ Rf_! (K ⊗ᴸ Lf^* L)`, as an isomorphism of
  bifunctors `D(X, A) × D(Y, A) ⥤ D(Y, A)`. -/
  projectionFormula {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :
    (rightDerivedLowerShriek A f).prod
          (𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))) ⋙
        MonoidalCategory.tensor (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) ≅
      (𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))).prod
          ((upperStar A f).leftDerivedFunctor) ⋙
        MonoidalCategory.tensor (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) ⋙
          rightDerivedLowerShriek A f
  /-- open-immersion purity: `j^! ≃ Lj^*` for an open immersion `j`. -/
  openPurity {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j] :
    rightDerivedUpperShriek A j ≅ (upperStar A j).leftDerivedFunctor
  /-- the closed-immersion unit: `1 ≃ Ri^! Ri_*` for a closed immersion `i`. -/
  closedUnit {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i] :
    𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) ≅
      (lowerStar A i).rightDerivedFunctor ⋙ rightDerivedUpperShriek A i
  /-- the pullback of the constant sheaf: `Lf^* A_Y ≃ A_X`. -/
  upperStarUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((upperStar A f).leftDerivedFunctor).obj (𝟙_ _) ≅ 𝟙_ _
  /-- for `f = 𝟙 X`, `upperStarUnit` is the identity isomorphism `L(𝟙 X)^* ≃ 𝟭`. -/
  upperStarUnit_id (X : Scheme.{u}) :
    upperStarUnit (𝟙 X) = (leftDerivedUpperStarId A X).app (𝟙_ _)
  /-- the evaluation-adjoint map `K ⟶ D_X D_X K`. -/
  bidualityMap {X : Scheme.{u}} (a : X ⟶ s)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    K ⟶ verdierDual (dualizing a) (verdierDual (dualizing a) K)
  /-- biduality on `Dᵇctf`: the evaluation-adjoint map `K ⟶ D_X D_X K` is invertible. -/
  isIso_bidualityMap {X : Scheme.{u}} (a : X ⟶ s)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : ctf X K) :
    IsIso (bidualityMap a K)

variable {A}

/-- The Verdier dual `D_X K = RHom(K, ω_X)` taken with respect to the dualizing complex of
a geometric operation package (part of blueprint `sk-d-six`). -/
noncomputable def GeometricOperations.verdierDual {s : Scheme.{u}}
    (G : GeometricOperations A s) {X : Scheme.{u}} (a : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  _root_.AlgebraicGeometry.ProEtale.verdierDual (G.dualizing a) K

/-- The identity isomorphism `(𝟙 X)^! ≃ 𝟭` of the exceptional inverse image: the conjugate
of the field `lowerShriekId : R(𝟙 X)_! ≃ 𝟭` along the adjunctions `R(𝟙 X)_! ⊣ (𝟙 X)^!` and
`𝟭 ⊣ 𝟭`. -/
noncomputable def GeometricOperations.upperShriekId {s : Scheme.{u}}
    (G : GeometricOperations A s) (X : Scheme.{u}) :
    rightDerivedUpperShriek A (𝟙 X) ≅ 𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  (conjugateIsoEquiv Adjunction.id (rightDerivedUpperShriekAdjunction A (𝟙 X))
    (G.lowerShriekId X)).symm

end AlgebraicGeometry.ProEtale
