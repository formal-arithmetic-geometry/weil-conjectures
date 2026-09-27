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
data which this project has not yet built, stated for the pro-étale functors that it has:

* `Lf^*` is `(AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor`,
* `Rf_*` is `(AlgebraicGeometry.ProEtale.lowerStar A f).rightDerivedFunctor`,
* `Rf_!` is `AlgebraicGeometry.ProEtale.rightDerivedLowerShriek A f`,
* `f^!` is `AlgebraicGeometry.ProEtale.rightDerivedUpperShriek A f`,
* `⊗ᴸ` and `RHom` are the monoidal structure and internal hom of
  `DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)`, which is monoidal closed, so
  `A_X` is `𝟙_ _` and `RHom(K, L)` is `(ihom K).obj L`;
* the two adjunctions are `derivedUpperStarLowerStarAdjunction` and
  `rightDerivedUpperShriekAdjunction`.

The bounded constructible objects of finite Tor amplitude are not available on the
pro-étale site either, so `Dᵇctf(X, A)` is carried as a parameter,
`AlgebraicGeometry.ProEtale.GeometricCoefficients`.

## Main definitions

- `AlgebraicGeometry.ProEtale.GeometricCoefficients`: the coefficient stage, carrying
  `Dᵇctf(X, A)` (blueprint `sk-d-setup`).
- `AlgebraicGeometry.ProEtale.GeometricOperations`: the geometric operation package
  (blueprint `sk-d-six`).
- `AlgebraicGeometry.ProEtale.GeometricOperations.verdierDual`,
  `AlgebraicGeometry.ProEtale.externalProduct`: the derived notions `D_X K` and `M ⊠ N`
  that the package puts in place, spelled out.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- Blueprint `sk-d-setup`: Coefficients and geometric categories.

The blueprint fixes `q = pʳ`, an algebraic closure `k` of `𝐅_q`, a prime `ℓ ≠ p`, a finite
extension `E/𝐐_ℓ` with uniformiser `ϖ`, and the finite coefficient ring `A = 𝒪_E/ϖⁿ`; a
*geometric scheme* is a scheme separated and of finite type over `s = Spec k`, and
`D(X, A)` is the derived category of sheaves of `A`-modules on `X_proét`. Here the
coefficients are an arbitrary Grothendieck abelian monoidal closed category `A`, so that
`D(X, A)` is `DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)`; the intended
instantiation is `A = ModuleCat (𝒪_E/ϖⁿ)`.

Constructibility on the pro-étale site is not available in this project, so the remaining
content of the subsection — the subcategory `Dᵇctf(X, A) ⊆ D(X, A)` of bounded
constructible objects of finite Tor amplitude — is carried here as data: an object
property on each `D(X, A)`, triangulated and stable under `Lf^*` and `Rf_!`. -/
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

/-- Blueprint `sk-d-six`: The geometric operation package.

A package over the base `s` consists of the six operations together with their units,
counits, composition identities, projection formulas, `!`-base change, open-immersion
purity, the closed-immersion unit `1 ≃ Ri^! Ri_*`, the identification `Rf_* = Rf_!` for
proper `f`, the dualizing complex `ω_X = a_X^! A` with its composition
`f^! ω_Y ≃ ω_X`, and biduality `K ≃ D_X D_X K` on `Dᵇctf`.

The functors and the two adjunctions are *not* fields: they are the pro-étale functors of
`WeilConjectures.SixFunctors.ProEtale`, listed in the module docstring. The fields are the
comparison data of the blueprint's package clause, which this project has not built. -/
structure GeometricOperations (s : Scheme.{u}) extends GeometricCoefficients A where
  /-- the dualizing complex `ω_X = a_X^! A` of a geometric scheme `a : X ⟶ s`. -/
  dualizing {X : Scheme.{u}} (a : X ⟶ s) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)
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
  /-- `!`-base change along a Cartesian square: `Lg^* Rf_! ≃ Rf'_! Lg'^*`. -/
  baseChange {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (_sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] :
    rightDerivedLowerShriek A f ⋙ (upperStar A g).leftDerivedFunctor ≅
      (upperStar A g').leftDerivedFunctor ⋙ rightDerivedLowerShriek A f'
  /-- the projection formula: `Rf_! K ⊗ᴸ L ≃ Rf_! (K ⊗ᴸ Lf^* L)`. -/
  projectionFormula {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
      (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (rightDerivedLowerShriek A f).obj K ⊗ L ≅
      (rightDerivedLowerShriek A f).obj (K ⊗ ((upperStar A f).leftDerivedFunctor).obj L)
  /-- open-immersion purity: `j^! ≃ Lj^*` for an open immersion `j`. -/
  openPurity {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [HasCompactification j] :
    rightDerivedUpperShriek A j ≅ (upperStar A j).leftDerivedFunctor
  /-- the closed-immersion unit: `1 ≃ Ri^! Ri_*` for a closed immersion `i`. -/
  closedUnit {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i] :
    𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A)) ≅
      (lowerStar A i).rightDerivedFunctor ⋙ rightDerivedUpperShriek A i
  /-- biduality on `Dᵇctf`: the evaluation-adjoint map `K ⟶ D_X D_X K` is invertible. -/
  biduality {X : Scheme.{u}} (a : X ⟶ s)
      (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (hK : ctf X K) :
    Nonempty (K ≅ (ihom ((ihom K).obj (dualizing a))).obj (dualizing a))

variable {A}

/-- The Verdier dual `D_X K = RHom(K, ω_X)` attached to a geometric operation package
(part of blueprint `sk-d-six`). -/
noncomputable def GeometricOperations.verdierDual {s : Scheme.{u}}
    (G : GeometricOperations A s) {X : Scheme.{u}} (a : X ⟶ s)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (ihom K).obj (G.dualizing a)

variable (A)

/-- The external product `M ⊠ N = p_X^* M ⊗ᴸ p_Y^* N` on the product `X ×_s Y`
(part of blueprint `sk-d-six`). -/
noncomputable def externalProduct {s X Y : Scheme.{u}} (aX : X ⟶ s) (aY : Y ⟶ s)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback aX aY)) A) :=
  ((upperStar A (pullback.fst aX aY)).leftDerivedFunctor).obj M ⊗
    ((upperStar A (pullback.snd aX aY)).leftDerivedFunctor).obj N

end AlgebraicGeometry.ProEtale
