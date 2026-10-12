/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The tensor-formula map `Lf^* K ⊗ᴸ ω_f ⟶ Rf^! K`

Let `f : X ⟶ Y` admit a compactification, so that `Rf_! ⊣ Rf^!`, and assume that the
projection map `PF : Rf_! M ⊗ᴸ K ⟶ Rf_!(M ⊗ᴸ Lf^* K)` is an isomorphism. The *tensor-formula
map* is the mate of the projection formula with the counit of `Rf_! ⊣ Rf^!`: for
`K : D(Y_ét)` it is the transpose along `Rf_! ⊣ Rf^!` of

`Rf_!(Lf^* K ⊗ᴸ ω_f) ≅ Rf_!(ω_f ⊗ᴸ Lf^* K) ≅ Rf_! ω_f ⊗ᴸ K ⟶ Λ_Y ⊗ᴸ K ≅ K`,

the symmetry of `- ⊗ᴸ -`, the inverse projection formula at `(ω_f, K)`, the counit
`Rf_! Rf^! Λ_Y ⟶ Λ_Y` tensored with `K`, and the left unitor. Here `ω_f = Rf^! Λ_Y` is the
dualizing complex. Cohomological smoothness (blueprint `def-pur-co-smoothness`,
`thm-pur-cohomological-smoothness`) asserts that this map is an isomorphism for smooth `f` on
`D^b_{ctf}`.

## Implementation notes

The projection map of the library, like the blueprint's `PF_{f,M,K}` of
`def-exchange-projection`, has the object on `X` as its *left* factor; the blueprint writes the
tensor formula with `Lf^* K` on the left. The two are related by the symmetry
`AlgebraicGeometry.Etale.derivedTensorBraiding` of `- ⊗ᴸ -`.

Everything is stated for a general coefficient category `A`, so that the specialisation to
`ModuleCat Λ` never compares two monoidal structures on `D(X_ét)` (see the implementation
notes of `WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`).

## Main definitions

- `AlgebraicGeometry.Etale.dualizingComplexTensorCounit`: the natural map
  `Rf_!(Lf^* K ⊗ᴸ ω_f) ⟶ K`.
- `AlgebraicGeometry.Etale.dualizingComplexTensorMap`: the tensor-formula map
  `Lf^* K ⊗ᴸ ω_f ⟶ Rf^! K`, natural in `K`.

## Main statements

- `AlgebraicGeometry.Etale.dualizingComplexTensorMap_app`: the component at `K` is the
  transpose of `AlgebraicGeometry.Etale.dualizingComplexTensorCounit`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

namespace Etale

variable (X : Scheme.{u}) in
/-- The symmetry `K ⊗ᴸ M ≅ M ⊗ᴸ K` of the derived tensor product, natural in both variables: the
braiding `AlgebraicGeometry.Etale.derivedBraidedCategory` of `D(X_ét)`. Its existence is
`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`. -/
noncomputable def derivedTensorBraiding : derivedTensor A X ≅ (derivedTensor A X).flip :=
  letI := derivedBraidedCategory A X
  BraidedCategory.curriedBraidingNatIso _

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]
  [IsIso (projectionMap A f)]

/-- The natural map `Rf_!(Lf^* K ⊗ᴸ ω_f) ⟶ K`: the symmetry
`Lf^* K ⊗ᴸ ω_f ≅ ω_f ⊗ᴸ Lf^* K`, the inverse of the projection formula
`Rf_! ω_f ⊗ᴸ K ≅ Rf_!(ω_f ⊗ᴸ Lf^* K)` at `(ω_f, K)`, the counit `Rf_! Rf^! Λ_Y ⟶ Λ_Y` of
`Rf_! ⊣ Rf^!` tensored with `K`, and the left unitor `Λ_Y ⊗ᴸ K ≅ K`. -/
noncomputable def dualizingComplexTensorCounit :
    L((f)^*[A]) ⋙ (derivedTensor A X).flip.obj (dualizingComplex A f) ⋙ R(f)_![A] ⟶ 𝟭 _ :=
  Functor.whiskerLeft L((f)^*[A])
      (Functor.whiskerRight ((derivedTensorBraiding A X).inv.app (dualizingComplex A f))
        R(f)_![A]) ≫
    (show L((f)^*[A]) ⋙ (derivedTensor A X).obj (dualizingComplex A f) ⋙ R(f)_![A] ⟶
        (derivedTensor A Y).obj ((R(f)_![A]).obj (dualizingComplex A f)) from
      (inv (projectionMap A f)).app (dualizingComplex A f)) ≫
    (derivedTensor A Y).map ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _)) ≫
      (derivedTensorLeftUnitorNatIso A Y).hom

lemma dualizingComplexTensorCounit_app
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (dualizingComplexTensorCounit A f).app K =
      (R(f)_![A]).map (((derivedTensorBraiding A X).inv.app (dualizingComplex A f)).app
          ((L((f)^*[A])).obj K)) ≫
        ((inv (projectionMap A f)).app (dualizingComplex A f)).app K ≫
        ((derivedTensor A Y).map
          ((rightDerivedUpperShriekAdjunction A f).counit.app (𝟙_ _))).app K ≫
        (derivedTensorLeftUnitor A Y K).hom :=
  rfl

/-- The *tensor-formula map* `φ_K : Lf^* K ⊗ᴸ ω_f ⟶ Rf^! K`, natural in `K : D(Y_ét)`: the
mate of the projection formula with the counit of `Rf_! ⊣ Rf^!`, that is, the transpose along
`Rf_! ⊣ Rf^!` of `AlgebraicGeometry.Etale.dualizingComplexTensorCounit`. Here
`ω_f = Rf^! Λ_Y` is `AlgebraicGeometry.Etale.dualizingComplex`.

This is the canonical map of blueprint `def-pur-co-smoothness` (2) and
`thm-pur-cohomological-smoothness` (1). -/
noncomputable def dualizingComplexTensorMap :
    L((f)^*[A]) ⋙ (derivedTensor A X).flip.obj (dualizingComplex A f) ⟶ R(f)^![A] :=
  Functor.whiskerLeft (L((f)^*[A]) ⋙ (derivedTensor A X).flip.obj (dualizingComplex A f))
      (rightDerivedUpperShriekAdjunction A f).unit ≫
    Functor.whiskerRight (dualizingComplexTensorCounit A f) R(f)^![A]

/-- The component of the tensor-formula map at `K` is the transpose along `Rf_! ⊣ Rf^!` of
`Rf_!(Lf^* K ⊗ᴸ ω_f) ⟶ K`. -/
lemma dualizingComplexTensorMap_app (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (dualizingComplexTensorMap A f).app K =
      (rightDerivedUpperShriekAdjunction A f).homEquiv _ _
        ((dualizingComplexTensorCounit A f).app K) := by
  simp [dualizingComplexTensorMap, Adjunction.homEquiv_unit]

end Etale

end AlgebraicGeometry
