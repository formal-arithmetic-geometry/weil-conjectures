/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Shift.ShiftedHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Cohomology classes in `D(X_ét)`: cup products and direct images

A class of degree `i` of an object `M` of `D(X_ét)` is a morphism `Λ_X ⟶ M[i]`, an element of
`CategoryTheory.ShiftedHom Λ_X M i`. For the structure morphism `a` of a scheme over `Spec k`,
the classes of `Ra_! K` and `Ra_* K` are `H^i_c(X, K)` and `H^i(X, K)`. This file gives the
operations on classes that the Poincaré duality chapter uses, for a general `R`-linear
coefficient category `A`:

* the *cup product* `H^i(C) × H^j(D) ⟶ H^{i+j}(E)` along a morphism `C ⊗ᴸ D ⟶ E`;
* the identification `H^n(X, M) ≅ H^n(Y, Ra_* M)` of classes on `X` with classes of the direct
  image along `a : X ⟶ Y`, by the adjunction `La^* ⊣ Ra_*`;
* for a proper `a`, the identification of the classes of `Ra_* M` and of `Ra_! M`.

## Main definitions

- `AlgebraicGeometry.Etale.shiftedHomCupProduct`,
  `AlgebraicGeometry.Etale.cohomologyClassesCupProduct`: the cup product along a morphism
  `C ⊗ᴸ D ⟶ E`, of morphisms `P ⟶ C[i]`, `Q ⟶ D[j]` and of classes.
- `AlgebraicGeometry.Etale.unitCupProduct`: the cup product `H^i(X) × H^j(X) ⟶ H^{i+j}(X)` of
  classes of the unit `Λ_X`.
- `AlgebraicGeometry.Etale.lowerStarClassEquiv`: `H^n(X, M) ≃ H^n(Y, Ra_* M)`.
- `AlgebraicGeometry.Etale.lowerStarClassEquivLowerShriek`: `H^n(Y, Ra_* M) ≃ H^n(Y, Ra_! M)`
  for a proper `a`.
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
  (R : Type*) [CommRing R] [Linear R A] [MonoidalLinear R A]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

namespace Etale

section CupProduct

variable {X : Scheme.{u}}

variable {A} in
/-- The *cup product* of morphisms `x : P ⟶ C[i]` and `y : Q ⟶ D[j]` along a morphism
`φ : C ⊗ᴸ D ⟶ E`: the morphism
```
             x ⊗ᴸ y                        ≅                     φ[i + j]
P ⊗ᴸ Q ─────────▶ C[i] ⊗ᴸ D[j] ─────────▶ (C ⊗ᴸ D)[i + j] ─────────▶ E[i + j]
```
the shifts being moved out with `AlgebraicGeometry.Etale.derivedTensorShiftIso`. It is
`R`-bilinear, being built from composition and the `R`-linear functors `- ⊗ᴸ Q` and
`C[i] ⊗ᴸ -`. -/
noncomputable def shiftedHomCupProduct {P Q C D E : 𝐃(X, A)}
    (φ : ((derivedTensor A X).obj C).obj D ⟶ E) (i j : ℤ) :
    (P ⟶ C⟦i⟧) →ₗ[R] (Q ⟶ D⟦j⟧) →ₗ[R] (((derivedTensor A X).obj P).obj Q ⟶ E⟦i + j⟧) :=
  (Linear.comp _ _ _).compl₁₂ (((derivedTensor A X).flip.obj Q).mapLinearMap R)
    (Linear.rightComp R _ ((derivedTensorShiftIso A C D i j).hom ≫ φ⟦i + j⟧') ∘ₗ
      ((derivedTensor A X).obj (C⟦i⟧)).mapLinearMap R)

variable {A} in
/-- The *cup product* of classes `x : Λ_X ⟶ C[i]` and `y : Λ_X ⟶ D[j]` along a morphism
`φ : C ⊗ᴸ D ⟶ E`: the class of degree `i + j` of `E`
```
        λ⁻¹                  x ⊗ᴸ y                        ≅                     φ[i + j]
Λ_X ─────────▶ Λ_X ⊗ᴸ Λ_X ─────────▶ C[i] ⊗ᴸ D[j] ─────────▶ (C ⊗ᴸ D)[i + j] ─────────▶ E[i + j]
```
the diagonal `Λ_X ≅ Λ_X ⊗ᴸ Λ_X` being the inverse of the left unitor
(`AlgebraicGeometry.Etale.shiftedHomCupProduct` followed by the diagonal). -/
noncomputable def cohomologyClassesCupProduct {C D E : 𝐃(X, A)}
    (φ : ((derivedTensor A X).obj C).obj D ⟶ E) (i j : ℤ) :
    ShiftedHom (𝟙_ _) C i →ₗ[R] ShiftedHom (𝟙_ _) D j →ₗ[R] ShiftedHom (𝟙_ _) E (i + j) :=
  (shiftedHomCupProduct R φ i j).compr₂
    (Linear.leftComp R _ (derivedTensorLeftUnitor A X (𝟙_ _)).inv)

variable (X)

/-- The *cup product* `H^i(X) × H^j(X) ⟶ H^{i+j}(X)` of classes `Λ_X ⟶ Λ_X[i]` and
`Λ_X ⟶ Λ_X[j]` of the unit: the cup product
`AlgebraicGeometry.Etale.cohomologyClassesCupProduct` along the left unitor
`Λ_X ⊗ᴸ Λ_X ≅ Λ_X`, as for the cup product with supports
`AlgebraicGeometry.Etale.cupWithSupports`. -/
noncomputable def unitCupProduct (i j : ℤ) :
    ShiftedHom (𝟙_ _) (𝟙_ 𝐃(X, A)) i →ₗ[R] ShiftedHom (𝟙_ _) (𝟙_ 𝐃(X, A)) j →ₗ[R]
      ShiftedHom (𝟙_ _) (𝟙_ 𝐃(X, A)) (i + j) :=
  cohomologyClassesCupProduct R (derivedTensorLeftUnitor A X (𝟙_ _)).hom i j

end CupProduct

section DirectImage

variable {X Y : Scheme.{u}} (a : X ⟶ Y)

/-- Classes on `X` are classes on `Y` of the direct image: for `a : X ⟶ Y`, an identification
`e : La^* Λ_Y ≅ Λ_X` and `M ∈ D(X_ét)`, the classes `Λ_X ⟶ M[n]` correspond to the classes
`Λ_Y ⟶ (Ra_* M)[n]`,
```
                  e⁻¹                adjunction                     ≅
(Λ_X ⟶ M[n]) ─────────▶ (La^* Λ_Y ⟶ M[n]) ─────────▶ (Λ_Y ⟶ Ra_*(M[n])) ─────▶ (Λ_Y ⟶ (Ra_* M)[n])
```
through `e`, the adjunction `La^* ⊣ Ra_*` and `Ra_*(M[n]) ≅ (Ra_* M)[n]`. For
`a : X ⟶ Spec k` this identifies `Hom(Λ_X, M[n])` with `H^n(X, M)`. -/
noncomputable def lowerStarClassEquiv (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) (M : 𝐃(X, A))
    (n : ℤ) : ShiftedHom (𝟙_ _) M n ≃ₗ[R] ShiftedHom (𝟙_ _) ((R((a)_*[A])).obj M) n where
  toFun f := (derivedUpperStarLowerStarAdjunction A a).homEquiv (𝟙_ _) _ (e.hom ≫ f) ≫
    ((R((a)_*[A])).commShiftIso n).hom.app M
  invFun g := e.inv ≫ ((derivedUpperStarLowerStarAdjunction A a).homEquiv (𝟙_ _) _).symm
    (g ≫ ((R((a)_*[A])).commShiftIso n).inv.app M)
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := by simp [Adjunction.homEquiv_unit]
  map_smul' r f := by simp [Adjunction.homEquiv_unit]

variable [HasSmallSiteSheafify A] [HasCompactification a] [IsProper a]

/-- For a proper `a`, the classes of degree `n` of `Ra_* M` and of `Ra_! M` agree, through
`Ra_* ≅ Ra_!` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`):
```
                         (Ra_* M ≅ Ra_! M)[n]
(Λ_Y ⟶ (Ra_* M)[n]) ─────────────────────────▶ (Λ_Y ⟶ (Ra_! M)[n])
```
Over `Y = Spec k` this is `H^n(X, M) ≅ H^n_c(X, M)`. -/
noncomputable def lowerStarClassEquivLowerShriek (M : 𝐃(X, A)) (n : ℤ) :
    ShiftedHom (𝟙_ _) ((R((a)_*[A])).obj M) n ≃ₗ[R] ShiftedHom (𝟙_ _) ((R(a)_![A]).obj M) n :=
  Linear.homCongr R (Iso.refl _)
    ((shiftFunctor _ n).mapIso ((rightDerivedLowerShriekIsoRightDerivedLowerStar A a).app M).symm)

end DirectImage

end Etale

end AlgebraicGeometry
