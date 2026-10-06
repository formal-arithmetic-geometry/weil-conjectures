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

- `AlgebraicGeometry.Etale.cupProduct`, `AlgebraicGeometry.Etale.shiftedHomCupProduct`: the cup
  product along a morphism `C ⊗ᴸ D ⟶ E`, of morphisms `P ⟶ C[i]`, `Q ⟶ D[j]` and of classes.
- `AlgebraicGeometry.Etale.unitCupProduct`: the cup product `H^i(X) × H^j(X) ⟶ H^k(X)`,
  `i + j = k`, of classes of the unit `Λ_X`.
- `AlgebraicGeometry.Etale.lowerStarClassEquiv`: `H^n(X, M) ≃ H^n(Y, Ra_* M)`.
- `AlgebraicGeometry.Etale.lowerStarClassEquivLowerShriek`: `H^n(Y, Ra_* M) ≃ H^n(Y, Ra_! M)`
  for a proper `a`.

## Implementation notes

As for `CategoryTheory.ShiftedHom.comp`, the cup products take the target degree `k` as an
explicit argument together with a proof of `i + j = k`, so that no cast is needed when the
degree of the product is only propositionally `i + j`.
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
`φ : C ⊗ᴸ D ⟶ E`, in degree `k = i + j`: the morphism
```
             x ⊗ᴸ y                        ≅                   φ[k]
P ⊗ᴸ Q ─────────▶ C[i] ⊗ᴸ D[j] ─────────▶ (C ⊗ᴸ D)[k] ─────────▶ E[k]
```
the shifts being moved out with `AlgebraicGeometry.Etale.derivedTensorShiftIso'`. It is
`R`-bilinear, being built from composition and the `R`-linear functors `- ⊗ᴸ Q` and
`C[i] ⊗ᴸ -`. -/
noncomputable def cupProduct {P Q C D E : 𝐃(X, A)}
    (φ : ((derivedTensor A X).obj C).obj D ⟶ E) (i j k : ℤ) (h : i + j = k) :
    (P ⟶ C⟦i⟧) →ₗ[R] (Q ⟶ D⟦j⟧) →ₗ[R] (((derivedTensor A X).obj P).obj Q ⟶ E⟦k⟧) :=
  (Linear.comp _ _ _).compl₁₂ (((derivedTensor A X).flip.obj Q).mapLinearMap R)
    (Linear.rightComp R _ ((derivedTensorShiftIso' A C D i j k h).hom ≫ φ⟦k⟧') ∘ₗ
      ((derivedTensor A X).obj (C⟦i⟧)).mapLinearMap R)

variable {A R} in
lemma cupProduct_apply {P Q C D E : 𝐃(X, A)} (φ : ((derivedTensor A X).obj C).obj D ⟶ E)
    (i j k : ℤ) (h : i + j = k) (x : P ⟶ C⟦i⟧) (y : Q ⟶ D⟦j⟧) :
    cupProduct R φ i j k h x y = ((derivedTensor A X).flip.obj Q).map x ≫
      ((derivedTensor A X).obj (C⟦i⟧)).map y ≫ (derivedTensorShiftIso' A C D i j k h).hom ≫
        φ⟦k⟧' :=
  rfl

variable {A} in
/-- The *cup product* of classes `x : Λ_X ⟶ C[i]` and `y : Λ_X ⟶ D[j]` along a morphism
`φ : C ⊗ᴸ D ⟶ E`: the class of degree `k = i + j` of `E`
```
        λ⁻¹                  x ⊗ᴸ y                        ≅                   φ[k]
Λ_X ─────────▶ Λ_X ⊗ᴸ Λ_X ─────────▶ C[i] ⊗ᴸ D[j] ─────────▶ (C ⊗ᴸ D)[k] ─────────▶ E[k]
```
the diagonal `Λ_X ≅ Λ_X ⊗ᴸ Λ_X` being the inverse of the left unitor
(`AlgebraicGeometry.Etale.cupProduct` followed by the diagonal). -/
noncomputable def shiftedHomCupProduct {C D E : 𝐃(X, A)}
    (φ : ((derivedTensor A X).obj C).obj D ⟶ E) (i j k : ℤ) (h : i + j = k) :
    ShiftedHom (𝟙_ _) C i →ₗ[R] ShiftedHom (𝟙_ _) D j →ₗ[R] ShiftedHom (𝟙_ _) E k :=
  (cupProduct R φ i j k h).compr₂
    (Linear.leftComp R _ (derivedTensorLeftUnitor A X (𝟙_ _)).inv)

variable {A R} in
lemma shiftedHomCupProduct_apply {C D E : 𝐃(X, A)} (φ : ((derivedTensor A X).obj C).obj D ⟶ E)
    (i j k : ℤ) (h : i + j = k) (x : ShiftedHom (𝟙_ _) C i) (y : ShiftedHom (𝟙_ _) D j) :
    shiftedHomCupProduct R φ i j k h x y =
      (derivedTensorLeftUnitor A X (𝟙_ _)).inv ≫ cupProduct R φ i j k h x y :=
  rfl

variable (X)

/-- The *cup product* `H^i(X) × H^j(X) ⟶ H^k(X)`, `i + j = k`, of classes `Λ_X ⟶ Λ_X[i]` and
`Λ_X ⟶ Λ_X[j]` of the unit: the cup product `AlgebraicGeometry.Etale.shiftedHomCupProduct`
along the left unitor `Λ_X ⊗ᴸ Λ_X ≅ Λ_X`, as for the cup product with supports
`AlgebraicGeometry.Etale.cupWithSupports`. -/
noncomputable def unitCupProduct (i j k : ℤ) (h : i + j = k) :
    ShiftedHom (𝟙_ _) (𝟙_ 𝐃(X, A)) i →ₗ[R] ShiftedHom (𝟙_ _) (𝟙_ 𝐃(X, A)) j →ₗ[R]
      ShiftedHom (𝟙_ _) (𝟙_ 𝐃(X, A)) k :=
  shiftedHomCupProduct R (derivedTensorLeftUnitor A X (𝟙_ _)).hom i j k h

variable {A R X} in
lemma unitCupProduct_apply (i j k : ℤ) (h : i + j = k) (x : ShiftedHom (𝟙_ _) (𝟙_ 𝐃(X, A)) i)
    (y : ShiftedHom (𝟙_ _) (𝟙_ 𝐃(X, A)) j) :
    unitCupProduct A R X i j k h x y =
      shiftedHomCupProduct R (derivedTensorLeftUnitor A X (𝟙_ _)).hom i j k h x y :=
  rfl

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
@[simps]
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
@[simps]
noncomputable def lowerStarClassEquivLowerShriek (M : 𝐃(X, A)) (n : ℤ) :
    ShiftedHom (𝟙_ _) ((R((a)_*[A])).obj M) n ≃ₗ[R] ShiftedHom (𝟙_ _) ((R(a)_![A]).obj M) n where
  toFun f := f ≫ ((rightDerivedLowerShriekIsoRightDerivedLowerStar A a).inv.app M)⟦n⟧'
  invFun g := g ≫ ((rightDerivedLowerShriekIsoRightDerivedLowerStar A a).hom.app M)⟦n⟧'
  left_inv f := by simp [← Functor.map_comp]
  right_inv g := by simp [← Functor.map_comp]
  map_add' f g := by simp
  map_smul' r f := by simp

end DirectImage

end Etale

end AlgebraicGeometry
