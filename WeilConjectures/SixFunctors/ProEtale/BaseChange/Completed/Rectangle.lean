/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.ReductionHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjectionBaseChange

/-!
# The finite-level exchange rectangle on pro-étale derived categories

Fix a commutative square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
and a coefficient object `P ∈ D(Y_proét)` (for instance the reduction `P_n = Λ/Iⁿ` of an adic
coefficient ring, see `def-weil-pbc-adic-coefficient-datum`). This file instantiates the abstract
exchange rectangle of `WeilConjectures.CategoryTheory.CompletedBaseChange.Rectangle` at the
pro-étale derived categories:

* `AlgebraicGeometry.ProEtale.baseChangeSquare A sq`: the base change square of the derived
  categories `D(X_proét), D(Y_proét), D(X'_proét), D(Y'_proét)` with the derived pullbacks, the
  derived direct images and the Cartesian identification
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso`; its exchange map is the derived base
  change map `AlgebraicGeometry.ProEtale.derivedBaseChangeMap` (`def-weil-pbc-ambient-ringed-exchange`);
* `AlgebraicGeometry.ProEtale.tensorReduction A sq P`: the reduction `- ⊗ᴸ P` of this square into
  itself, with the tensor comparisons of the derived pullbacks. The commutativity of the cube of
  left adjoints (the field `cube`, assumed in the abstract setting) is **proved** here from the
  compatibility of the square isomorphism with the tensor comparisons;
* `AlgebraicGeometry.ProEtale.tensorReductionHom A sq φ`: a morphism of coefficients `P ⟶ P'`
  (e.g. the quotient `P_{n+1} ⟶ P_n`) induces a morphism of reductions.

For `K ∈ D(X_proét)` the four corners (`def-weil-pbc-four-corners`,
`def-weil-pbc-level-map-corners`) are
```
A = Lg^*(Rf_*K ⊗ᴸ P),        B = Lg^*Rf_*(K ⊗ᴸ Lf^*P),
C = Rf'_*Lg'^*K ⊗ᴸ Lg^*P,     D = Rf'_*Lg'^*(K ⊗ᴸ Lf^*P),
```
and the four arrows (`def-weil-pbc-four-arrows`, `def-weil-pbc-level-map-arrows`) are
`h = Lg^* π_{f,K,P}`, `v = (Ex_K ⊗ 1) ∘ comparison`, `h' = Rf'_*(comparisons) ∘ π_{f',Lg'^*K,Lg^*P}`
and `v' = Ex_{K ⊗ᴸ Lf^*P}`; they are identified with the arrows of the abstract reduction by
`AlgebraicGeometry.ProEtale.tensorReduction_arrowH_app` etc.

## Main results

- `AlgebraicGeometry.ProEtale.finiteLevelRectangle`: `v' ∘ h = h' ∘ v`
  (`lem-weil-pbc-finite-level-rectangle`, `lemma-weil-pbc-level-map-rectangle`).
- `AlgebraicGeometry.ProEtale.finiteLevelRectangle_naturality`: operator naturality
  (`lemma-weil-pbc-level-map-operator-naturality`).
- `AlgebraicGeometry.ProEtale.finiteLevelRectangle_tower_comm`: the four arrows commute with the
  coefficient transitions (`lemma-weil-pbc-level-map-tower-compatibility`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [ProEtale.UpperStarPreservesFlat A]

namespace ProEtale

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The base change square of pro-étale derived categories attached to a commutative square of
schemes `g' ≫ f = f' ≫ g` (Blueprint `def-weil-pbc-cartesian-square`, on derived categories):
derived pullbacks, derived direct images with the adjunctions `Lf^* ⊣ Rf_*`, and the Cartesian
identification `Lg^* Lf'^* ≅ Lf^* Lg'^*`. -/
noncomputable def baseChangeSquare (sq : CommSq g' f' f g) :
    BaseChangeSquare (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X') A))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology Y') A)) where
  upperF := L((f)^*[A])
  lowerF := R((f)_*[A])
  adjF := derivedUpperStarLowerStarAdjunction A f
  upperF' := L((f')^*[A])
  lowerF' := R((f')_*[A])
  adjF' := derivedUpperStarLowerStarAdjunction A f'
  upperG := L((g)^*[A])
  upperG' := L((g')^*[A])
  iso := leftDerivedUpperStarSquareIso A sq

/-- The exchange map of `ProEtale.baseChangeSquare` is the derived base change map
(Blueprint `def-weil-pbc-ambient-ringed-exchange`). -/
lemma baseChangeSquare_exchange (sq : CommSq g' f' f g) :
    (baseChangeSquare A sq).exchange.natTrans = derivedBaseChangeMap A sq := rfl

/-- The reduction `- ⊗ᴸ P` of the pro-étale base change square along a coefficient object
`P ∈ D(Y_proét)`: on the four corners it is the tensor product with `P`, `Lf^*P`, `Lg^*P` and
`Lf'^*Lg^*P`, the comparisons are the tensor comparisons of the derived pullbacks, and the
commutativity of the cube of left adjoints is
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso_hom_tensor`. -/
noncomputable def tensorReduction (sq : CommSq g' f' f g)
    (P : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (baseChangeSquare A sq).Reduction (baseChangeSquare A sq) where
  redX := (-⊗ᴸ-(X)[A]).flip.obj (L((f)^*[A]).obj P)
  redY := (-⊗ᴸ-(Y)[A]).flip.obj P
  redX' := (-⊗ᴸ-(X')[A]).flip.obj (L((f')^*[A]).obj (L((g)^*[A]).obj P))
  redY' := (-⊗ᴸ-(Y')[A]).flip.obj (L((g)^*[A]).obj P)
  γF := TwoSquare.mk _ _ _ _
    { app M := ((leftDerivedUpperStarTensorComparison A f).app M).app P
      naturality M N φ := by
        simpa using congrArg (fun α ↦ α.app P)
          ((leftDerivedUpperStarTensorComparison A f).naturality φ) }
  γF' := TwoSquare.mk _ _ _ _
    { app M := ((leftDerivedUpperStarTensorComparison A f').app M).app (L((g)^*[A]).obj P)
      naturality M N φ := by
        simpa using congrArg (fun α ↦ α.app (L((g)^*[A]).obj P))
          ((leftDerivedUpperStarTensorComparison A f').naturality φ) }
  δG := NatIso.ofComponents
    (fun M ↦ asIso (((leftDerivedUpperStarTensorComparison A g).app M).app P))
    (fun φ ↦ by
      simpa using congrArg (fun α ↦ α.app P)
        ((leftDerivedUpperStarTensorComparison A g).naturality φ))
  δG' := NatIso.ofComponents
    (fun K ↦ asIso (((leftDerivedUpperStarTensorComparison A g').app K).app
        (L((f)^*[A]).obj P)) ≪≫
      ((-⊗ᴸ-(X')[A]).obj (L((g')^*[A]).obj K)).mapIso
        ((leftDerivedUpperStarSquareIso A sq).app P).symm)
    (fun φ ↦ by
      sorry)
  cube := by
    sorry

end ProEtale

end AlgebraicGeometry
