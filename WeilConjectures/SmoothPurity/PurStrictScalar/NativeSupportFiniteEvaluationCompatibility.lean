/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.RamifiedReductionFiniteEvaluation

/-! # Finite evaluation of the native support model

Source: Stacks 03DA, 0D6E, 0E8I and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Native support evaluation equals the constant support model followed by finite
restriction of the proper/open image.
Source: Stacks 03DA, 0D6E, 0E8I, 0940.
(blueprint: lem-pur-native-support-finite-evaluation-compatibility).
Proof: expand supportModel into the normalized systemProper and systemOpen squares.
The identity-on-sections scalar restriction square is compatible with singleton
selection. Right-derived uniqueness with the fixed resolution units identifies
the proper evaluation square with the finite proper restriction square. Transpose
the open comparison under its exact adjunction: both maps have the same open unit,
and both vanish outside the open. Exact localization preserves this equality.
Compose these two squares and use naturality of reductionEvaluation. The native
finiteImageIso factors cancel the finite direct/open model comparisons. This gives
the displayed equation, including positive exponent one and the empty open. -/
theorem nativeSupport_finiteEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (m : ℕ) (hm : 1 ≤ m) (M : DerivedCategory (scalarReductionSource l E X)) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y (m - 1)).map
        ((supportModel l E c S).hom.app M) ≫
      (constantImageEvaluation l E c (m - 1)).hom.app ((reduction l E X S).obj M) ≫
      (PurCompactSupport.image (constants l E) c).map
        ((positiveReductionEvaluation l E X S m hm).hom.app M) ≫
      (positiveImageRestriction l E c m hm).hom.app
        ((pbcDerivedExtend (PurCompactSupport.projection l E m hm X)).obj M) =
      (positiveSupportEvaluation l E c S m hm).hom.app M := by sorry

end WeilConjectures.PurStrictScalar
