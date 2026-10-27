/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.FiniteProjectionCompositionRealization
import Sheaf.SixFunctors.CompositionProjectionMate

/-! # Fixed-triangle binary square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection

namespace WeilConjectures.CompactSupportFiniteProjection

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  AlgebraicGeometry.ProEtale.derivedTensor Functor.leftDerivedFunctor
  DerivedCategory instCategoryDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions realization fixedComponent fixedTensor

def binarySquareEquation
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) : Prop :=
  ((partialTensor S Z).map
    ((S.finite.composition (X := X) (Y := Y) (Z := Z) f g cf cg cfg).hom.app K)).app L ≫
      component S (X := Y) (Y := Z) g cg ((S.finite.support (X := X) (Y := Y) f cf).obj K) L ≫
      (S.finite.support (X := Y) (Y := Z) g cg).map
        (component S (X := X) (Y := Y) f cf K ((torPull S (X := Y) (Y := Z) g).obj L)) =
    component S (X := X) (Y := Z) (f ≫ g) cfg K L ≫
      (S.finite.composition (X := X) (Y := Y) (Z := Z) f g cf cg cfg).hom.app
        (((partialTensor S X).obj K).obj ((torPull S (X := X) (Y := Z) (f ≫ g)).obj L)) ≫
      (S.finite.support (X := Y) (Y := Z) g cg).map ((S.finite.support (X := X) (Y := Y) f cf).map
        (((partialTensor S X).obj K).map
          (torPullComposition S (X := X) (Y := Y) (Z := Z) f g L).hom))




/-- The binary equation holds on a supplied compatible Cartesian triangle.
Source: the fixed-triangle step of fix-prop-projection-formula.proof.md;
coefficient projection formula, raw triangle law and endpoint pasting
(blueprint: lem-sf-finite-projection-binary-triangle-square).

Proof: use the proved projection-free triangle pasting, the raw factor projection
identities and the faithful constructible inclusion. The statement is strictly below
the existential theorem because all six triangle maps and the pullback square are
supplied. Zero objects, identity maps and empty schemes use the same equations. -/
theorem binary_square_on_triangle
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X V W Y B Z : SixFunctorSpace D}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry D).map j)] [IsOpenImmersion ((geometry D).map b)]
    [IsOpenImmersion ((geometry D).map i)] [QuasiCompact ((geometry D).map b)]
    [QuasiCompact ((geometry D).map i)]
    [IsProper ((geometry D).map q)] [IsProper ((geometry D).map p)] [IsProper ((geometry D).map s)]
    (hb : b ≫ p = q ≫ i)
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left) :
    binarySquareEquation S (X := X) (Y := Y) (Z := Z) (j ≫ q) (i ≫ s)
      (binaryFirst j q) (binarySecond i s)
      (binaryTotal j b q p i s hb) K L := by sorry


end WeilConjectures.CompactSupportFiniteProjection
