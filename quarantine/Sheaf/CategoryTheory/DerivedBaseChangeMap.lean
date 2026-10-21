/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
public import Sheaf.CategoryTheory.Sites.GrothendieckTopos

/-!
# Derived base-change maps for ringed topoi

Source: Stacks Project, Cohomology on Sites, Tag 07A7
(blueprint: def-trf-topos-derived-base-change-map).

The square and its derived pullback/direct-image data are explicit.  In particular,
the three comparison isomorphisms and the compatible square identification determine
the comparison used below; the map is then the counit transpose along the displayed
derived adjunction.  No Cartesian, flatness, properness, or boundedness hypothesis is
part of this definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RingedDerivedComparisons

namespace CategoryTheory.RingedDerivedComparisons

/-- A commutative square of ringed topoi together with its total derived functors,
composition comparisons, and the specified inverse-image square identification.
The four `Site`s are the chosen small presentations of the four Grothendieck topoi;
`Site.D` is their ordinary unbounded derived category of sheaves of modules.
Source: Stacks Project, Cohomology on Sites, Tags 0D6D and 07A7
(blueprint: def-trf-topos-derived-base-change-map). -/
structure DerivedBaseChangeSquare (E E' F F' : Site.{u, w}) where
  g' : Morphism E' E
  f' : Morphism E' F'
  f : Morphism E F
  g : Morphism F' F
  p : Morphism E' F
  q : Morphism E' F
  lf : Lift f
  lg : Lift g
  lf' : Lift f'
  lg' : Lift g'
  lp : Lift p
  lq : Lift q
  pInverse : p.inverse ≅ g.inverse ⋙ f'.inverse
  qInverse : q.inverse ≅ f.inverse ⋙ g'.inverse
  pRing : p.ringMap =
    pInverse.hom.app ((sheafCompose F.J (CategoryTheory.forget CommRingCat.{u})).obj F.A) ≫
      f'.inverse.map g.ringMap ≫ f'.ringMap
  qRing : q.ringMap =
    qInverse.hom.app ((sheafCompose F.J (CategoryTheory.forget CommRingCat.{u})).obj F.A) ≫
      g'.inverse.map f.ringMap ≫ g'.ringMap
  squareInverse : p.inverse ≅ q.inverse
  squareRing : p.ringMap =
    squareInverse.hom.app
      ((sheafCompose F.J (CategoryTheory.forget CommRingCat.{u})).obj F.A) ≫ q.ringMap
  /-- Canonical composition, fixed on K-flat representatives. -/
  firstComposition : Composition lf' lg lp pInverse
  /-- Canonical composition for the other path, with the same normalization. -/
  secondComposition : Composition lg' lf lq qInverse
  /-- Canonical transport along the specified ring-compatible geometric isomorphism. -/
  squareComparison : TwoIso lp lq squareInverse

/-- The canonical comparison `theta` and its counit-transpose base-change map.
For `K : D_E`, the result has source `Lg* Rf* K` and target
`Rf'* Lg'* K`; its transpose is the displayed composite through the counit of
`Lf* ⊣ Rf*`.  The first three factors are exactly
`c_{f',g}^{-1}`, `delta`, and `c_{g',f}`.
Source: Stacks Project, Cohomology on Sites, Tag 07A7
(blueprint: def-trf-topos-derived-base-change-map). -/
def derivedBaseChangeMap {E E' F F' : Site.{u, w}}
    (S : DerivedBaseChangeSquare E E' F F') (K : E.D) :
    S.lg.edge.left.obj (S.lf.edge.right.obj K) ⟶
      S.lf'.edge.right.obj (S.lg'.edge.left.obj K) :=
  (CategoryTheory.mateEquiv S.lf.edge.derivedAdjunction S.lf'.edge.derivedAdjunction
    (TwoSquare.mk _ _ _ _
      (((S.firstComposition.pullback.symm ≪≫ S.squareComparison.pullback) ≪≫
        S.secondComposition.pullback).hom))).app K

end CategoryTheory.RingedDerivedComparisons
