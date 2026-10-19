/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.TowerClassFinite

/-! # Finite supported diagonal normalization

Source: blueprint main-20261015, sec-smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-finite-diagonal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Direct image along the actual diagonal is exact on system sheaves.
Source: classes (3); finite direct image exactness
(blueprint: def-sp-tower-class-finite-diagonal).
Proof: a closed immersion has finite geometric fibres and its small pro-etale
direct image is exact, including the empty closed immersion. The coefficient
system maps are formed with the same identity structural maps at every level;
kernels and sheafified cokernels are levelwise, so the ordinary system direct
image preserves both. Transport through the section-normalized realization
retains those kernels and cokernels. -/
theorem diagonalPush_exact {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) :
    PreservesFiniteLimits g.push ∧ PreservesFiniteColimits g.push := by
  sorry

/-- Exact diagonal direct image preserves finite limits.
Source: classes (3) (blueprint: def-sp-tower-class-finite-diagonal). -/
instance diagonalPushLimits {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) :
    PreservesFiniteLimits g.push := (diagonalPush_exact l E g).1

/-- Exact diagonal direct image preserves finite colimits.
Source: classes (3) (blueprint: def-sp-tower-class-finite-diagonal). -/
instance diagonalPushColimits {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) :
    PreservesFiniteColimits g.push := (diagonalPush_exact l E g).2

/-- The supported finite quotient is induced by the same integral quotient on P.
Source: classes (3), supported quotient normalization
(blueprint: def-sp-tower-class-finite-diagonal).
Proof: over a chart U of W its source consists of locally constant integers on
P times_W U. Send each such integer to its residue multiple of one. The ordinary
pushforward evaluation identifies the target with these actual coefficient
sections on P times_W U. Constant generators locally generate the source and
sheaf gluing gives existence and uniqueness. -/
theorem finiteSupportedQuotient_existsUnique {b : SpTowerShriek.Base l E}
    {S : Scheme.{u}} (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) (n : ℕ) :
    ∃! q : diagonalIntegralSource S ⟶
      (finiteForget l E (diagonalSurface S) n).obj
        ((SpTowerShriek.ev l E (diagonalSurface S) n).obj
          (g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))))),
      ∀ (U : (diagonalSurface S).ProEtᵒᵖ) (k : ULift.{u + 1} ℤ),
        HEq
          (((g.ordinaryPushEvaluation n).hom.app
              (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))).val.app U
            (q.hom.app U ((toSheafify (Scheme.ProEt.topology (ProjectiveLine S))
              ((Functor.const (ProjectiveLine S).ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                  (chart (diagonalImmersion S) U) k)))
          (k.down : (SpTowerShriek.B l E (ProjectiveLine S) n).obj.obj
            (chart (diagonalImmersion S) U)) := by
  sorry

/-- The canonical supported finite coefficient quotient, fixed on integral generators.
Source: classes (3) (blueprint: def-sp-tower-class-finite-diagonal). -/
def finiteSupportedQuotient {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) (n : ℕ) :=
  (finiteSupportedQuotient_existsUnique l E g n).exists.choose

/-- The diagonal class evaluated in its actual finite coefficient module categories.
Source: classes (3) (blueprint: def-sp-tower-class-finite-diagonal). -/
def evaluatedDiagonal {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (d : Diagonal l E b S c) (n : ℕ) :=
  mapSingleArrow (SpTowerShriek.ev l E (diagonalSurface S) n) (2 : ℤ)
    ((d.geometry.push.singleFunctorCompRightDerivedFunctorIso).inv.app _ ≫
      diagonalArrow l E c d.sourceIso) ≫
    ((DerivedCategory.singleFunctor _ 0).map (lineEvaluation l E c n).hom)⟦(2 : ℤ)⟧'

/-- Concrete finite diagonal normalization, expressed by the coefficient-linear
realization of the signed Cartier boundary. The supported integer quotient and
the map z -> 1 tensor z fix the source and target, respectively.
Source: classes (3), proof steps 9--13 (blueprint: def-sp-tower-class-finite-diagonal). -/
def FiniteDiagonalNormalization {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (d : Diagonal l E b S c) : Prop :=
  ∀ n : ℕ,
    finiteBoundaryEquality
      ((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface S)) 0).map
        (finiteSupportedQuotient l E d.geometry n))
      (((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface S)) 0).map
        (finiteRootMap l E (diagonalSurface S) n))⟦(2 : ℤ)⟧')
      (forgetEvaluatedArrow (SpTowerShriek.ev l E (diagonalSurface S) n)
        (finiteForget l E (diagonalSurface S) n) (lineEvaluation l E c n)
        ((d.geometry.push.singleFunctorCompRightDerivedFunctorIso).inv.app _ ≫
          diagonalArrow l E c d.sourceIso))
      (mapSingleArrow (abEvaluation (diagonalSurface S) n) (2 : ℤ)
        (kummerComposite
          (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
          c.kummer.exact (diagonalBoundary S)))

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
