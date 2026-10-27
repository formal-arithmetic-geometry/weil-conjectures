/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Paper.TowerChernPullbackData

/-! # Invertibility of the integral reduction mate

Source: blueprint classes proof (2), integral quotient reduction.
(blueprint: lem-sp-tower-reduction-mate-invertible).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.singleFunctors
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapHomologicalComplex

set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical mate of the derived forgetful square. Its construction uses only
adjunction units and counits, with no choices of normalized endpoints.
Source: classes (2), reduction/pullback comparison
(blueprint: lem-sp-tower-reduction-mate-invertible). -/
def reductionPullbackMate {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cY : Chern l E Y} {cX : Chern l E X}
    (d : IntegralCoefficientPullback l E f cY cX) :
    (abPull f).mapDerivedCategory ⋙ cX.reduction.derived ⟶
      cY.reduction.derived ⋙ d.pull.mapDerivedCategory :=
  ((mateEquiv cY.reduction.derivedAdjunction cX.reduction.derivedAdjunction).symm
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d.forgetIso).hom)).natTrans

/-- Exact geometric inverse image commutes with integral quotient reduction, before
specifying either the integer or Kummer normalization.

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
classes proof (2); reduction-pullback proof steps 1--2
(blueprint: lem-sp-tower-reduction-mate-invertible).

Proof: realize abelian towers and semilinear quotient modules on the sequence site.
The recorded forgetful functors are the actual sectionwise forgetful functors.
At level n, every abelian morphism between sheaves killed by ell^(n+1) is linear
for the unique normalized constant quotient action. Consequently d.forgetIso
identifies d.pull with geometric inverse image of quotient modules, on morphisms
as well as objects, compatibly with every quotient transition. Apply the
algebra-diagram pullback/extension comparison for the constant integer ring and
the quotient diagram R. On a flat-term K-flat complex of entire integer towers,
the comparison is balanced association (p tensor r) mapped to f*p tensor f*r;
its inverse multiplies the scalar factors. This is invertible on these
representatives and descends to the whole unbounded derived categories.
Transport through the unique universal-derived-counit isomorphisms to the two
recorded reductions. Their representative transpose equations identify the
transported inverse comparison with the mate defined above: transpose its
component through the target reduction adjunction and obtain inverse image of
the source unit followed by the recorded forgetful square. The hom equivalence
is injective, so this is the specified mate. Thus the mate is invertible.
No endpoint normalization or Kummer boundary is used in this argument. -/
theorem tower_reductionMate_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cY : Chern l E Y} {cX : Chern l E X}
    (d : IntegralCoefficientPullback l E f cY cX) :
    IsIso (reductionPullbackMate l E d) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
