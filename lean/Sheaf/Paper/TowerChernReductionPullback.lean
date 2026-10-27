/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E9
-/
module

public import Sheaf.Paper.TowerChernPullbackData

/-! # Pullback of integral reduction to the quotient tower

Source: blueprint classes proof (2), realization steps 2--4, before extension to E
(blueprint: lem-sp-tower-chern-reduction-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Integral reduction commutes with an exact inverse image of the quotient module
towers. Only the Z-to-R stage occurs; no scalar extension to A, Tate tensor line,
or coefficient/line comparison at A occurs in the conclusion.

Source: blueprint classes proof (2); realization proof steps 2--4
(blueprint: lem-sp-tower-chern-reduction-pullback).

Proof: identify abelian towers with sheaves on the vertical sequence site, and
their R-modules with the recorded module systems. The forgetful square identifies
the underlying inverse image; the Z/ell^(n+1) action is unique on each torsion
sheaf, so the identification is R-linear and respects quotient transitions.
Apply the derived algebra-diagram extension/pullback comparison for Z -> R.
Transport it to the given reduction functors by the unique isomorphisms respecting
their universal derived counits. This gives eta on every integral derived object.
For integers, transpose through the reduction adjunctions. The source normalization
turns both transposes into integerGenerator, and unit_normalization identifies
the results, including the canonical single comparisons.
For full units, transpose through the same adjunctions instead of recomputing
any cohomology. The target normalizations identify the transposes of rootIso
with the shifted signed Kummer boundaries. Exact-functor transport of the
short-exact-sequence triangle commutes with that boundary, including its shift
comparison. Naturality of the triangle under d.kummer then compares its two
boundaries. Substitute d.kummer_roots for the first component and d.kummer_units
for the last. Naturality of the single comparison, followed by the shift-by-two
comparison, gives exactly derivedRoot. The normalized mate relation of the
extension comparison identifies these equal transposes with the two sides of
the second equation. Injectivity of the reduction adjunction's hom equivalence
proves equality in the module-system derived category. No faithfulness of
forgetting or derived evaluation is asserted. Nothing uses nonemptiness,
flatness of f, or unramified E. -/
theorem tower_chernReduction_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤)))
    (cY : Chern l E Y) (cX : Chern l E X)
    (_nY : cY.Normalized l E) (_nX : cX.Normalized l E)
    (d : IntegralCoefficientPullback l E f cY cX) :
    ∃ η : cY.reduction.derived ⋙ d.pull.mapDerivedCategory ⟶
        (abPull f).mapDerivedCategory ⋙ cX.reduction.derived,
      η.app ((DerivedCategory.singleFunctor (Ab Y) 0).obj (integers Y)) ≫
          cX.reduction.derived.map (integerDerivedPull f) ≫ cX.unitIso.hom =
        d.pull.mapDerivedCategory.map cY.unitIso.hom ≫ d.derivedUnit.hom ∧
      η.app (((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y))⟦(1 : ℤ)⟧) ≫
          cX.reduction.derived.map (unitsDerivedPull f) ≫ cX.rootIso.hom =
        d.pull.mapDerivedCategory.map cY.rootIso.hom ≫ (d.derivedRoot 2).hom := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
