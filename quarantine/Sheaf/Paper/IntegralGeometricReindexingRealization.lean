/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.IntegralGeometricComparisonData

/-! # A component of integral geometric comparison realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IntegralGeometricComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)
  {X' X Y' Y : Scheme.{u}} {gx : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {gy : Y' ⟶ Y} {sq : IsPullback gx f' f gy}
  {c : Compactification f}
  [∀ z : X, Invertible (l : X.residueField z)]
  [∀ z : Y, Invertible (l : Y.residueField z)]
  [∀ z : X', Invertible (l : X'.residueField z)]
  [∀ z : Y', Invertible (l : Y'.residueField z)]
  (a : SpTowerMate.Data l E b o q sq c)
  (s : SpExceptionalBaseChange.IntegralData l E b o q a)
  [QuasiCompact f] [QuasiCompact f']
  [QuasiCompact (c.i ≫ c.g)] [HasCompactification (c.i ≫ c.g)]
  [QuasiCompact ((c.ofIsPullback sq).i ≫ (c.ofIsPullback sq).g)]
  [HasCompactification ((c.ofIsPullback sq).i ≫ (c.ofIsPullback sq).g)]

/-- Realize inverse image and total limit, with the reconstruction unit equation.
Source: latest blueprint integral-adjunction-bijection, Normalization;
geometric realization Steps 2--4.
(blueprint: lem-pur-integral-geometric-reindexing-realization).

Proof: use the coefficient isomorphism compatible with every quotient projection to
identify ordinary inverse image with exact reindexing on completed modules and fixed-ring
and varying-ring strict towers. Its exact inverse is inverse reindexing. Transpose a map
from an acyclic complex through this equivalence. The inverse preserves acyclicity, so
K-injectivity supplies a null homotopy, which transposes back. This proves the three
K-injective assertions, without claiming evaluation preserves K-injectives. Apply ordinary
inverse-limit commutation to a K-injective resolution after scalar restriction. This gives
the derived limit comparison. The reconstruction units and the projection normalization
of the reindexing comparison give exactly PullLimit.unit. For ell-power rather than
uniformizer-power indices, write ell as a unit times a positive power of the uniformizer
and apply cofinal Roos restriction; its maps preserve quotient augmentations. Exact
countable products and the strict Roos/derived-limit comparison justify this restriction.
The argument applies to each horizontal isomorphism separately, including identities.
-/
theorem integral_geometric_reindexing_realization [IsIso gx] [IsIso gy] :
    Nonempty (ReindexingPart l E b o q a s) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralGeometricComparison
