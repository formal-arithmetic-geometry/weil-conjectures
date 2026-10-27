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

/-- Realize the smooth source and its canonical Tate word on the two sides.
Source: latest blueprint integral-adjunction-bijection, Purity;
geometric realization Steps 6--7.
(blueprint: lem-pur-integral-geometric-purity-realization).

Proof: apply completed-operation substitution to pullback, tensor with the actual
integral roots-of-unity line, and the even shift. The native pullback comparison is the
specified reduction counit, so the cofinal source formula is the SourceModel equation.
The root maps respect coefficient transitions; their inverse limit and tensor powers give
towerTate, and pullback composition, tensor and shift coherences give towerTateWord.
They are natural before localization, giving towerComparison. Reduce the integral ordered
word to obtain TateComparison.reduction. The reconstruction unit supplies realization and
its unit formula. The two smooth packages give source constructibility and their
purity_realization fields make the displayed limit-of-gamma words invertible. Their
naturality gives natural isomorphisms. Finally compose with rightAdjointUniq to the
specified right adjoints, preserving the counits. These are exactly the two
SmoothGammaRealization predicates. For d=0 the line and shift are their unit words;
no negative tensor power or inverse of a root map is required.
-/
theorem integral_geometric_purity_realization [IsIso gx] (d : ℕ)
    (m : SmoothPart l E b o q a s d) :
    Nonempty (PurityPart l E b o q a s d m) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralGeometricComparison
