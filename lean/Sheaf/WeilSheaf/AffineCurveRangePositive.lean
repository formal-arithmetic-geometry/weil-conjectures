/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Curve.EtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.WeilSheaf.Category
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.FiniteTypeSheafFiniteness
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.FiniteMittagLeffler
import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.SfWeilSheafComplex

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Compactly supported direct image from a smooth affine curve has no cohomology above two.

Source: blueprint sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/
lem-zl-affine-curve-range.md, proof steps 1--3.
(blueprint: lem-zl-affine-curve-range-positive)

Proof: Work on the geometric fibre. Smoothness of relative dimension one gives a smooth
curve; its finitely many connected components can be treated separately, with the empty
scheme giving zero. Choose a smooth proper compactification of each component. Extension by
zero is exact and preserves constructibility, and compactification independence identifies
compactly supported direct image with proper direct image of that extension by zero.
Choose a finite coefficient field and a constructible integral lattice. For each finite
reduction, the extended sheaf is in degree zero on a proper smooth curve. Torsion etale
cohomological dimension at most two gives zero cohomology in degrees greater than two.
Etale/pro-etale comparison identifies these finite-coefficient computations with those in the
chosen pro-etale model. Proper finiteness makes all the finite-reduction cohomology groups
finite. Adic direct image is computed by their derived inverse limit. In its Milnor exact
sequence, the limit of the degree-r groups is zero for r > 2. The first derived limit of the
degree-(r-1) groups is also zero: a tower of finite groups is Mittag--Leffler. This includes
r = 3, where degree two itself need not vanish. Thus no extra degree-three term appears.
Rationalization and finite coefficient-field extensions preserve zero cohomology, as does
passage to algebraically closed coefficients. Forgetting the Weil structure commutes with the
derived functors and detects zero objects. The resulting Weil cohomology sheaf is therefore
zero for r > 2. No geometric connectedness or lisse hypothesis on G is required. -/
theorem isZero_homology_compactSupport_of_isAffine_of_two_lt [IsAffine X]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X)
    {r : ℤ} (hr : 2 < r) :
    IsZero ((WeilComplex.homologySheaf r).obj
      ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj G))) := by
  sorry

end AlgebraicGeometry.WeilSheaf
