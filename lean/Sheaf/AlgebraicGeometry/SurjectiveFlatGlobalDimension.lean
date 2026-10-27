/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import WeilConjectures.Topology.DimensionSupremumLocalDimensions
import WeilConjectures.AlgebraicGeometry.Dimension

/-!
# Global dimension for a surjective flat morphism

Source: Stacks Project, Morphisms, Tag 0AFE, `lemma-rel-dimension-dimension`,
second proof paragraph (blueprint: lem-per-surjective-flat-global-dimension).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A surjective flat locally finite type morphism of locally Noetherian schemes with
constant local fibre dimension `d` has source dimension equal to target dimension plus `d`,
provided the target is nonempty. All dimensions are in `WithBot ℕ∞`.

Source: Stacks Project, Morphisms, Tag 0AFE, `lemma-rel-dimension-dimension`,
second proof paragraph (blueprint: lem-per-surjective-flat-global-dimension).

Proof:
1. Choose Noetherian affine neighbourhoods using `pqf-def-locnoeth`.
   By `lem-weil-pbc-affine-open-stalk-localization`, clause (c), their germ maps are
   localizations. Thus `lem-weil-pbc-localization-noetherian` makes every stalk of X
   and Y Noetherian, without a quasi-compactness or finite global dimension assumption.
2. For a in X and b = f(a), the stalk map is flat and local by `def-weil-flat-morphism`.
   Apply `lem-weil-pbc-flat-height-formula` at the maximal ideals. A local ring localized
   at its maximal ideal is unchanged, since the denominators are already units.
   Use `lem-sbc-scheme-fibre-stalk-quotient` to identify the quotient by the extended
   base maximal ideal with the fibre stalk. Ring isomorphisms preserve prime chains
   (`def-weil-pbc-krull-dimension-ring`). Hence dim O_{X,a} equals dim O_{Y,b} plus
   dim O_{X_b,a}.
3. Surjectivity and `def-pc-scheme-fibre` make every fibre nonempty, with every fibre
   point corresponding to a point a over b. Its local topological dimensions are d.
   By `lem-weil-pbc-dimension-supremum-local-dimensions`, its global dimension is d.
   Then `lem-pc-scheme-dimension-local-rings` gives d as the supremum of fibre stalk
   dimensions. Each is at most d and some attains d: for d = 0 any point works;
   for d > 0, otherwise all are at most d - 1. The fibre stalk dimensions need not
   all equal d.
4. By `lem-pc-scheme-dimension-local-rings` on X and Y, take the suprema of stalk
   dimensions. Step 2 and the bound in Step 3 give dim X <= dim Y + d. Conversely,
   for each b choose a fibre stalk attaining d. Its image a in X gives
   dim X >= dim O_{Y,b} + d. If dim Y is finite, its nonempty family of stalk
   dimensions attains that integer (including zero); if dim Y is infinite, the same
   inequalities force dim X to be infinite. These two bounds give the equality.
   Nonempty Y excludes the empty supremum and surjectivity also makes X nonempty. -/
theorem topologicalKrullDim_eq_add_of_surjective_flat_constantRelativeDimension
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f] (d : ℕ)
    (hd : ∀ a : X, topologicalKrullDimAt (f.asFiber a) = (d : WithBot ℕ∞))
    [Surjective f] [Nonempty Y] :
    topologicalKrullDim X = topologicalKrullDim Y + (d : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
