/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Sheaf.AlgebraicGeometry.PureDimension
import Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.AlgebraicGeometry.LimitFibreDimensionBound
import Sheaf.AlgebraicGeometry.RetrocompactBoundedFibreDimension
import Sheaf.RingTheory.DimensionAtPointComponents
import Sheaf.TraceFormula.RelativeDimensionBaseChange
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Pure relative dimension descends to a finite stage

Source: Stacks Project, Limits, Tag 0EY2, together with Morphisms, Tags 02NJ and 02NK
(blueprint: lem-trf-pure-relative-dimension-finite-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Pure relative dimension of a locally finitely presented morphism over an affine-transition
inverse limit is eventually present at every finite stage.

Source: Stacks Project, Limits, Tag 0EY2, lemma-descend-dimension-d; persistence under base
change is Morphisms, Tag 02NK, with the relative-dimension notion of Tag 02NJ.
The limit and stage morphisms are the underlying maps of the canonical base changes in `Over`.
The disjunction permits empty fibres, exactly as in the source statement.

Proof plan (the six steps of the node):
1. Restrict to the cofinal tail above `i₀`. Form the source and target base-change systems.
   The scheme-over-limit lemma gives affine transitions and their limits. Qcqs permanence
   makes the structure maps and `f₀` quasi-compact and quasi-separated. Local finite
   presentation is stable under base change, so the stage morphisms are of finite type.
   The source-to-base-change comparisons are isomorphisms, hence closed immersions,
   as required for the finite-stage fibre-dimension bound (Tags 01YZ, 05M5, and 01T4).
2. Pure dimension `d` bounds the dimension of each limit fibre by `d`. Apply Tag 05M5
   to descend this bound and reindex the tail so every fibre of `f₀` has dimension at
   most `d`.
3. Let `U₀` be the locus where local fibre dimension is at most the integer `d - 1`.
   For positive `d`, Tag 02G0 makes it open and retrocompact. For `d = 0` it is empty,
   since local dimension at a point is nonnegative. Thus `E = X₀ \ U₀` is constructible.
4. A finite-type scheme over a field has local dimension equal to the maximum of the
   dimensions of the components through the point: use the affine component formula
   and invariance under nonempty opens in an irreducible locally algebraic scheme
   (Tags 00OT and 0A21). Hence a pure `d`-dimensional fibre has local dimension `d`
   everywhere. Tag 02FY preserves local fibre dimension under base change, so no point
   of the limit source maps into `U₀`; its image lies in `E`.
5. Apply constructible containment to the source system and `E`. At some stage and
   at every later stage the image in `X₀` lies in `E` (Tag 05F4).
6. At that stage, membership in `E` gives local fibre dimension greater than the integer
   `d - 1`, and Step 2 bounds it by `d`; Tag 02FY transfers both bounds. Thus the local
   fibre dimension is `d` at every point. At the generic point of each component, the
   affine component formula and invariance on nonempty opens identify this value with
   the component dimension, giving pure dimension `d`. The later morphisms are base
   changes of this stage morphism; Tag 02NK gives purity at every later stage.
(blueprint: lem-trf-pure-relative-dimension-finite-stage) -/
theorem pure_relative_dimension_finite_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left]
    (d : ℕ)
    (hpure : ∀ z : ((Over.pullback (c.π.app (op i₀))).obj Y₀).left,
      IsEmpty (((Over.pullback (c.π.app (op i₀))).map f₀).left.fiber z) ∨
        (((Over.pullback (c.π.app (op i₀))).map f₀).left.fiber z).IsPureDimension d) :
    ∃ i : I, ∃ hi : i₀ ≤ i,
      ∀ (j : I) (hj : i ≤ j),
        ∀ z : ((Over.pullback (D.map (homOfLE (hi.trans hj)).op)).obj Y₀).left,
          IsEmpty (((Over.pullback (D.map (homOfLE (hi.trans hj)).op)).map f₀).left.fiber z) ∨
            Scheme.IsPureDimension
              (((Over.pullback (D.map (homOfLE (hi.trans hj)).op)).map f₀).left.fiber z) d := by
  sorry

end AlgebraicGeometry
