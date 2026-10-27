/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.NodalPointEtaleLocality
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource

/-! # Dimensions and nodal singularities under an étale cover over a field

Source: Stacks Project, curves.tex, Tags 0C5D and 0C57; descent.tex, Tags 04N4,
04NL and 036U; varieties.tex, Tag 0A21 (3), (5)
(blueprint: lem-trf-etale-cover-field-curve-nodality).

Smoothness at a point is expressed by smoothness on an open neighbourhood.
Completed local algebras use the existing canonical scalar map, not a chosen
coefficient field. There is no nonemptiness condition on the index type or schemes.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A jointly surjective étale family over an algebraically closed field preserves
local topological dimensions and detects pure dimension, pointwise smoothness, and,
in pure dimension one, nodal completions at nonsmooth points.

Source: Stacks Project, curves.tex, Tag 0C5D, lemma-nodal-family-etale-local-source,
and Tag 0C57, lemma-node-etale-local; descent.tex, Tags 04N4, 04NL, 036U;
varieties.tex, Tag 0A21 (3), (5)
(blueprint: lem-trf-etale-cover-field-curve-nodality).

Proof:
1. Fix i and y and put x = e_i(y). By def-weil-etale-morphism, e_i is flat and
   locally finitely presented, hence locally of finite type by
   def-sbc-locally-finite-presentation and def-weil-finite-type-morphism.
   Apply lem-sbc-flat-composite-fibre-dimension-at-point to D_i -> C -> Spec k.
   The fibres over Spec k identify with D_i and C: its residue field is k and
   def-pc-scheme-fibre and def-pc-fibre-product identify the fibre projections
   with isomorphisms. By lem-weil-pbc-etale-smooth-zero-dimensional-fibres the
   e_i-fibre has dimension zero at y. Additivity gives dim_y D_i = dim_x C.
2. By lem-trf-locally-algebraic-dimension-components, pure dimension n implies
   local dimension n everywhere, since every component through a point has
   dimension n and the family of those components is nonempty. Conversely,
   lem-sbc-constant-local-dimension-components with the whole scheme as open
   gives dimension n for every component. Use def-weil-pure-dimension.
   The equality in step 1 transfers purity to each D_i; in reverse, joint
   surjectivity lifts every x and gives constant local dimension on C.
3. Apply the pointwise clause of lem-trf-etale-source-smoothness to e_i and f.
   This gives the two open-neighbourhood smoothness conditions. In pure
   dimension one, lem-trf-nodal-point-etale-locality gives the equivalence of
   the completed local k-algebra presentations at y and x, in particular
   when both points are nonsmooth. All completions use maximal ideals.
4. If every nonsmooth point of C has this presentation, a nonsmooth y has
   nonsmooth image by step 3, and the same step transfers its presentation.
   Conversely, lift a nonsmooth x using joint surjectivity; step 3 makes the
   lift nonsmooth and transfers its presentation back to x. Empty sources
   contribute no points. An empty family forces C empty, so purity and the
   universal nodality conditions are vacuous. No separatedness or global
   quasi-compactness is used. -/
theorem etale_cover_field_curve_nodality
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [IsLocallyNoetherian C] {I : Type v} (D : I → Scheme.{u})
    (e : ∀ i : I, D i ⟶ C) [∀ i : I, Etale (e i)]
    [∀ i : I, LocallyOfFiniteType (e i ≫ f)] [∀ i : I, IsLocallyNoetherian (D i)]
    (hcover : ∀ x : C, ∃ (i : I) (y : D i), e i y = x) :
    (∀ (i : I) (y : D i), topologicalKrullDimAt y = topologicalKrullDimAt (e i y)) ∧
    (∀ n : ℕ, C.IsPureDimension n ↔ ∀ i : I, (D i).IsPureDimension n) ∧
    (∀ (i : I) (y : D i),
      (∃ V : C.Opens, e i y ∈ V ∧ Smooth (V.ι ≫ f)) ↔
        ∃ W : (D i).Opens, y ∈ W ∧ Smooth (W.ι ≫ e i ≫ f)) ∧
    (C.IsPureDimension 1 →
      (∀ (i : I) (y : D i),
        ¬ (∃ V : C.Opens, e i y ∈ V ∧ Smooth (V.ι ≫ f)) →
        ¬ (∃ W : (D i).Opens, y ∈ W ∧ Smooth (W.ι ≫ e i ≫ f)) →
        (Nonempty
          (@AlgEquiv k
            (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk (e i y)))
              (C.presheaf.stalk (e i y)))
            (MvPowerSeries (Fin 2) k ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
            _ _ _ (f.completedLocalScalarMap (e i y)).toAlgebra inferInstance) ↔
          Nonempty
            (@AlgEquiv k
              (AdicCompletion (IsLocalRing.maximalIdeal ((D i).presheaf.stalk y))
                ((D i).presheaf.stalk y))
              (MvPowerSeries (Fin 2) k ⧸
                Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
              _ _ _ ((e i ≫ f).completedLocalScalarMap y).toAlgebra inferInstance))) ∧
      ((∀ x : C, ¬ (∃ V : C.Opens, x ∈ V ∧ Smooth (V.ι ≫ f)) →
          Nonempty
            (@AlgEquiv k
              (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
                (C.presheaf.stalk x))
              (MvPowerSeries (Fin 2) k ⧸
                Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
              _ _ _ (f.completedLocalScalarMap x).toAlgebra inferInstance)) ↔
        ∀ (i : I) (y : D i),
          ¬ (∃ W : (D i).Opens, y ∈ W ∧ Smooth (W.ι ≫ e i ≫ f)) →
          Nonempty
            (@AlgEquiv k
              (AdicCompletion (IsLocalRing.maximalIdeal ((D i).presheaf.stalk y))
                ((D i).presheaf.stalk y))
              (MvPowerSeries (Fin 2) k ⧸
                Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})
              _ _ _ ((e i ≫ f).completedLocalScalarMap y).toAlgebra inferInstance))) := by
  sorry

end AlgebraicGeometry
