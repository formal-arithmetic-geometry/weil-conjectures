/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-! # Scalar coherence for one part of the affine normal-form argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Pullback and the chart presentation commute with the single scalar map.
This is the comparison for the direct normal form, before any coordinate exchange.
Source: Charts, retained Steps 10--11 of reduction-exceptional
(blueprint: lem-sp-finite-affine-scalar-chart-presentation).

Proof:
1. Cancel the ordered normal forms against the first factors in
   finiteAffineChartNormalIso. Insert finiteAffineExpandOrderedIso. In positive
   dimension it is the identity; at zero its scalar square is the canonical
   scalar/pullback, tensor-unit and zero-shift normalization. Thus it suffices to
   compare the direct pullback/right-Tate/shift presentations.
2. Expand tensorEPullback for the chart e. The scalar/pullback tensor square and
   shift naturality move scalar extension through its first factors. Its Tate
   factor has the same ordinary balancing square at both endpoints: on each pure
   ordered root tensor the coefficient a,b is sent to phi(a)b and every root to
   its pullback. The scalar-unit and ordered tensor recursions prove this in all
   powers; flatness identifies the ordinary and derived single comparisons.
3. Apply scalar/pullback composition to e and the affine projection. This gives
   the inverse scalar/pullback comparison for their composite with the exact same
   orientation as finiteAffineNormalScalarMap. Integer shift compatibility moves
   the accumulated even shift through this equality.
4. Apply the normalized scalar symmetry law to convert the right Tate factor
   into the chart operation's left Tate factor. No two Tate factors are exchanged.
   The canonical exact-to-left-derived pullback comparisons turn the remaining
   inverse scalar/pullback factor into finiteAffineExactPullbackScalarIso.
5. Naturality and inverse cancellation remove the inserted comparisons. The
   resulting factors, in order, are precisely finiteAffineChartScalarMap. This
   also proves the zero-coordinate case with its canonical unit expansion. -/
theorem finiteAffineScalar_chartPresentation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    {U : Scheme.{u}} [IsNoetherian U] (e : U ⟶ affineTraceTower S d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (K : DerivedCategoryModule A S) :
    (scalarPullbackIso φ e).inv.app ((orderedAffineRight A N hA S d).obj K) ≫
        (ordinaryFinitePullback B e).map (finiteAffineOrderedScalarMap φ N hA hB S d K) ≫
        (ordinaryFinitePullback B e).map
          ((orderedAffineRightIso B N hN hB S hS d).inv.app ((scalarExtension φ S).obj K)) ≫
        (finiteAffineChartNormalIso B N hN hB S hS d e ((scalarExtension φ S).obj K)).hom =
      (scalarExtension φ U).map
          ((ordinaryFinitePullback A e).map
              ((orderedAffineRightIso A N hN hA S hS d).inv.app K) ≫
            (finiteAffineChartNormalIso A N hN hA S hS d e K).hom) ≫
        finiteAffineChartScalarMap φ N hA hB (e ≫ affineTraceProjection S d)
          d (2 * (d : ℤ)) K := by
  sorry

end AlgebraicGeometry.Etale
