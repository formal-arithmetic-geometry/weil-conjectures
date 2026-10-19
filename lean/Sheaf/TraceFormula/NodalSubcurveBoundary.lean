/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import Sheaf.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.TraceFormula.ReducedSchemeImage
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Sheaf.AlgebraicGeometry.ComplementaryPureSubcurveComponents
import Sheaf.AlgebraicGeometry.StacksNodalClosedSubcurve

/-! # Reduced nodal subcurves and their boundary

Source: Stacks Project, `curves.tex`, Tag 0E38 (blueprint: lem-trf-nodal-subcurve-boundary).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The reduced closed subscheme supported on the closure of the complement of a
closed immersion.  Source: Stacks Project, `curves.tex`, Tag 0E38
(blueprint: lem-trf-nodal-subcurve-boundary). -/
noncomputable def reducedComplement {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.mk
      (closure (Set.range (Scheme.openComplementOfIsClosedImmersion i).ι))
      isClosed_closure)).subscheme

/-- The canonical inclusion of the reduced complement into the ambient scheme.
Source: Stacks Project, `curves.tex`, Tag 0E38 (blueprint: lem-trf-nodal-subcurve-boundary). -/
noncomputable def reducedComplementι {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] : reducedComplement i ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.mk
      (closure (Set.range (Scheme.openComplementOfIsClosedImmersion i).ι))
      isClosed_closure)).subschemeι

/-- The canonical inclusion of the scheme-theoretic boundary.  The fibre product
of two closed immersions is locally the quotient by the sum of their ideals.
Source: Stacks Project, Tag 0E38 (blueprint: lem-trf-nodal-subcurve-boundary). -/
noncomputable def reducedBoundaryι {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] :
    pullback (C := Scheme.{u}) i (reducedComplementι i) ⟶ X :=
  pullback.fst i (reducedComplementι i) ≫ i

/-- A reduced pure one-dimensional subcurve of a nodal neighbourhood is nodal;
its scheme-theoretic boundary is a finite disjoint union of rational points,
which are nodes of the ambient scheme and smooth on both subcurves.
Source: Stacks Project, `curves.tex`, Tag 0E38, (1), (2)(a)--(c)
(blueprint: lem-trf-nodal-subcurve-boundary).

Proof plan:
1. A field is Noetherian. By lem-weil-pbc-finite-type-over-noetherian, X is
   Noetherian. Its open N is Noetherian and quasi-compact by
   lem-weil-pbc-noetherian-open-subscheme-noetherian. Reducedness restricts
   to N, and finitely many restricted finite-type charts make N finite type.
   Y is still reduced, closed and pure of dimension one in N. If N is empty,
   Y and the boundary are empty and all assertions are vacuous.
2. Apply lem-sbc-equidimensional-open-local-dimension to X, its full open,
   and n = 1. Then lem-sbc-constant-local-dimension-components on the open N
   gives pure dimension one for N.
3. Put W equal to the reduced closure of N minus Y in N.
   By lem-trf-complementary-pure-subcurve-components, W is pure of dimension
   one, possibly empty, and its reduced complementary closure is Y.
   Both complementary opens are reduced, so lem-trf-reduced-scheme-image
   identifies their scheme-theoretic closures with W and Y.
4. The immersion of X minus Y into X is quasi-compact because X is Noetherian,
   and quasi-separated because it is an immersion. Its reduced image is Z by
   lem-trf-reduced-scheme-image. Apply lemma-nagata-scheme-image-restrict-open
   to identify W with Z restricted to N. Since Y lies in N, the intersections
   Y cap W and Y cap Z agree, including their sum-of-ideals scheme structure.
5. Apply lem-trf-stacks-nodal-closed-subcurve to N and Y. The previous steps
   supply every ambient hypothesis. The base is algebraically closed, so
   lem-weil-pbc-closed-point-residue-field-base identifies closed residue fields
   with k. Tag 0E38 gives nodality of Y, a finite separable boundary, ambient
   nodes, and smoothness on Y. The local rings of N and X agree.
6. Every finite extension of an algebraically closed field is the base field:
   each minimal polynomial splits and is irreducible, hence linear. Therefore
   the boundary is a finite disjoint union of copies of Spec k, including the
   empty union.
7. If W is empty, the boundary is empty. Otherwise apply
   lem-trf-stacks-nodal-closed-subcurve to N and W, whose complementary closure
   is Y by step 3. Its smoothness conclusion gives smoothness of W along the
   boundary. Since W is the restriction of Z to N, Z is smooth there too.
-/
theorem nodal_subcurve_boundary
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsReduced X] (hpureX : X.IsPureDimension 1)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hpureY : Y.IsPureDimension 1) (N : X.Opens)
    (hN : ∀ y : Y, i y ∈ N)
    (hnodal : ∀ (x : X), x ∈ N → x ∈ closedPoints X →
      ¬(f.stalkMap x).hom.FormallySmooth →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1}))) :
    (∀ (x : Y), x ∈ closedPoints Y →
      ¬((i ≫ f).stalkMap x).hom.FormallySmooth →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
          (Y.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1}))) ∧
    (∃ n : ℕ, Nonempty
      (pullback (C := Scheme.{u}) i (reducedComplementι i) ≅
        ∐ fun _ : Fin n => Spec (.of k))) ∧
    (∀ t : pullback (C := Scheme.{u}) i (reducedComplementι i),
      reducedBoundaryι i t ∈ closedPoints X ∧
      ¬(f.stalkMap (reducedBoundaryι i t)).hom.FormallySmooth ∧
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk (reducedBoundaryι i t)))
          (X.presheaf.stalk (reducedBoundaryι i t)) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1}))) ∧
    (∀ t : pullback (C := Scheme.{u}) i (reducedComplementι i),
      ((i ≫ f).stalkMap ((pullback.fst i (reducedComplementι i)) t)).hom.FormallySmooth ∧
      ((reducedComplementι i ≫ f).stalkMap
        ((pullback.snd i (reducedComplementι i)) t)).hom.FormallySmooth) := by
  sorry

end AlgebraicGeometry
