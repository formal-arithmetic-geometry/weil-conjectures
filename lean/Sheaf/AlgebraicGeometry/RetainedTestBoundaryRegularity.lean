/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Field.ULift

import Sheaf.AlgebraicGeometry.JetDiagramHilbertControl
import Sheaf.AlgebraicGeometry.CoordinateSubspaceBlowupCharts
import Sheaf.AlgebraicGeometry.DiagonalTaylorFaithfulFlatness
import Sheaf.AlgebraicGeometry.FormalCoefficientTransformCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Regular test boundaries at retained Hilbert--Samuel levels

Source: Bierstone--Milman--Temkin, arXiv:0905.3580v1, sections 5.2 and 6.2--6.3;
structural refinement by the supported coefficient-chart argument in the DAG
(blueprint: lem-per-retained-test-boundary-regularity).

The family `S` records a finite history, with all three test operations taken from
`HilbertSamuel.Step`. Its `levelTransform` field makes `(S j).level` precisely the initial
level summed once for each earlier line test. Only the newly started test boundary is used.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- Every prefix of an admissible finite test history satisfies the transported upper bound.
At a retained-level point every ordered subset of the distinct boundary hypersurfaces through
that point is regular on the intrinsic stalk, for every choice of local defining equations.
The ambient local equations are restricted by the closed embedding's actual stalk map.
No reducedness, irreducible-component assertion, or earlier-center boundary is imposed.
Source: BMT arXiv:0905.3580v1, sections 5.2 and 6.2--6.3; the node's supported standard-basis
refinement (blueprint: lem-per-retained-test-boundary-regularity).

Proof:
1. The supplied presentation identifies cosupport with the retained locus at every prefix,
   by def-trf-hilbert-samuel-presentation, so each admissible center lies in that locus.
   At an initial equality point use lem-per-nonreduced-regular-hilbert-coefficients and
   lem-trf-jet-diagram-hilbert-control to obtain the actual defining ideal, an empty boundary
   and a reference diagram with Hilbert function equal to the initial level. Shrink around
   the point and apply lem-trf-formal-coefficient-transform-criterion to identify equality
   with the coefficient order locus and to obtain the chart's upper bound. Below the initial
   level, until an admissible center affects the germ, auxiliary tests give smooth products
   by lem-trf-coordinate-subspace-blowup-charts. The jet formula sums the original function
   once per free variable. Its first differing index and sign survive inclusive summation.
2. Split the history into admissible blowups and intervening auxiliary strings. Inductively
   retain whole-series multiplication and derivative certificates, including below the level.
   Apply lem-per-supported-exceptional-chart-packet to each block, with its center in the
   equality locus. A strict rank witness excludes equality; otherwise the packet supplies
   the actual transformed ideal, pure transverse division, certificates and distinct boundary
   coefficient parameters. At equality lem-per-hilbert-boundary-supported-certificates
   recovers the five datum conditions for the next block. No inference that equality upstairs
   forces equality downstairs is used.
3. On transformed coefficient support, lem-per-hilbert-boundary-supported-certificates gives
   the upper bound and identifies equality with the coefficient order locus. Off support or
   in the strict-witness alternative, the packet bounds all lower jet dimensions and makes
   one strictly smaller. Use lem-trf-jet-diagram-hilbert-control at arbitrary scheme points
   to identify these functions with the intrinsic function and the reference function with
   the initial level summed once per line. Together with step 1 this proves every bound.
4. At equality write the formal local ideal as K=(f_i) in L[[W,Z]]. Supported generation and
   lem-trf-homogeneous-continuous-formal-division give unique division with remainder outside
   the diagram. The ideal K is the remainder kernel. Vertices have zero W components, so
   uniqueness makes the remainder map commute with each boundary coefficient parameter.
   For any subset T of these parameters, assign each remainder monomial divisible by T to
   its first dividing parameter. Dividing that monomial keeps it outside the diagram. Hence
   quotienting by T sets exactly those variables to zero in the remainder space, and every
   remaining parameter acts injectively. The constant monomial survives, including K=0.
5. The chart packet identifies boundary equations with these distinct parameters up to units
   and transverse coordinate straightening. The centered Taylor map is faithfully flat,
   including at nonclosed points, by lem-trf-diagonal-taylor-faithful-flatness. Descend each
   injectivity assertion by lem-weil-pbc-faithfully-flat-ideal-contraction. The final quotient
   is nonzero since the equations lie in the maximal ideal (also witnessed by the formal
   constant monomial). Units preserve generated ideals and injectivity. Apply
   def-weil-pbc-regular-sequence to each subset and order. Earlier-center ideals are absent.
-/
theorem retained_test_boundary_regularity (n : ℕ)
    (S : Fin (n + 1) → Embedded (ULift.{u} ℚ))
    (steps : ∀ a : Fin n, Step (S a.castSucc) (S a.succ))
    (M : Marked (S 0)) (hpresentation : Presents M)
    (hfinite : LocallyOfFiniteType ((S 0).i ≫ (S 0).p))
    (hcompact : QuasiCompact ((S 0).i ≫ (S 0).p))
    (hbound : ∀ x : (S 0).X, le (function ((S 0).i ≫ (S 0).p) x) (S 0).level)
    (hadmissible : ∀ a : Fin n, (steps a).Admissible (S a.castSucc).locus) :
    ∀ j : Fin (n + 1),
      (∀ x : (S j).X, le (function ((S j).i ≫ (S j).p) x) (S j).level) ∧
      ∀ x : (S j).X, function ((S j).i ≫ (S j).p) x = (S j).level →
        ∀ (m : ℕ) (labels : Fin m → Fin (S j).boundary.length),
          Function.Injective labels →
          (∀ a : Fin m, (S j).i x ∈ ((S j).boundary.get (labels a)).support) →
          ∀ equations : Fin m → (S j).Z.presheaf.stalk ((S j).i x),
            (∀ a : Fin m, stalkIdeal ((S j).boundary.get (labels a)) ((S j).i x) =
              Ideal.span {equations a}) →
            RingTheory.Sequence.IsRegular ((S j).X.presheaf.stalk x)
              (List.ofFn (fun a : Fin m ↦ ((S j).i.stalkMap x) (equations a))) := by
  sorry

end AlgebraicGeometry.HilbertSamuel
