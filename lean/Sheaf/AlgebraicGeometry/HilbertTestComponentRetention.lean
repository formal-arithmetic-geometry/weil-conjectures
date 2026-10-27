/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelPresentation
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Blowup.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Field.ULift

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg
import WeilConjectures.RingTheory.AssociatedGradedRing
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.Blowup.Affine.Defs
import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import Sheaf.RingTheory.FlatGradedFibreRegularLift
import Sheaf.AlgebraicGeometry.JetDiagramHilbertControl
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import Sheaf.RingTheory.RegularSequenceGradedPolynomial

/-! # Component dimensions retained by Hilbert--Samuel tests

Source: Bierstone--Milman--Temkin, arXiv:0905.3580v1, sections 6.1--6.3 and Remark 6.2
(blueprint: lem-per-hilbert-test-component-retention).

These are global dimensions of the component subspaces through the point, not dimensions
of minimal-prime quotients of its local ring. Nilpotents are allowed. The finite sequence
is supplied using the existing presentation tests, with its initially empty test boundary.
Ordered earlier-center ideals are independent history data and impose no test-boundary
conditions here. No presentation, invariant, or resolution sequence is constructed.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.HilbertSamuel

/-- The global dimensions of irreducible components through a point. This is the profile
`P_X(x)` in BMT section 6.3, with the underlying topological subspace dimension
(blueprint: lem-per-hilbert-test-component-retention). -/
noncomputable def globalComponentDimensions (X : Scheme.{u}) (x : X) : Set (WithBot ℕ∞) :=
  {d | ∃ W : Set X, W ∈ irreducibleComponents X ∧ x ∈ W ∧ topologicalKrullDim W = d}

/-- Strict transform only loses component dimensions; a Hilbert--Samuel near point loses none.
The center is a closed subscheme of the ambient, with its specified factorization through X.
The immersion of X may be locally closed, and no reducedness is assumed.
Source: BMT sections 6.1 and 6.3, Gabber correction and Remark 6.2
(blueprint: lem-per-hilbert-test-component-retention).

Proof, node steps 1--4:
1. Locally make the embedding closed. By finite type over a Noetherian field there are
   finitely many irreducible components. Scheme-theoretic strict transform is the closure
   of the preserved complement of the center. Its components are precisely the closures
   of the dense opens of those original components not contained in the center. Distinct
   such components remain incomparable. A component through y comes from one through x;
   the dense open identifies function fields. Dimension equals transcendence degree for
   finite-type domains, giving the inclusion even with nilpotents.
2. For equality of the extended functions use `lem-per-scheme-near-point-normal-cone`:
   R = O_(X,x), I the center ideal, A = R/I, and gr_I R is A-flat, with residue fiber
   S = B[T_1,...,T_e]. The point y belongs to the vertex Proj k[T_1,...,T_e].
3. For a minimal prime p, the quotient to the component cone has homogeneous kernel
   represented by a in I^n intersect p. A nonzero vertex image would make multiplication
   injective by `lem-trf-graded-polynomial-vertex-regularity`. The flat graded fiber lift
   makes a a nonzerodivisor in R. Minimal primes are associated in a Noetherian ring,
   contradicting a in p. Thus this kernel lies in the vertex kernel, degree by degree.
4. Relative Proj base change of the component Rees algebra identifies its exceptional
   fiber with this component cone. The kernel inclusion puts the whole vertex in every
   component fiber. Hence every component through x has strict transform through y.
   A component contained in the center has empty Proj, and is excluded by this conclusion,
   not by an extra hypothesis. Step 1 then gives equality of dimension profiles. -/
theorem hilbert_test_blowup_component_retention {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [QuasiCompact p] [IsImmersion i]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    (C : Z.IdealSheafData) (c : C.subscheme ⟶ X)
    (hc : c ≫ i = C.subschemeι) [Smooth (C.subschemeι ≫ p)]
    (hconstant : IsLocallyConstant (fun a : C.subscheme ↦ function (i ≫ p) (c a)))
    (x : X) (hx : x ∈ Set.range c) (y : C.strictTransform i)
    (hy : strictTransformToSource i C.blowupMap C.support.compl y = x) :
    globalComponentDimensions (C.strictTransform i) y ⊆ globalComponentDimensions X x ∧
      (function (strictTransformToSource i C.blowupMap C.support.compl ≫ i ≫ p) y =
          function (i ≫ p) x →
        globalComponentDimensions (C.strictTransform i) y = globalComponentDimensions X x) := by
  sorry

/-- Every prefix of a supplied finite admissible presentation test sequence retains the
initial component profile, translated by the number of line tests. Around each retaining
point both the extended-level upper bound and profile containment hold on one open.
The ordered earlier-center ideals remain separate from `history j |>.boundary`: the
presentation starts that test boundary empty, and `Step` alone updates it.
Source: BMT sections 5.2 and 6.1--6.3, Gabber correction and Remark 6.2
(blueprint: lem-per-hilbert-test-component-retention).

Proof, node steps 5--8 (using steps 1--4 above):
5. Write L_j = Lambda^(r_j) H_0. The retained-test-boundary regularity lemma gives no
   return from a dropped level at an auxiliary test. Finite differences cancel summation
   at a line test. At an admissible blowup the center is in the retaining locus, while
   away from the center the map is an isomorphism. Thus retaining points have retaining
   ancestors at every prefix. The depth-zero profile is P_0 by hypothesis.
6. The presentation identifies its cosupport with the current retaining locus. Its smooth
   admissible center is therefore locally Hilbert--Samuel constant. Steps 1--4 preserve
   the profile at a retaining point of its actual strict transform. For a line product,
   components are Z times A^1 and their function fields acquire one independent variable;
   dimension equals transcendence degree and the tower formula increase each dimension
   by one. The Taylor free-variable formula sums the extended function once.
7. At a retaining exceptional-intersection test, the two boundary equations a,b form a
   regular sequence by `lem-per-retained-test-boundary-regularity`. Its cartesian charts
   R[v]/(av-b) and R[w]/(bw-a) are the intrinsic blowup charts by the regular-sequence
   chart theorem. Their associated graded ring is (R/(a,b))[T_1,T_2]. Use steps 3--4
   with B = k: the whole exceptional fiber lies on every component strict transform.
   Step 1 preserves the dimensions and excludes extra components, also with nilpotents.
8. Induction proves the profile formula at every prefix. Upper semicontinuity and finite
   image of the scheme Hilbert--Samuel function give a neighborhood with H_j <= L_j.
   Remove the finitely many closed components not through the retaining point to obtain
   profile containment there, and intersect these two neighborhoods. Empty retaining
   loci are vacuous. All transforms and the presentation are inputs, not existence claims.
-/
theorem hilbert_test_sequence_component_retention
    (n : ℕ) (history : Fin (n + 1) → Embedded (ULift.{u} ℚ))
    (marks : ∀ j : Fin (n + 1), Marked (history j))
    (steps : ∀ j : Fin n, Step (history j.castSucc) (history j.succ))
    (hfinite : QuasiCompact (history 0).p)
    (hpresentation : Presents (marks 0))
    (hadmissible : ∀ j : Fin n, (steps j).Admissible (marks j.castSucc).cosupport)
    (htransforms : ∀ j : Fin n, (steps j).Transforms (marks j.castSucc) (marks j.succ))
    (r : Fin (n + 1) → ℕ) (hrzero : r 0 = 0)
    (hrstep : ∀ j : Fin n,
      r j.succ = r j.castSucc + if (steps j).kind = .line then 1 else 0)
    (P₀ : Set (WithBot ℕ∞))
    (hbound : ∀ x : (history 0).X,
      le (function ((history 0).i ≫ (history 0).p) x) (history 0).level)
    (hprofile : ∀ x : (history 0).X,
      function ((history 0).i ≫ (history 0).p) x = (history 0).level →
        globalComponentDimensions (history 0).X x = P₀) :
    ∀ (j : Fin (n + 1)) (y : (history j).X),
      function ((history j).i ≫ (history j).p) y =
          (summation^[r j]) (history 0).level →
        globalComponentDimensions (history j).X y =
            (fun d : WithBot ℕ∞ ↦ d + (r j : WithBot ℕ∞)) '' P₀ ∧
          ∃ U : (history j).X.Opens, y ∈ U ∧ ∀ z : (history j).X, z ∈ U →
            le (function ((history j).i ≫ (history j).p) z)
                ((summation^[r j]) (history 0).level) ∧
              globalComponentDimensions (history j).X z ⊆
                (fun d : WithBot ℕ∞ ↦ d + (r j : WithBot ℕ∞)) '' P₀ := by
  sorry

end AlgebraicGeometry.HilbertSamuel
