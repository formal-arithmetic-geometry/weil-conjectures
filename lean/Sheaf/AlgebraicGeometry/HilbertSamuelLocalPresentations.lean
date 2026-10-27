/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Field.ULift

import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import Sheaf.SecTraceFormula.SmoothCenterBlowupGeometry
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm
import WeilConjectures.Blowup.Complement
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FiniteType

/-! # Local Hilbert--Samuel presentations and their transforms

Source: ILO VIII 2.3.11--2.3.13, pp. 93--94; BMT, arXiv:0905.3580, sections 6.1--6.3;
BM 1997, Chapter III (blueprint: lem-trf-hilbert-samuel-local-presentations).

The declarations separate the numerical assertions, existence, finite-test equivalence,
maximal order at singular points, common étale comparison, and smooth pullback.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.HilbertSamuel

/-- Local finiteness and lexicographic upper semicontinuity of the normalized function.
The length finiteness clause makes the natural-valued definition literal, including `n = 0`.
Source: BMT 6.1; BM 1997, Remarks 9.1, Theorem 9.2 and Lemma 9.3
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: `lem-trf-jet-diagram-hilbert-control` identifies the coordinates with finite Taylor-module
fiber dimensions and gives locally finitely many diagrams, hence levels. Affine finite-type
rings are Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`. Their finite Taylor
modules are finitely presented by `lem-trf-noetherian-submodule-finitely-presented`. A fiber
matrix has cokernel dimension at least c exactly when its appropriate minors vanish, so each
coordinate is upper semicontinuous. Choose a finite bound on the first differing index of
any two of the finitely many local levels. Intersect the coordinate upper-semicontinuity
neighborhoods up to that bound to obtain lexicographic upper semicontinuity. Maximal-ideal
power quotients have finite length by their finite residue-field graded pieces. -/
theorem function_local_finite_upperSemicontinuous {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [IsImmersion i] [IsReduced X]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)] :
    (∀ (x : X) (n : ℕ), Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (n + 1)) < ⊤) ∧
    (∀ x : X, ∃ U : X.Opens, x ∈ U ∧ (function (i ≫ p) '' (U : Set X)).Finite) ∧
    (∀ H : ℕ → ℕ, IsClosed {x : X | le H (function (i ≫ p) x)}) := by
  sorry

/-- Nonincrease under any smooth locally Hilbert--Samuel constant center, including away
from that center. Source: BMT 6.1(3); BM 1997, Theorems 7.20 and 9.4
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: In a local equality stratum use `lem-trf-formal-coefficient-transform-criterion` and
`lem-pur-smooth-pair-local-coordinates` to compute transformed coefficients and obtain the
inequality. Smoothness of the center makes it reduced, so its inclusion in the equality set
factors scheme-theoretically through the embedded scheme. Outside the center use
`thm-nagata-global-blowup-complement` and `lemma-nagata-strict-transform-over-complement`.
Cover the locally constant center by these equality-stratum neighborhoods. -/
theorem function_nonincrease (S : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (C : S.Z.IdealSheafData) (hC : LocallyConstantCenter S C) :
    ∀ x : C.strictTransform S.i,
      le (function (strictTransformMap S.i C.blowupMap C.support.compl ≫
          C.blowupMap ≫ S.p) x)
        (function (S.i ≫ S.p)
          (strictTransformToSource S.i C.blowupMap C.support.compl x)) := by
  sorry

/-- No infinite strict drops among levels encountered along a fixed initial admissible
blowup history. Source: BMT 6.1(4); BM 1997, Corollary 3.20 and Lemma 9.3
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: `lem-trf-jet-diagram-hilbert-control` gives the descending-chain condition for diagrams
in a fixed number of ambient variables. Cover the initial finite-type scheme by finitely
many smooth ambient charts. Blowup charts preserve their dimension, so the same finite
variable bound holds at every subsequent stage, rather than only for the initial image.
`lem-trf-smooth-center-blowup-geometry` preserves the smooth ambient and reduced strict
transform, so the diagram bound reapplies throughout the history. -/
theorem function_no_infinite_drops (S : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (history : ℕ → Embedded (ULift.{u} ℚ)) (hstart : history 0 = S)
    (hsteps : ∀ n : ℕ, BlowupTransition (history n) (history (n + 1)))
    (values : ℕ → ℕ → ℕ)
    (hvalues : ∀ n : ℕ, ∃ x : (history n).X,
      function ((history n).i ≫ (history n).p) x = values n) :
    ¬ ∀ n : ℕ, lt (values (n + 1)) (values n) := by
  sorry

/-- Every point, regular or singular, has a local presentation with all the finite-test
conditions, not just initial set equality. Source: BMT 6.2; BM 1997, Theorems 9.4 and 9.6
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: Shrink to the local maximal equality stratum using the numerical theorem.
`lem-trf-regular-hilbert-coefficient-data` supplies regular coefficients with positive weights.
Choose a common positive multiple b and take the sum of their b/weight powers. For an empty
coefficient list take b = 1 and the zero ideal. This is a real coefficient-ideal construction.
Noetherian finite-generation and relation-module finiteness give coherence via
`lem-trf-noetherian-submodule-finitely-presented`. The initial equality criterion of
`lem-trf-formal-coefficient-transform-criterion` identifies its cosupport with the equality
stratum. Under admissible blowup the coefficient transform c' = e^(-weight) sigma*c makes
the combined ideal transform by e^(-b). The same criterion identifies equality points of
the strict transform. For exceptional-intersection blowups use ordinary pullback of X,N,I;
for line products use ordinary pullback and sum the level, appending the line zero section.
Induct on test length, carrying transversality of the ordered boundary to N. The boundary
starts empty and every new exceptional equation or line coordinate is a coordinate on N.
Thus both cosupports coincide and allow exactly the same next centers at every finite stage.
These are steps 3--5 of the node, using `lem-trf-jet-diagram-hilbert-control` as well. -/
theorem local_presentations {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [IsImmersion i] [IsReduced X]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)] :
    ∀ x : X, LocalPresentationAt p i x := by
  sorry

/-- The local presentation can be taken in a minimal smooth local envelope. Source: BMT 6.2;
`lem-trf-smooth-embedding-etale-comparison` and node proof step 6
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: In an étale chart choose independent linear equations in the embedding ideal and
complete their differentials to ambient coordinates. Their zero locus is a smooth closed
local envelope with defining ideal of X contained in the square of the ambient maximal
ideal. This is the minimal-envelope part of `lem-trf-smooth-embedding-etale-comparison`.
Apply the coefficient construction and the finite-test induction of node proof steps 3--5
inside that envelope. The level is intrinsic under the pointed étale localization. -/
theorem local_minimal_presentations {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [IsImmersion i] [IsReduced X]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)] (x : X) :
    ∃ (E : Scheme.{u}) (e : E ⟶ Z) (S : Embedded (ULift.{u} ℚ))
      (j : S.Z ⟶ E) (g : S.X ⟶ X) (a : S.X) (M : Marked S),
      Etale e ∧ IsClosedImmersion j ∧ j ≫ e ≫ p = S.p ∧
      IsPullback g S.i i (j ≫ e) ∧ Etale g ∧ g a = x ∧ MinimalAt S a ∧
      S.level = function (i ≫ p) x ∧ Presents M := by
  sorry

/-- At a singular point of a minimal smooth envelope a presentation becomes equivalent,
étale locally, to one on the full envelope of exactly its positive marked order.
Source: BMT 6.2; transverse suspension in the node's proof step 6
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: `lem-trf-smooth-embedding-etale-comparison` supplies minimal envelopes and transverse
retraction coordinates. At a singular point the Taylor ideal is nonzero, so the coefficient
construction from `lem-trf-regular-hilbert-coefficient-data` has an essential transverse
variable. Apply `lem-trf-marked-ideal-transverse-suspension`: the explicit ideal
(z_1^b,...,z_r^b) + p*I has the same tests on the full envelope and, because r is positive,
has order exactly b throughout cosupport. For a regular codimension-zero germ the ideal
zero with marking one still presents the level, but has infinite order; no finite-order
assertion is made there. -/
theorem presentation_full_maximalOrder (S : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (x : S.X) (hminimal : MinimalAt S x)
    (hsingular : ¬ IsRegularLocalRing (S.X.presheaf.stalk x))
    (hlevel : S.level = function (S.i ≫ S.p) x) (M : Marked S) (hM : Presents M) :
    ∃ (T : Embedded (ULift.{u} ℚ)) (f : T.Z ⟶ S.Z) (a : T.X) (g : T.X ⟶ S.X)
      (P Q : Marked T),
      Etale f ∧ Pullback f 0 ∧ IsPullback g T.i S.i f ∧ g a = x ∧
      MarkedPullback f M P ∧ Presents Q ∧ Equivalent P Q ∧ FullMaximalOrder Q := by
  sorry

/-- Coefficient choices and minimal envelopes give the same presentation class up to common
pointed étale comparison. The earlier-center lists are the images of the same ordered
intrinsic center ideals, so the comparison retains them. Source: BM 1997, Remarks 6.3 and
Definition 6.4; BMT 6.2--6.3 (blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: On one envelope the finite-test criterion of node proof step 5 identifies the tests
of any two coefficient constructions. For two minimal envelopes,
`lem-trf-smooth-embedding-etale-comparison` supplies a common étale comparison identifying
their copies of X. Pull the finite-test criterion back there using
`lem-trf-formal-coefficient-transform-criterion`. Cartesian comparison pulls every specified
earlier intrinsic center ideal back identically, and induction on the preceding admissible
history identifies the induced ordered boundary and subsequent tests. This is the intrinsic
history dependence in proof step 8, not a uniqueness assertion about coefficient ideals. -/
theorem presentation_intrinsic_comparison (S T : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (e : S.X ≅ T.X) (he : e.hom ≫ T.i ≫ T.p = S.i ≫ S.p)
    (x : S.X) (hS : MinimalAt S x) (hT : MinimalAt T (e.hom x))
    (hlevelS : S.level = function (S.i ≫ S.p) x) (hlevelT : T.level = S.level)
    (earlier : List S.X.IdealSheafData)
    (M : Marked S) (P : Marked T) (hM : Presents M) (hP : Presents P) :
    ∃ c : CommonComparison S T x (e.hom x) e
      (earlier.map (fun I ↦ I.map S.i))
      (earlier.map (fun I ↦ I.map (e.hom ≫ T.i))),
      ∃ M' P' : Marked c.W,
        MarkedPullback c.f M M' ∧ MarkedPullback c.g P P' ∧ Equivalent M' P' := by
  sorry

/-- After any common étale identification that retains the ordered earlier center ideals
and their induced boundary, the transformed presentation class is independent of coefficient
data. Earlier divisors are history data, while the newly started test boundary is empty.
Source: BM 1997, Remarks 6.3 and Definition 6.4; BMT 6.2--6.3
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: Pull the two presentations back to the supplied common comparison, retaining every
earlier center ideal and the induced boundary via its cartesian squares. The retaining-level
criterion of `lem-trf-formal-coefficient-transform-criterion` identifies both transformed
cosupports at every finite test stage, including their permissible centers. Induct through
any preceding admissible history to retain those identifications. This is node proof step 8.
-/
theorem presentation_history_comparison (S T : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    [IsReduced T.X] [LocallyOfFiniteType (T.i ≫ T.p)] [QuasiCompact (T.i ≫ T.p)]
    (x : S.X) (y : T.X) (e : S.X ≅ T.X)
    (earlierS : List S.Z.IdealSheafData) (earlierT : List T.Z.IdealSheafData)
    (c : CommonComparison S T x y e earlierS earlierT)
    (M : Marked S) (P : Marked T) (hM : Presents M) (hP : Presents P) :
    ∃ M' P' : Marked c.W,
      MarkedPullback c.f M M' ∧ MarkedPullback c.g P P' ∧ Equivalent M' P' := by
  sorry

/-- Numerical smooth-pullback formula, including dimension zero and arbitrary points.
Source: BMT 6.3 (blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: `sbc-thm-etale-local-normal-form` expresses the map locally as an étale map followed
by affine-space projection. The Taylor-module counts of `lem-trf-jet-diagram-hilbert-control`
are unchanged by étale localization; adjoining r free variables applies summation r times.
The first nonzero coefficient of the difference of two sequences remains the first nonzero
coefficient of its sum, with the same sign, so this also preserves equality strata. -/
theorem function_smooth_pullback {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of (ULift.{u} ℚ))) (f : Y ⟶ X) (r : ℕ)
    [IsReduced X] [LocallyOfFiniteType p] [QuasiCompact p]
    [SmoothOfRelativeDimension r f] :
    ∀ y : Y, function (f ≫ p) y = (summation^[r]) (function p (f y)) := by
  sorry

/-- Presentations commute with local smooth pullback on each relative-dimension piece,
including restrictions (open immersions have relative dimension zero). Source: BMT 6.3
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: Apply the numerical smooth-pullback formula. Pull back the coefficient construction
and use `lem-trf-formal-coefficient-transform-criterion` in the pulled-back étale coordinates.
Its division identities survive smooth pullback and the level becomes the r-fold sum.
The finite-test induction of proof step 5 applies again. Restriction uses precisely the
same formulas on a smaller open neighborhood. This is proof step 7 and the restriction
part of step 8; it does not equate unsummed levels under positive-dimensional smooth maps. -/
theorem presentation_smooth_pullback (S T : Embedded (ULift.{u} ℚ))
    [IsReduced S.X] [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (f : T.Z ⟶ S.Z) (r : ℕ) (hf : Pullback f r)
    (M : Marked S) (hM : Presents M) :
    (∃ P : Marked T, MarkedPullback f M P) ∧ T.locus = f ⁻¹' S.locus ∧
      ∀ P : Marked T, MarkedPullback f M P → Presents P := by
  sorry

/-- Emptying a maximum presentation's cosupport removes that retained maximum from the
strict transform. Source: BMT 6.3, first paragraph
(blueprint: lem-trf-hilbert-samuel-local-presentations).

Proof: Induct on the specified admissible history. Step 5 of the node identifies the
retaining-level locus with the transformed cosupport. Step 4 gives nonincrease at every
admissible blowup. If the final cosupport is empty, no point has the retained maximum;
nonincrease rules out a larger value. The descending-chain assertion applies in the same
ambient dimension and forbids infinitely many strict drops. This conditional statement,
proof step 9, makes no assertion of existence of a completed resolution tower. -/
theorem presentation_empty_maximum (S : Embedded (ULift.{u} ℚ))
    (M : Marked S) (hM : Presents M)
    (hmax : ∀ x : S.X, le (function (S.i ≫ S.p) x) S.level)
    (n : ℕ) (history : Fin (n + 1) → Embedded (ULift.{u} ℚ))
    (marks : ∀ j : Fin (n + 1), Marked (history j))
    (hstart : history 0 = S) (hstartMark : HEq (marks 0) M)
    (steps : ∀ j : Fin n, Step (history j.castSucc) (history j.succ))
    (hkinds : ∀ j : Fin n, (steps j).kind = .admissibleBlowup)
    (hadmissible : ∀ j : Fin n, (steps j).Admissible (history j.castSucc).locus)
    (htransforms : ∀ j : Fin n,
      (steps j).Transforms (marks j.castSucc) (marks j.succ))
    (hempty : (marks (Fin.last n)).cosupport = ∅) :
    ∀ x : (history (Fin.last n)).X,
      lt (function ((history (Fin.last n)).i ≫ (history (Fin.last n)).p) x) S.level := by
  sorry

end AlgebraicGeometry.HilbertSamuel
