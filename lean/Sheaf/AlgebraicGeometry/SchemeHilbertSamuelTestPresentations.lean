/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelPresentation
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Logic.Relation
public import Mathlib.Algebra.Field.ULift

import Sheaf.AlgebraicGeometry.CoordinateSubspaceBlowupCharts
import Sheaf.AlgebraicGeometry.DiagonalTaylorFaithfulFlatness
import Sheaf.TraceFormula.EtaleLocalRingFlatness
import Sheaf.AlgebraicGeometry.ExtendedHilbertLocalUpperBound
import Sheaf.AlgebraicGeometry.FormalCoefficientTransformCriterion
import Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus
import Sheaf.AlgebraicGeometry.JetDiagramHilbertControl
import Sheaf.AlgebraicGeometry.MarkedControlledBlowupCharts
import Sheaf.AlgebraicGeometry.MarkedIdealTransverseSuspension
import Sheaf.AlgebraicGeometry.PermissibleCoordinateChart
import Sheaf.AlgebraicGeometry.MinimalSmoothEnvelopeComparison
import Sheaf.RingTheory.SmoothLocalTangentConeExtension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Length
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm

/-! # Hilbert--Samuel test presentations with nilpotents

Source: Bierstone--Milman--Temkin, arXiv:0905.3580v1, sections 6.1--6.3, pp.13--15;
BM 1997, Chapter III; BM 2008, section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

The actual scheme, including its nilpotents, is used throughout. The declarations state the
numerical properties, local existence, finite tests, full-envelope presentation, intrinsic
comparison, smooth pullback and disappearance of an emptied level.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.HilbertSamuel

/-- Finite image and closed lexicographic upper sets for the actual scheme.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 1. Apply [lem-trf-jet-diagram-hilbert-control] to affine charts of $X$, with their actual
quotient algebras, not their reductions. It identifies $H_X$ with finite principal-parts fibre
dimensions and Taylor-diagram counting functions, and gives locally finitely many diagrams.
[lem-trf-extended-hilbert-local-upper-bound] gives an open neighbourhood of each $a$ on which
every value is pointwise at most $H_X(a)$. For any threshold $v$, the strict sublevel $H_X<v$ is
the union of these neighbourhoods for its points; hence the upper level set is closed. Finite
type gives a finite affine cover by [def-weil-finite-type-morphism]; a finite union of the
finite local value sets is finite. All these cited statements allow nilpotents and nonclosed
points. -/
theorem scheme_function_local_finite_upperSemicontinuous {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] [IsImmersion i]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)] :
    (∀ (x : X) (n : ℕ), Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (n + 1)) < ⊤) ∧
    (Set.range (function (i ≫ p))).Finite ∧
    (∀ H : ℕ → ℕ, IsClosed {x : X | le H (function (i ≫ p) x)}) := by
  sorry

/-- Nonincrease under a smooth locally constant-level center on the strict transform.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 3. For a smooth center in this equality locus, [lem-trf-marked-controlled-blowup-charts]
supplies smooth supports, ordered transverse boundary and the regular controlled transform.
[lem-trf-formal-coefficient-transform-criterion] applies to the actual defining ideal with no
reducedness assumption: $H'\le H_X(a)$; equality is exactly the transformed coefficient order
locus, with the same five conditions. Its coefficients are
$c'_{i\gamma}=e^{-m_{i\gamma}}\sigma^*c_{i\gamma}$. Therefore
$\sum((c'_{i\gamma})^{b/m_{i\gamma}})=e^{-b}\sigma^*I$, term by term. Off the center use the
same chart statement, which says the marked pair is unchanged. Repeat the argument at each point
of any smooth locally constant-$H_X$ center to obtain the claimed nonincrease over that center. -/
theorem scheme_function_nonincrease (S : Embedded (ULift.{u} ℚ))
    [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (C : S.Z.IdealSheafData) (hC : LocallyConstantCenter S C) :
    ∀ x : C.strictTransform S.i,
      le (function (strictTransformMap S.i C.blowupMap C.support.compl ≫
          C.blowupMap ≫ S.p) x)
        (function (S.i ≫ S.p)
          (strictTransformToSource S.i C.blowupMap C.support.compl x)) := by
  sorry

/-- No consecutive strict drops in a permissible blowup history.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 11. Fix a finite smooth coordinate cover near the initial $X$ and let $d$ bound its
coordinate dimensions. Smooth-center blowups have local coordinate-subspace models by
[lem-trf-smooth-pair-blowup-local-models]; [lem-trf-coordinate-subspace-blowup-charts] shows
that each chart has the same number of coordinates. Thus all strict transforms reached by
permissible blowups have local smooth envelopes of dimension at most $d$, without any assertion
of reducedness. [lem-trf-jet-diagram-hilbert-control] expresses every reached level as a diagram
counting function in $e\le d$ variables. Pad a diagram $D\subset\mathbf N^e$ to $d$ variables by
including every exponent with a nonzero last coordinate: its complement consists of $(\alpha,0)$
for $\alpha\notin D$, so the counting function is unchanged. The fixed-$d$ descending-chain
assertion of the same node rules out an infinite strict descent, including subsequences
separated by arbitrary plateaus. Line tests sum the reference level; this termination assertion
concerns retained levels of permissible blowup histories from the fixed finite-dimensional
input. -/
theorem scheme_function_no_infinite_drops (S : Embedded (ULift.{u} ℚ))
    [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (history : ℕ → Embedded (ULift.{u} ℚ)) (hstart : history 0 = S)
    (hsteps : ∀ n : ℕ, BlowupTransition (history n) (history (n + 1)))
    (values : ℕ → ℕ → ℕ)
    (hvalues : ∀ n : ℕ, ∃ x : (history n).X,
      function ((history n).i ≫ (history n).p) x = values n) :
    ¬ ∀ n : ℕ, lt (values (n + 1)) (values n) := by
  sorry

/-- Every point has a presentation for every finite test, with nilpotents retained.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 2. Apply [lem-per-nonreduced-regular-hilbert-coefficients] at $a$, with $Q\ge\max d_i-1$.
On its one smooth support $N$ set $m_{i\gamma}=d_i-|\gamma|$ and choose a positive common
multiple $b$ of the finitely many positive weights; put $I=\sum(c_{i\gamma}^{b/m_{i\gamma}})$.
For an empty list take $(I,b)=(0,1)$. [lem-trf-logarithmic-differential-transform] gives
$\operatorname{ord}I=\min (b/m_{i\gamma})\operatorname{ord}c_{i\gamma}$, so cosupport is exactly
the coefficient order locus. [lem-trf-coefficient-order-hilbert-equality] identifies that locus
with $H_X=H_X(a)$ after shrinking. Its block hypotheses at $a$ are the supplied five conditions.
It also asks for the vertex-derivative and forbidden-derivative conditions (4),(5) at every
point $y\in N$, while the datum gives them only on its coefficient order locus. Shrink $N$ to an
irreducible affine neighbourhood of $a$; this is possible because its local rings are regular,
hence domains, by [lem-weil-pbc-smooth-scheme-over-field-regular]. On that neighbourhood the
Jacobian determinants in (4), regular functions that are units at $a$, remain units. Each
membership in (4),(5) says that certain coefficient functions $c_{i\gamma}$ have zero Taylor
expansion. At $a$ the Taylor map is faithfully flat by
[lem-trf-implicit-taylor-coordinate-calculus], so their germs are zero. Hence these functions
vanish on the irreducible neighbourhood, and the memberships hold at every $y$. The finite ideal
is coherent by [pqf-lem-coherent-ft-locnoeth], since $N$ is locally Noetherian by
[lem-weil-pbc-smooth-scheme-over-field-regular].
Step 3. For a smooth center in this equality locus, [lem-trf-marked-controlled-blowup-charts]
supplies smooth supports, ordered transverse boundary and the regular controlled transform.
[lem-trf-formal-coefficient-transform-criterion] applies to the actual defining ideal with no
reducedness assumption: $H'\le H_X(a)$; equality is exactly the transformed coefficient order
locus, with the same five conditions. Its coefficients are
$c'_{i\gamma}=e^{-m_{i\gamma}}\sigma^*c_{i\gamma}$. Therefore
$\sum((c'_{i\gamma})^{b/m_{i\gamma}})=e^{-b}\sigma^*I$, term by term. Off the center use the
same chart statement, which says the marked pair is unchanged. Repeat the argument at each point
of any smooth locally constant-$H_X$ center to obtain the claimed nonincrease over that center.
Step 4. Set up induction on finite tests, retaining the bound $H_j\le
L_j=\Lambda^{\ell_j}H_X(a)$, equality exactly at cosupport, the five coefficient conditions
there, and the ordered transverse boundary. Store full supported multiplication identities over
every source point in cosupport. In a permissible chart meeting $N'$, write $Y_h=e$,
$Y_k=e(\eta_k+U_k)$ and $Z=eZ'$. [lem-trf-coordinate-blowup-division-generators] gives
generators $f_i'=e^{-d_i}\sigma^*f_i$ of the actual saturated ideal. For $Z^\beta f_i=\sum
q_hf_h$, put $v=\operatorname{ord}_{(Y,Z)}(Z^\beta f_i)$, so $v\ge d_i+|\beta|$. Its filtration
estimate makes $e^{d_h-d_i-|\beta|}\sigma^*q_h$ regular and gives supported identities for
$(Z')^\beta f_i'$. The supports restrict only $Z$, so mixing $Y$ does not change them.
Differentiation gives $g_j'=e^{-1}\sigma^*g_j$ and the same transverse Jacobians. The forbidden
derivative memberships persist because the coordinate ideals $(Z'^\ell)$ are $e$-saturated. On
$e=0$ the pure transverse degree-$d_i$ forms remain the source forms. These statements retain
certificates even over points whose order dropped. Taylor compatibility with regular models is
[lem-trf-implicit-taylor-coordinate-calculus].
Step 5. A line test appends a free coefficient variable.
[lem-trf-formal-coefficient-transform-criterion] and [lem-trf-jet-diagram-hilbert-control] give
ordinary coefficient pullback and $L_{j+1}=\Lambda L_j$, retaining all certificates. For
sequences whose first differing index is $q$, partial sums agree below $q$ and their difference
at $q$ is the original difference. Hence summation preserves and reflects lexicographic
comparisons; it is injective since $F(0)=\Lambda F(0)$ and $F(q+1)=\Lambda F(q+1)-\Lambda F(q)$.
This proves the bound and equality assertions for line tests, including nonclosed points. The
new zero section is a free coefficient-coordinate boundary; the existing boundary remains
ordered.
Step 6. For an exceptional-intersection test first compute the auxiliary ordinary pullback
prescribed by [def-trf-hilbert-samuel-presentation]. Its coordinate charts replace two
coefficient parameters by $W_u=e,W_v=e(\xi+V)$, by [lem-trf-permissible-coordinate-chart]. Trace
the two boundary germs backwards. Before any permissible exceptional divisor they are free
variables over an earlier $X$, so the jet free-variable formula applies. Otherwise take the last
permissible blowup affecting the germ. Step 4 stored whole-series certificates over its
cosupport source point, including lower-level points on its exceptional fibre. Subsequent line
and boundary substitutions preserve those identities; the pure transverse forms remain the
source forms because the transverse variables are not translated. Apply
[lem-per-hilbert-boundary-supported-certificates] at the new points of $N$: equality holds
exactly at the new coefficient order locus, with all five conditions there, and strict drops
cannot return to $L_j$. Outside $N$, a first nonzero essential transverse direction makes one of
the stored vertex derivatives of order $d_i-1$ a unit; the earlier retained blocks have zero
direction. Thus its first dropping block contributes a nonzero remainder independent of the
earlier prefix columns, giving strict lexicographic drop by the homogeneous-division criterion
[lem-trf-homogeneous-continuous-formal-division]. For the actual scheme take saturation by $e$:
the certificate node says saturation leaves an equality germ unchanged and cannot raise a
strictly smaller function. Keep the auxiliary model and its quotient onto the actual model
through subsequent substitutions and saturations; at any new candidate equality point its
coefficient certificates make $e$ injective, so the auxiliary and strict germs coincide there.
Hence both conventions give the same retaining-level loci. This is a prefix dimension count, not
invariance at lower-level images.
Step 7. Steps 3--6 close the induction on every finite prefix. The order formulas of
[lem-trf-logarithmic-differential-transform] identify the coefficient order locus with the
cosupport of the prescribed transformed $I$ in each case. At an equality point all five
conditions are available for the next permissible test;
[lem-trf-extended-hilbert-local-upper-bound] supplies its pointwise upper neighbourhood if
needed. The two equal loci allow exactly the same next smooth centers, and normal crossings is
the same condition on the same ordered ambient boundary. Thus all finite-depth predicates of
[def-trf-hilbert-samuel-presentation] hold, with one initial chart and empty boundary. An etale
chart maps onto an open neighbourhood of $a$ by [lem-weil-pbc-etale-morphism-open-map];
replacing the base by that image makes it surjective. Empty cosupport has empty equality locus,
so removes the level. -/
theorem scheme_local_presentations {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] [IsImmersion i]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)] :
    ∀ x : X, LocalPresentationAt p i x := by
  sorry

/-- The presentation can be chosen in a minimal smooth envelope.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 8. Choose a minimal smooth envelope using [lem-trf-smooth-embedding-etale-comparison].
Apply steps 2--7 there. If its coefficient support has codimension $r=0$, no transverse variable
exists. A nonempty vertex list would then have degree zero, making a generator a unit in a
proper defining ideal. Thus the list is empty and the Taylor ideal is zero.
[lem-trf-diagonal-taylor-faithful-flatness] and [lem-weil-pbc-faithfully-flat-ideal-contraction]
first contract the zero ideal to the localized ambient chart. The original ambient stalk maps
faithfully flatly to that chart stalk: it is flat by [lem-trf-etale-local-ring-flatness] and
local, hence faithfully flat by [lem-weil-pbc-flat-local-hom-faithfully-flat]. A second ideal
contraction makes the original defining germ zero, so $X$ has the smooth ambient local ring,
regular by [lem-weil-pbc-smooth-scheme-over-field-regular]. At a nonregular germ, therefore
$r>0$. In retraction coordinates $p:Z\to N$, take $J=(z_1^b,\ldots,z_r^b)+p^*I$.
[lem-trf-marked-ideal-transverse-suspension] gives the same finite tests and order exactly $b$
throughout cosupport on the whole envelope. At a regular germ the empty coefficient construction
still works, with infinite order for its zero ideal and no finite-order claim. -/
theorem scheme_local_minimal_presentations {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] [IsImmersion i]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)] (x : X) :
    ∃ (E : Scheme.{u}) (e : E ⟶ Z) (S : Embedded (ULift.{u} ℚ))
      (j : S.Z ⟶ E) (g : S.X ⟶ X) (a : S.X) (M : Marked S),
      Etale e ∧ IsClosedImmersion j ∧ j ≫ e ≫ p = S.p ∧
      IsPullback g S.i i (j ≫ e) ∧ Etale g ∧ g a = x ∧ MinimalAt S a ∧
      S.level = function (i ≫ p) x ∧ Presents M := by
  sorry

/-- A nonregular minimal germ has an equivalent full-envelope maximal-order presentation.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 8. Choose a minimal smooth envelope using [lem-trf-smooth-embedding-etale-comparison].
Apply steps 2--7 there. If its coefficient support has codimension $r=0$, no transverse variable
exists. A nonempty vertex list would then have degree zero, making a generator a unit in a
proper defining ideal. Thus the list is empty and the Taylor ideal is zero.
[lem-trf-diagonal-taylor-faithful-flatness] and [lem-weil-pbc-faithfully-flat-ideal-contraction]
first contract the zero ideal to the localized ambient chart. The original ambient stalk maps
faithfully flatly to that chart stalk: it is flat by [lem-trf-etale-local-ring-flatness] and
local, hence faithfully flat by [lem-weil-pbc-flat-local-hom-faithfully-flat]. A second ideal
contraction makes the original defining germ zero, so $X$ has the smooth ambient local ring,
regular by [lem-weil-pbc-smooth-scheme-over-field-regular]. At a nonregular germ, therefore
$r>0$. In retraction coordinates $p:Z\to N$, take $J=(z_1^b,\ldots,z_r^b)+p^*I$.
[lem-trf-marked-ideal-transverse-suspension] gives the same finite tests and order exactly $b$
throughout cosupport on the whole envelope. At a regular germ the empty coefficient construction
still works, with infinite order for its zero ideal and no finite-order claim. -/
theorem scheme_presentation_full_maximalOrder (S : Embedded (ULift.{u} ℚ))
    [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (x : S.X) (hminimal : MinimalAt S x)
    (hsingular : ¬ IsRegularLocalRing (S.X.presheaf.stalk x))
    (hlevel : S.level = function (S.i ≫ S.p) x) (M : Marked S) (hM : Presents M) :
    ∃ (T : Embedded (ULift.{u} ℚ)) (f : T.Z ⟶ S.Z) (a : T.X) (g : T.X ⟶ S.X)
      (P Q : Marked T),
      Etale f ∧ Pullback f 0 ∧ IsPullback g T.i S.i f ∧ g a = x ∧
      MarkedPullback f M P ∧ Presents Q ∧ Equivalent P Q ∧ FullMaximalOrder Q := by
  sorry

/-- The class is intrinsic under minimal-envelope and coefficient choices.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 9. For two minimal envelopes use [lem-trf-smooth-embedding-etale-comparison] to identify
the pointed closed pairs on a common etale neighbourhood, respecting the specified earlier
intrinsic ideals. At depth zero both presentations have the same intrinsic equality locus by
step 7. Induct on depth: the same locus and ordered boundary give the same next centers, and the
same geometric test transforms the same embedded scheme; step 7 identifies both next cosupports
with its retaining-level locus. This proves equivalence for arbitrary coefficient choices and
their suspensions. The same argument starts at any identified transformed germ in a finite
permissible history, retaining the ordered earlier ideals even at intrinsic identity stages.
Exceptional birth data is the ordered data induced by those same centers; it is not inserted
into the freshly empty test boundary. -/
theorem scheme_presentation_intrinsic_comparison (S T : Embedded (ULift.{u} ℚ))
    [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
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

/-- Comparison retains the ordered earlier intrinsic ideals through finite histories.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 9. For two minimal envelopes use [lem-trf-smooth-embedding-etale-comparison] to identify
the pointed closed pairs on a common etale neighbourhood, respecting the specified earlier
intrinsic ideals. At depth zero both presentations have the same intrinsic equality locus by
step 7. Induct on depth: the same locus and ordered boundary give the same next centers, and the
same geometric test transforms the same embedded scheme; step 7 identifies both next cosupports
with its retaining-level locus. This proves equivalence for arbitrary coefficient choices and
their suspensions. The same argument starts at any identified transformed germ in a finite
permissible history, retaining the ordered earlier ideals even at intrinsic identity stages.
Exceptional birth data is the ordered data induced by those same centers; it is not inserted
into the freshly empty test boundary. -/
theorem scheme_presentation_history_comparison (S T : Embedded (ULift.{u} ℚ))
    [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    [LocallyOfFiniteType (T.i ≫ T.p)] [QuasiCompact (T.i ≫ T.p)]
    (x : S.X) (y : T.X) (e : S.X ≅ T.X)
    (earlierS : List S.Z.IdealSheafData) (earlierT : List T.Z.IdealSheafData)
    (c : CommonComparison S T x y e earlierS earlierT)
    (M : Marked S) (P : Marked T) (hM : Presents M) (hP : Presents P) :
    ∃ M' P' : Marked c.W,
      MarkedPullback c.f M M' ∧ MarkedPullback c.g P P' ∧ Equivalent M' P' := by
  sorry

/-- The extended level is summed by the relative dimension under a smooth morphism.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 10. For a smooth intrinsic map $Y\to X$ use [sbc-thm-etale-local-normal-form] to factor it
locally as etale followed by a projection from $X\times\mathbf A^r$. Use a local embedding of
$X$ and its ambient product to compute the presentation upstairs.
[lem-trf-jet-diagram-hilbert-control] gives $H_Y=\Lambda^rH_X$;
[lem-trf-smooth-local-tangent-cone-extension] gives $h_y=\Lambda^s h_x$ for the fibre-local
dimension $s$ by counting polynomial monomials in its graded isomorphism and summing
graded-piece lengths using [lem-weil-pbc-length-additive-short-exact]. The coefficient data pull
back by [lem-trf-formal-coefficient-transform-criterion]. Repeating the induction of steps 3--7
for these data treats all next centers upstairs, without requiring them to descend.
Equal-dimensional full-envelope comparisons are therefore equivalences by step 9; for different
dimensions apply the same argument after adjoining the smooth parameters. The ideal-pullback
clause of the envelope comparison retains earlier ideals, so the argument applies at every stage
of the finite histories. -/
theorem scheme_function_smooth_pullback {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of (ULift.{u} ℚ))) (f : Y ⟶ X) (r : ℕ)
    [LocallyOfFiniteType p] [QuasiCompact p]
    [SmoothOfRelativeDimension r f] :
    ∀ y : Y, function (f ≫ p) y = (summation^[r]) (function p (f y)) := by
  sorry

/-- Smooth pullback carries presentations to presentations of the summed level.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 10. For a smooth intrinsic map $Y\to X$ use [sbc-thm-etale-local-normal-form] to factor it
locally as etale followed by a projection from $X\times\mathbf A^r$. Use a local embedding of
$X$ and its ambient product to compute the presentation upstairs.
[lem-trf-jet-diagram-hilbert-control] gives $H_Y=\Lambda^rH_X$;
[lem-trf-smooth-local-tangent-cone-extension] gives $h_y=\Lambda^s h_x$ for the fibre-local
dimension $s$ by counting polynomial monomials in its graded isomorphism and summing
graded-piece lengths using [lem-weil-pbc-length-additive-short-exact]. The coefficient data pull
back by [lem-trf-formal-coefficient-transform-criterion]. Repeating the induction of steps 3--7
for these data treats all next centers upstairs, without requiring them to descend.
Equal-dimensional full-envelope comparisons are therefore equivalences by step 9; for different
dimensions apply the same argument after adjoining the smooth parameters. The ideal-pullback
clause of the envelope comparison retains earlier ideals, so the argument applies at every stage
of the finite histories. -/
theorem scheme_presentation_smooth_pullback (S T : Embedded (ULift.{u} ℚ))
    [LocallyOfFiniteType (S.i ≫ S.p)] [QuasiCompact (S.i ≫ S.p)]
    (f : T.Z ⟶ S.Z) (r : ℕ) (hf : Pullback f r)
    (M : Marked S) (hM : Presents M) :
    (∃ P : Marked T, MarkedPullback f M P) ∧ T.locus = f ⁻¹' S.locus ∧
      ∀ P : Marked T, MarkedPullback f M P → Presents P := by
  sorry

/-- Empty cosupport after a permissible history removes the retained maximum.
Source: BMT 6.1--6.3, BM 1997 Chapter III and BM4 section 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof:
Step 7. Steps 3--6 close the induction on every finite prefix. The order formulas of
[lem-trf-logarithmic-differential-transform] identify the coefficient order locus with the
cosupport of the prescribed transformed $I$ in each case. At an equality point all five
conditions are available for the next permissible test;
[lem-trf-extended-hilbert-local-upper-bound] supplies its pointwise upper neighbourhood if
needed. The two equal loci allow exactly the same next smooth centers, and normal crossings is
the same condition on the same ordered ambient boundary. Thus all finite-depth predicates of
[def-trf-hilbert-samuel-presentation] hold, with one initial chart and empty boundary. An etale
chart maps onto an open neighbourhood of $a$ by [lem-weil-pbc-etale-morphism-open-map];
replacing the base by that image makes it surjective. Empty cosupport has empty equality locus,
so removes the level.
Step 11. Fix a finite smooth coordinate cover near the initial $X$ and let $d$ bound its
coordinate dimensions. Smooth-center blowups have local coordinate-subspace models by
[lem-trf-smooth-pair-blowup-local-models]; [lem-trf-coordinate-subspace-blowup-charts] shows
that each chart has the same number of coordinates. Thus all strict transforms reached by
permissible blowups have local smooth envelopes of dimension at most $d$, without any assertion
of reducedness. [lem-trf-jet-diagram-hilbert-control] expresses every reached level as a diagram
counting function in $e\le d$ variables. Pad a diagram $D\subset\mathbf N^e$ to $d$ variables by
including every exponent with a nonzero last coordinate: its complement consists of $(\alpha,0)$
for $\alpha\notin D$, so the counting function is unchanged. The fixed-$d$ descending-chain
assertion of the same node rules out an infinite strict descent, including subsequences
separated by arbitrary plateaus. Line tests sum the reference level; this termination assertion
concerns retained levels of permissible blowup histories from the fixed finite-dimensional
input. -/
theorem scheme_presentation_empty_maximum (S : Embedded (ULift.{u} ℚ))
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


/-- A presentation chart is surjective onto an open ambient neighbourhood, where the specified
level is maximal. Source: BMT 6.2; BM 1997 Chapter III
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof: Apply the coefficient construction and finite-test induction of node Steps 2--7 to the
actual defining ideal. Step 1 gives an open neighbourhood on which the level is maximal.
An etale map is open by `lem-weil-pbc-etale-morphism-open-map`. Restrict its target to its open
image containing the specified point. It is then surjective. All tests and coherence restrict
along this open immersion, and the boundary starts empty. -/
theorem scheme_local_presentations_surjective {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] [IsImmersion i]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)] (x : X) :
    ∃ (V : Z.Opens) (_ : i x ∈ V) (S : Embedded (ULift.{u} ℚ))
      (f : S.Z ⟶ V.toScheme) (g : S.X ⟶ X) (a : S.X) (M : Marked S),
      Etale f ∧ Function.Surjective f ∧ f ≫ V.ι ≫ p = S.p ∧
      IsPullback g S.i i (f ≫ V.ι) ∧ g a = x ∧
      S.level = function (i ≫ p) x ∧ Presents M ∧
      ∀ y : S.X, le (function (S.i ≫ S.p) y) S.level := by
  sorry

/-- A decreasing sequence of levels attained after arbitrary finite permissible histories from
one fixed input stabilizes, including subsequences separated by plateaus.
Source: BMT 6.1(4); BM 1997 Corollary 3.20
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof: Node Step 11 chooses finitely many smooth coordinate charts for the initial input,
with a common dimension bound d. The coordinate-subspace blowup charts preserve that bound.
`lem-trf-jet-diagram-hilbert-control` identifies every reached value with a diagram count in
at most d variables. Pad to d variables by putting all exponents with nonzero new coordinates
in the diagram; the count is unchanged. Its fixed-d descending-chain condition excludes an
infinite strict subsequence. A nonstabilizing decreasing sequence has such a subsequence,
including when its attained values come from different finite histories. No reducedness or
summation by line tests is assumed in this numerical termination assertion. -/
theorem scheme_function_reachable_stabilizes (S : Embedded (ULift.{u} ℚ))
    [LocallyOfFiniteType S.p] [QuasiCompact S.p]
    (values : ℕ → ℕ → ℕ)
    (hvalues : ∀ n : ℕ, ∃ T : Embedded (ULift.{u} ℚ),
      Relation.ReflTransGen BlowupTransition S T ∧
        ∃ x : T.X, function (T.i ≫ T.p) x = values n)
    (hdecreasing : ∀ n : ℕ, le (values (n + 1)) (values n)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → values n = values N := by
  sorry

/-- The raw local function is summed by the dimension of the local ring of the smooth fibre;
the fibre point is arbitrary and is not required to be closed.
Source: BMT 6.3; the associated-graded calculation of node Step 10
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof: `lem-trf-smooth-local-tangent-cone-extension` identifies the associated graded ring
with a polynomial ring in s variables over the residue-field extension of the source graded
ring. Count homogeneous monomials and sum the lengths of the graded pieces, using
`lem-weil-pbc-length-additive-short-exact`. The fibre is regular of local dimension s.
This proves h_y = Lambda^s h_x, independently of the relative transcendence degree. -/
theorem scheme_localFunction_smooth_pullback {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of (ULift.{u} ℚ)))
    [LocallyOfFiniteType p] [QuasiCompact p] (f : Y ⟶ X) [Smooth f]
    (x : X) (y : f.fiber x) :
    ∃ s : ℕ, ringKrullDim ((f.fiber x).presheaf.stalk y) = (s : WithBot ℕ∞) ∧
      localFunction Y (f.fiberι x y) = (summation^[s]) (localFunction X x) := by
  sorry

/-- Presentations retain all finite tests after any permissible finite history, with the
actual ordered transformed boundary. The test boundary is reset only for a new presentation.
Source: BMT 5.2 and 6.2; node Steps 3--7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof: Induct on the history length, using `PresentsThrough` at every larger initial depth.
Node Steps 3--6 give the controlled transform in the admissible case, ordinary pullback in
the other cases, and the summed level for a line. Step 7 identifies both loci and all next
centers at every depth. Quantifying over all depths gives the asserted finite-test property
at the final stage. This includes length zero and identity stages. -/
theorem scheme_presentation_finite_history (S : Embedded (ULift.{u} ℚ))
    (M : Marked S) (hM : Presents M) (n : ℕ)
    (history : Fin (n + 1) → Embedded (ULift.{u} ℚ))
    (marks : ∀ j : Fin (n + 1), Marked (history j))
    (hstart : history 0 = S) (hstartMark : HEq (marks 0) M)
    (steps : ∀ j : Fin n, Step (history j.castSucc) (history j.succ))
    (hadmissible : ∀ j : Fin n, (steps j).Admissible (history j.castSucc).locus)
    (htransforms : ∀ j : Fin n,
      (steps j).Transforms (marks j.castSucc) (marks j.succ)) :
    ∀ depth : ℕ, PresentsThrough depth (history (Fin.last n)) (marks (Fin.last n)) := by
  sorry

/-- At every exceptional-intersection test in a finite permissible history the strict and
ordinary-pullback conventions have the same ambient retaining-level locus.
Source: BMT 5.2 and 6.2; node Steps 4--7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof: Step 4 stores supported whole-series multiplication certificates even above points
whose order dropped. Step 6 traces the two labelled boundary germs back to their free-variable
stage or last permissible blowup. The boundary-supported certificates persist under their
substitutions. The saturation clause of `lem-per-hilbert-boundary-supported-certificates`
identifies the retained locus before and after exceptional saturation. The same argument
and Step 7 apply at each finite prefix, with nilpotents retained. Thus the auxiliary ordinary
pullback used in `Step` computes exactly the strict-transform retaining locus. -/
theorem scheme_exceptional_strict_retaining_locus (S : Embedded (ULift.{u} ℚ))
    [LocallyOfFiniteType S.p] [QuasiCompact S.p]
    (M : Marked S) (hM : Presents M)
    (hmax : ∀ x : S.X, le (function (S.i ≫ S.p) x) S.level)
    (n : ℕ) (history : Fin (n + 1) → Embedded (ULift.{u} ℚ))
    (marks : ∀ j : Fin (n + 1), Marked (history j))
    (hstart : history 0 = S) (hstartMark : HEq (marks 0) M)
    (steps : ∀ j : Fin n, Step (history j.castSucc) (history j.succ))
    (hadmissible : ∀ j : Fin n, (steps j).Admissible (history j.castSucc).locus)
    (htransforms : ∀ j : Fin n,
      (steps j).Transforms (marks j.castSucc) (marks j.succ))
    (T : Embedded (ULift.{u} ℚ)) (s : Step (history (Fin.last n)) T)
    (hexceptional : s.kind = .exceptionalIntersection) :
    (strictTransformMap (history (Fin.last n)).i s.π s.center.support.compl) ''
      {x | function (strictTransformMap (history (Fin.last n)).i s.π
        s.center.support.compl ≫ T.p) x = T.level} = T.locus := by
  sorry

/-- Empty transformed cosupport removes the level after arbitrary finite tests, including
line tests (which change the retained level) and exceptional tests.
Source: BMT 6.2--6.3; node Step 7
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof: Node Steps 3--7 give equality of the retaining-level locus with cosupport at every
finite prefix. If the latter is empty, no intrinsic point of the final scheme has that level,
since its image under the closed embedding would belong to cosupport. -/
theorem scheme_presentation_empty_level (S : Embedded (ULift.{u} ℚ))
    (M : Marked S) (hM : Presents M) (n : ℕ)
    (history : Fin (n + 1) → Embedded (ULift.{u} ℚ))
    (marks : ∀ j : Fin (n + 1), Marked (history j))
    (hstart : history 0 = S) (hstartMark : HEq (marks 0) M)
    (steps : ∀ j : Fin n, Step (history j.castSucc) (history j.succ))
    (hadmissible : ∀ j : Fin n, (steps j).Admissible (history j.castSucc).locus)
    (htransforms : ∀ j : Fin n,
      (steps j).Transforms (marks j.castSucc) (marks j.succ))
    (hempty : (marks (Fin.last n)).cosupport = ∅) :
    ∀ x : (history (Fin.last n)).X,
      function ((history (Fin.last n)).i ≫ (history (Fin.last n)).p) x ≠
        (history (Fin.last n)).level := by
  sorry

/-- Comparisons between different envelope dimensions are made on a common smooth extension,
with both levels summed by their respective relative dimensions.
Source: BMT 6.3; node Steps 9--10
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof: Pull back both presentations by the actual smooth cartesian squares. Step 10 gives
presentations of the summed levels, including all upstairs centers. Since these levels and
the embedded scheme agree, Step 9 identifies every finite test. Earlier center ideals are
pulled back in their original order; equality of their lists identifies their induced birth
data without adding them to the empty starting test boundary. This argument applies at any
identified stage of the finite histories. -/
theorem scheme_presentation_smooth_comparison
    (S T W : Embedded (ULift.{u} ℚ))
    [LocallyOfFiniteType S.p] [QuasiCompact S.p]
    [LocallyOfFiniteType T.p] [QuasiCompact T.p]
    (f : W.Z ⟶ S.Z) (g : W.Z ⟶ T.Z) (r s : ℕ)
    (hf : Pullback f r) (hg : Pullback g s)
    (earlierS : List S.Z.IdealSheafData) (earlierT : List T.Z.IdealSheafData)
    (hearlier : earlierS.map (fun I ↦ I.comap f) = earlierT.map (fun I ↦ I.comap g))
    (M : Marked S) (P : Marked T) (hM : Presents M) (hP : Presents P) :
    ∃ M' P' : Marked W,
      MarkedPullback f M M' ∧ MarkedPullback g P P' ∧
      Presents M' ∧ Presents P' ∧ Equivalent M' P' := by
  sorry

/-- An intrinsic smooth morphism admits local embedded smooth charts, and the class upstairs
is the actual pullback class, with the correctly summed level. Every ordered earlier ambient
center ideal is pulled back along the same smooth chart map, including unit ideals from
identity stages. Source: BMT 6.3; node Steps 9--10
(blueprint: lem-per-scheme-hilbert-samuel-test-presentations).

Proof: Use `sbc-thm-etale-local-normal-form` for the intrinsic smooth morphism: locally it
is etale over the projection from X times affine r-space. Base change a local smooth ambient
embedding of X to that product, and use the etale chart to embed Y locally. Step 10 pulls
the coefficient data and their finite-test identities back to this chart. The numerical
formula sums the extended level r times. The finite-test induction permits every upstairs
center, whether or not it descends. The actual ideal pullbacks preserve the earlier lists
and their ordering; they are not inserted into the newly empty boundary. -/
theorem scheme_presentation_intrinsic_smooth_charts {X Y Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p] [IsImmersion i]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)]
    (f : Y ⟶ X) (r : ℕ) [SmoothOfRelativeDimension r f] (y : Y)
    (earlier : List Z.IdealSheafData) :
    ∃ (S T : Embedded (ULift.{u} ℚ)) (z : S.Z ⟶ Z) (F : T.Z ⟶ S.Z)
      (a : S.X) (b : T.X) (gX : S.X ⟶ X) (gY : T.X ⟶ Y) (q : T.X ⟶ S.X)
      (M : Marked S) (P : Marked T) (earlierT : List T.Z.IdealSheafData),
      Etale z ∧ Etale gY ∧ z ≫ p = S.p ∧ IsPullback gX S.i i z ∧
      gY b = y ∧ gX a = f y ∧ q b = a ∧ q ≫ gX = gY ≫ f ∧
      Pullback F r ∧ IsPullback q T.i S.i F ∧
      S.level = function (i ≫ p) (f y) ∧ T.level = function (f ≫ i ≫ p) y ∧
      Presents M ∧ MarkedPullback F M P ∧ Presents P ∧
      earlierT = earlier.map (fun I ↦ I.comap (F ≫ z)) := by
  sorry

end AlgebraicGeometry.HilbertSamuel
