/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.MarkedIdealInvariantData
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.MarkedControlledBlowupCharts

/-!
# A simultaneous numerical resolution engine for marked ideals

Source: ILO VIII 2.3.11--2.3.13, pp. 93--94; BMT arXiv:0905.3580, sections 5.1--5.4
(blueprint: lem-trf-marked-ideal-numerical-resolution-engine).
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.MarkedIdeal

/-- There is one numerical-word assignment for every rational marked ideal and its
maximum-center histories, including smooth restrictions and compatible finite local
presentations, with the coefficient-dimension and monomial termination controls.
The ordered alphabet is fixed once and for all by `Entry` and `Word`.

Source: ILO VIII 2.3.11--2.3.13; BMT sections 5.1--5.4; the explicit ten-step
construction of the DAG node
(blueprint: lem-trf-marked-ideal-numerical-resolution-engine).

Proof plan:

1. Fix one tagged alphabet consisting of rational entries, integer entries, the symbol $\infty$,
and finite monomial tuples, ordered lexicographically with the indicated terminal symbols. Use end
markers to compare words; hence words of different lengths belong to one totally ordered set. A
harmless uniform leading entry $1$ is the normalized order of a maximal-order companion; append
the actual residual blocks below it. In particular every maximal-order input has the requested
leading entry. This header neither changes centers nor asserts that the untransformed total order
of an arbitrary marked ideal decreases. For histories, carry the ordered components and the birth
bookkeeping of [lem-trf-residual-companion-boundary-reduction]. We define the tail recursively on
the dimension of its current smooth support, using the same formulas for all inputs; no dimension
bound is inserted into a numerical entry. Uses: lem-trf-residual-companion-boundary-reduction.

2. If the initial ideal is zero on a component, give that component the terminal word
$(1,\infty)$, larger than all finite residual blocks; its center is the entire component, which
disappears by the chart lemma. On the other components, for a nonzero weighted presentation
$(J,c)$ use [lem-trf-residual-companion-boundary-reduction] to factor its boundary monomial and
compute the residual order $\mu$. Append $(\mu,s)$ only when $\mu>0$; at $\mu=0$ append $0$
followed immediately by the monomial entry, without an old-boundary count. At a positive block
take the displayed companion and its old-boundary augmentation. On each neighbourhood of the
maximal pair it presents exactly the retained-prefix stratum, and has maximal order with a
logarithmic maximal-contact equation transverse to the remaining new boundary. Restrict to that
hypersurface by [lem-trf-logarithmic-coefficient-test-equivalence], using the explicit sum of
powers with mark $d!$. Its support dimension is one less. If this coefficient ideal is nonzero on
a component, repeat there. If it is zero, put the terminal $\infty$ symbol there and stop that
branch; its entire support is already a smooth stratum. If the residual order is zero, stop
coefficient recursion and use the monomial construction in Steps 4--5. In dimension zero a nonzero
ideal is a unit, so it has empty cosupport; a zero auxiliary coefficient ideal is the just
described terminal case. Thus this recursion constructs finite words, with at most the original
support dimension many coefficient restrictions. Uses: lem-trf-residual-companion-boundary-
reduction, lem-trf-logarithmic-coefficient-test-equivalence, lem-trf-marked-controlled-blowup-
charts.

3. The two local inputs identify whole test sequences after transforms, rather than only initial
sets. Induction on the number of coefficient restrictions therefore identifies tail words for any
two equivalent local presentations of the same support dimension: the next normalized residual
pair agrees, its augmented companions present equivalent retained strata, and their coefficient
presentations are equivalent in dimension one less. A terminal zero coefficient presentation is
recognizable by its full smooth cosupport; a residual-zero presentation has the normalized
exceptional exponents supplied by the companion lemma. The same induction proves equality after
smooth pullback: coefficient restriction adds no free coordinates to the word, and the companion
lemma compares orders and birth data even when relative dimensions change. Consequently all local
choices in Step 2 give the same word on overlaps and all identified histories. This also defines
words at nonmaximal points by restriction to their local retained-prefix strata. Uses: lem-trf-
logarithmic-coefficient-test-equivalence, lem-trf-residual-companion-boundary-reduction.

4. For a residual-zero presentation write its ideal as $\prod_i\mathcal I_{E_i}^{a_i}$ with mark
$c$. At $x$, among subsets $A$ of the components through $x$ with $\sum_{i\in A}a_i\ge c$, let $p$
be the least size; among those of size $p$ maximize $q=\sum_{i\in A}a_i/c$ and then the ordered
index tuple $A$. Use $\Gamma(x)=(-p,q,A)$ as the terminal monomial entry. Empty cosupport has no
word. By minimality, $\sum_{j\in A\setminus\{i\}}a_j<c$ for every $i\in A$. There are only
finitely many candidate subsets locally; on a stratum where $\Gamma$ is maximal, its center is the
coordinate intersection $\bigcap_{i\in A}E_i$. Passing to a special point can only add candidate
subsets, so $\Gamma$ cannot decrease under specialization and its upper-level sets are finite
unions of closed coordinate intersections. The maximal intersection is smooth and has normal
crossings with the boundary. When boundary components are disconnected, apply this argument on
their finitely many local constant-exponent pieces; equal words give the same intersection on
overlaps. No new geometric theorem is hidden here: these are precisely the coordinate
intersections in the definition of normal crossings. Uses: .

5. Blow up the monomial maximum. In its $i$-chart the chart lemma gives $a_F=\sum_{j\in
A}a_j-c<a_i$, with the other strict-transform exponents unchanged and component $i$ absent.
Compare any subset through a new point with an old subset by replacing $F$, if present, by $i$.
Its old sum is strictly larger if $F$ was present. Thus no new subset of size below $p$ can reach
$c$. For size $p$, either its new sum is strictly below the old maximum sum, or it omits $F$ and
is an old candidate. In the latter case it cannot be the chosen tuple $A$, since $i$ is absent, so
its ordered tuple is smaller when its sum ties. Hence $\Gamma$ strictly decreases above the
center, and the presentation is unchanged elsewhere. For termination, $p$ can increase only
finitely often since at most $\dim N$ boundary components meet. With $p$ fixed, $cq$ is a
nonnegative integer and decreases only finitely often. Once $p,q$ are fixed in a tail, a new
exceptional component cannot occur in a maximal chosen subset, by the strict-sum comparison. All
such subsets then use only the finitely many components already present at the start of that tail.
Their strictly descending index tuples cannot continue indefinitely. Uses: lem-trf-marked-
controlled-blowup-charts.

6. The companion lemma gives finite image and upper semicontinuity of each single block on a
retained-prefix stratum. Recursion on dimension gives the same properties for each coefficient
tail, using Step 4 in the monomial case and a constant terminal symbol in the zero case. For a
maximum leading pair its stratum is closed, and the maximum of its tail is closed there; repeating
this finite times proves that the full maximum is closed. More generally upper-level sets are
obtained by finite unions of these closed prefix pieces, which proves upper semicontinuity of the
word. A finite open cover of the finite-type input supplies only finitely many local block values
at each recursive level; hence the full image is finite. Locally its maximum center is the lift of
the lower-dimensional maximum center through the coefficient presentation, a monomial coordinate
intersection, or an entire terminal smooth support. The two local lemmas ensure that these lifts
are smooth and have normal crossings with all boundary components, including old ones encoded as
equations. Uses: lem-trf-logarithmic-coefficient-test-equivalence, lem-trf-residual-companion-
boundary-reduction.

7. Give the closed full maximum its reduced induced structure using [lem-weil-pbc-reduced-induced-
closed-subscheme]. Its local models in Step 6 are smooth and hence reduced by [lem-trf-smooth-
geometrically-normal]. The uniqueness assertion for reduced induced structures identifies its
ideal with the ideal of every local model. These ideals glue, so the center is a smooth closed
subscheme, with the claimed boundary condition. On a component where the original ideal is
nonzero, its generic point has unit ideal, so no cosupport center contains that component. A
component where the ideal is zero is instead removed by its terminal-support blowup. The
controlled chart lemma applies in both cases, giving a smooth transformed marked pair, a regular
coherent controlled ideal, and the transformed normal crossings boundary; it preserves nonzeroness
on every component not deleted. Thus every chosen maximum blowup is an allowed next history. Uses:
lem-weil-pbc-reduced-induced-closed-subscheme, lem-trf-smooth-geometrically-normal, lem-trf-
marked-controlled-blowup-charts.

8. At a point above the chosen center, either its first differing residual-order/birth-count block
drops, or all earlier blocks are retained. In the second case the companion and coefficient test
identifications reduce comparison to dimension one less. Induction applies there; at the terminal
zero-coefficient case blowing up the whole terminal support removes that retained stratum, and at
the terminal monomial case Step 5 gives strict decrease. Every block is nonincreasing at
comparison points by the companion lemma. Outside the center the chart lemma identifies the old
and new marked pair and its birth history, so the word is unchanged there. No old maximum point
lies outside the center. The new image is finite by Step 6; since every remaining value is
strictly below the old maximum, its own maximum is strictly below it. Uses: lem-trf-logarithmic-
coefficient-test-equivalence, lem-trf-residual-companion-boundary-reduction, lem-trf-marked-
controlled-blowup-charts.

9. Prove termination by induction on support dimension, with the stronger assertion allowing any
fixed finite prefix and any finite family of compatible local presentations. Take a finite cover
at the birth of a prefix; the least common multiple of its local denominator bounds is a
denominator bound for the synchronized next entries. Suppose an infinite chain of maximum blowups
exists. At a fixed earlier prefix the next positive residual-order values have one denominator
bound $D$ by the companion lemma. A nonincreasing sequence in $(1/D)\mathbf Z_{\ge0}$ is
eventually constant; while it is constant its nonnegative birth count is also eventually constant.
Discard this finite initial portion. If the stabilized residual entry is positive, all subsequent
changes are in the coefficient presentation of strictly smaller support dimension, contradicting
the induction hypothesis. A terminal zero coefficient support disappears when it is selected; it
cannot support an infinite tail. If the residual entry is zero, Step 5 rules out an infinite
monomial tail. The zero-dimensional base was checked in Step 2. This uses the actual denominator,
dimension and monomial controls; strict descent in an arbitrary lexicographic set alone is not a
termination proof. Uses: lem-trf-logarithmic-coefficient-test-equivalence, lem-trf-residual-
companion-boundary-reduction.

10. For finitely many equivalent presentations on an open cover use the same word space and take
the maximum over their finite disjoint union. Overlap equivalence from Step 3 identifies the
reduced maximum ideals. The reduced-center uniqueness used in Step 7 glues them; patches not
meeting this maximum undergo an empty-center stage. All proofs of nonincrease and the fixed-prefix
denominator bounds apply on each of the finitely many patches. An infinite synchronized tail
would, after passing to a fixed prefix and then to lower support dimension as in Step 9, require
an infinite monomial tail on one of finitely many patches; each such patch has only finitely many
monomial choices once $p,q$ stabilize. This is impossible by Step 5. Hence synchronization also
terminates. Empty initial support and empty cosupport produce the empty tower. Uses: lem-trf-
logarithmic-coefficient-test-equivalence, lem-trf-residual-companion-boundary-reduction, lem-weil-
pbc-reduced-induced-closed-subscheme.
-/
theorem exists_numerical_resolution : Nonempty NumericalResolution.{u} := by
  sorry

end AlgebraicGeometry.MarkedIdeal
