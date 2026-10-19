/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.ResolutionInvariantCalculusData
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.RingTheory.FlatUnderRegular
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Local dimension-corrected embedded resolution invariant calculus

Source: ILO, Expose VIII, 2.3.11 and 2.3.13, pp. 93--94; Bierstone--Milman--Temkin,
Q-universal desingularization, Theorem 6.1 and Addendum, sections 6.1--6.3
(blueprint: lem-trf-hilbert-samuel-resolution-invariant-calculus).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- There is one ordered synchronization value set with a least regular value, and a
simultaneous normalized local invariant for all embedded pairs and their admissible
histories, with the maximum-stratum calculus and termination clauses.

Source: ILO VIII 2.3.11, 2.3.13; BMT Theorem 6.1 and Addendum, sections 6.1--6.3
(blueprint: lem-trf-hilbert-samuel-resolution-invariant-calculus).

Proof plan, following the seven DAG steps:

1. For a local ring at x form h_x, q_x and c_x as in
   [lem-trf-hilbert-samuel-smooth-dimension-profile], and use the normalized head
   A_x=(c_x,\Delta^{q_x}h_x). For a fixed input choose an integer D at least its dimension. The
   common shift \Lambda^D is strictly increasing in lexicographic order: if f and g first differ
   at n, their partial sums first differ there with the same sign. Its inverse \Delta has the same
   property. Thus comparing normalized heads is exactly comparing the modified heads with this
   common D. Changing the dimension of a different input never enters this comparison. The cited
   statement gives finite image, upper semicontinuity and detection of regularity. Keep the
   normalized head, not D, as part of the synchronization value.

2. At a singular point take a minimal-embedding, maximal-order, codimension-zero presentation from
   [lem-trf-hilbert-samuel-local-presentations]. Apply
   [lem-trf-marked-ideal-numerical-resolution-engine] to that marked ideal and delete its first
   entry 1. Prefix the remaining word by A_x. On points already regular set \nu=\bot, irrespective
   of exceptional-divisor cleanup. Use the same lexicographic word space for every input and
   append the one new least element \bot. Minimal-embedding equivalence makes this definition
   independent of the local presentation: equivalent presentations give the same tail word, and
   the head is intrinsic. The transformed presentations use controlled ideal transforms while the
   scheme uses strict transforms; equality of their test sequences is precisely what permits
   applying the marked-ideal construction at every admissible stage.

3. On a finite affine cover, the heads and their tail words have finite images, so their union is
   finite. At a maximum head, its presentation identifies its stratum with the relevant
   marked-ideal cosupport. Upper semicontinuity of the head makes the maximum head closed; upper
   semicontinuity of the tail on that closed stratum makes the full maximum T=\{\nu_H=m\} closed
   in X_H. Let M_H be its reduced induced closed subscheme
   [lem-weil-pbc-reduced-induced-closed-subscheme]. Each point of T lies under a point of an etale
   neighbourhood U\to X_H carrying a presentation; by Step 2, \nu_H on U is the word of that
   presentation, and the marked-ideal engine makes the preimage of T the underlying set of a
   smooth closed center C_U transverse to the exceptional divisors. The base change
   M_H\times_{X_H}U\to M_H is etale [lem-weil-pbc-etale-scheme-base-change], so M_H\times_{X_H}U
   is reduced [etale-proposition-etale-reduced] with the same underlying set as C_U, hence equals
   C_U by the uniqueness clause (3). Now C_U is smooth over \mathbf Q, so its local rings are
   regular [lem-trf-smooth-geometrically-normal]. Etale maps are flat [def-weil-etale-morphism],
   so each local ring of M_H maps flatly and locally to a regular local ring of C_U and is regular
   [lem-weil-pbc-flat-under-regular]. Thus M_H is a nonempty regular closed subscheme when X_H is
   singular. No maximum greater than \bot meets the regular locus. Every generic point of a
   reduced scheme has a field as its local ring: localization at a minimal prime is reduced with
   only its zero prime, so each nonzero element is invertible. Thus a closed subset of singular
   points contains no irreducible component and hence no nonempty open subset. This proves the
   claimed nowhere density.

4. Each affine coordinate ring of X_H and P_H is Noetherian by
   [lem-weil-pbc-finite-type-algebra-noetherian]. A closed subscheme ideal is quasi-coherent by
   [lem-weil-pbc-reduced-induced-closed-subscheme]. Every submodule of a finite module over such a
   ring is finitely generated and finitely presented by
   [lem-trf-noetherian-submodule-finitely-presented]; applying this also to kernels of maps from
   finite free modules proves coherence of the two ideals. The center is smooth over \mathbf Q by
   [lem-trf-regular-perfect-field-smooth]. The ambient blowup and reduced strict transform remain
   in the required class by [lem-trf-smooth-center-blowup-geometry]. At the selected maximum,
   either the head drops or it stays fixed and the tail maximum strictly drops by the marked-ideal
   engine. At other points the admissible-transform heads and tails cannot increase. The next
   positive global maximum is therefore strictly smaller.

5. For a smooth pullback and y\mapsto x, [lem-trf-hilbert-samuel-smooth-dimension-profile] gives
   h_y=\Lambda^s h_x and q_y=q_x+s, with c_y=c_x. Hence \Delta^{q_y}h_y=\Delta^{q_x}h_x. This uses
   the fibre-local dimension s at this point and requires no constant relative dimension. The
   local presentation theorem and the marked-ideal engine give equality of the tail words under
   this pullback, including the ordered exceptional data. Consequently \nu(y)=\nu(x) at each
   finite stage. The maximum center is smooth over \mathbf Q by Step 4. Its inverse image is
   smooth over it, as a base change of the smooth ambient map [lem-pc-proper-base-change], hence
   smooth over \mathbf Q [lem-trf-smooth-composition] and reduced
   [lem-trf-smooth-geometrically-normal]; it has the same underlying inverse-image stratum.
   Uniqueness in [lem-weil-pbc-reduced-induced-closed-subscheme] gives equality of its extended
   ideal and the reduced stratum ideal. If empty, its ideal is the unit ideal. Restriction is the
   same comparison on an open neighbourhood. Deleting an empty center adds no exceptional
   hypersurface and changes none of the local data.

6. Suppose two histories satisfy (3). Their local rings identify, so their heads agree. The local
   presentation theorem identifies the maximal-order presentation equivalence classes using
   exactly the strict-transform schemes and the ordered earlier center ideals. The numerical
   marked-ideal engine then gives equal tail words. The retained ideals matter even for an
   intrinsic identity blowup: they determine the same ordered exceptional information used by the
   presentations. Thus the functions agree. Their images, maxima and maximum subsets agree, and
   uniqueness of reduced induced structure identifies their center ideals. The comparison is
   independent of local choices, so computing it before or after the restriction or smooth
   pullback in the preceding step gives the same head, presentation class and word. This proves
   the stated compatibility for finite histories, without identifying distinct ambient schemes.

7. Assume an infinite maximum-center process from one initial pair. Its heads cannot increase. By
   [lem-trf-hilbert-samuel-smooth-dimension-profile] they can strictly drop only finitely many
   times, so there is an infinite tail with the same maximum head. On this tail use its finitely
   many local presentations. The marked-ideal process is exactly the engine process at that head,
   since Step 2 used its tail word and Step 3 its full maximum center. By
   [lem-trf-marked-ideal-numerical-resolution-engine] this process terminates with empty
   cosupport; by [lem-trf-hilbert-samuel-local-presentations] this removes that head, a
   contradiction. Equivalently the engine's coefficient-dimension induction and terminal monomial
   case exclude the putative infinite constant-head tail. For a finite disjoint union use its
   finite cover and the same global maximum rule, so the same argument applies. The empty scheme
   and every regular scheme have no positive maximum and yield zero steps. This proves (4) for the
   very functions constructed above; no well-foundedness of an arbitrary ordered set is asserted.
-/
theorem exists_resolution_invariant_calculus :
    ∃ (V : Type (u + 1)) (order : LinearOrder V) (bottom : OrderBot V),
      Nonempty (@ResolutionInvariantCalculus.{u, u + 1} V order bottom) := by
  sorry

end AlgebraicGeometry
