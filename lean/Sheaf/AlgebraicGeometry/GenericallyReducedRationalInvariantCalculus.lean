/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.AlgebraicGeometry.GenericallyReducedResolutionData
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent
import Sheaf.AlgebraicGeometry.MarkedIdealNumericalResolutionEngine
import Sheaf.SecTraceFormula.SmoothCenterBlowupGeometry
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-!
# The generically reduced rational invariant calculus

Source: Bierstone--Milman--Temkin, Q-universal desingularization, Theorem/Addendum 6.1,
sections 6.1--6.3, pp. 12--15
(blueprint: lem-per-generically-reduced-rational-invariant-calculus).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.GenericallyReducedResolution

/-- One simultaneous local Hilbert--Samuel/marked-ideal calculus for all generically reduced
finite-type rational embedded schemes, including finite disjoint unions. This chooses the
version stopping at regularity, before the optional exceptional-divisor cleanup.
Source: BMT Theorem/Addendum 6.1, sections 6.1--6.3
(blueprint: lem-per-generically-reduced-rational-invariant-calculus).

Proof plan (the nine steps of the DAG node):

1. We construct the singular-locus part and stop as soon as the strict transform is regular. At
every nonregular point take the full-envelope maximal-order presentation supplied by
[lem-per-scheme-hilbert-samuel-test-presentations], retaining the earlier center ideals and their
order. Use the head $A_x=(c_x,\Delta^{q_x}h_x)$ of [lem-per-scheme-normalized-hilbert-head]. Apply
[lem-trf-marked-ideal-numerical-resolution-engine] to the presentations, and remove their common
leading word entry $1$. Denote the remaining marked word by $t_x$. Define $\nu_H(x)=\bot$ at
regular points and $\nu_H(x)=(A_x,t_x)$ otherwise, in the fixed lexicographic product of the head
space and marked-word space, with a new least element $\bot$. This definition is simultaneous on
finite histories, not an induction assuming termination. Uses:
lem-per-scheme-hilbert-samuel-test-presentations, lem-per-scheme-normalized-hilbert-head,
lem-trf-marked-ideal-numerical-resolution-engine.

2. These are well-defined values. For two presentations of the same germ and retained level,
[lem-per-scheme-hilbert-samuel-test-presentations] gives test equivalence on equal-dimensional
minimal envelopes. For different dimensions, it gives the comparison after adjoining relative
smooth parameters. The marked engine equates the tails under the former equivalence and under the
latter smooth pullback; the normalized head is unchanged by
[lem-per-scheme-normalized-hilbert-head]. Therefore every choice gives the same pair $(A,t)$. On
overlaps these equalities glue the pointwise assignments. Three choices give equalities of the
same values, so the comparison is transitive. The retained earlier ideals and their birth data,
rather than a renumbered tower, are used throughout. Uses:
lem-per-scheme-hilbert-samuel-test-presentations, lem-per-scheme-normalized-hilbert-head,
lem-trf-marked-ideal-numerical-resolution-engine.

3. There are finitely many heads on each finite-type stage by
[lem-per-scheme-normalized-hilbert-head]. On each head locus choose finitely many presentation
charts: finite-type schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian], and
finite subcovers can be chosen as follows. On each affine an ambient union of basic opens is the
union for an ideal $J$; [lem-weil-pbc-noetherian-submodule-finite] gives finitely many generators,
hence finitely many of the original basic opens cover that union. Apply this to the open
neighbourhoods covered by the local presentation charts of
[lem-per-scheme-hilbert-samuel-test-presentations] and restrict to the head locus. The engine
gives finite image and closed upper sets for the tails on these charts. Thus the glued word has
finite image. For upper semicontinuity, near a point remove the finitely many larger head loci; on
the remaining maximum-head locus the assertion is the engine's upper semicontinuity. The boundary
of a head locus can only have greater head, already included in any upper set containing that
locus. Hence the lexicographic upper sets are closed. The regular head criterion shows that our
bottom locus is exactly the regular locus. Uses: lem-per-scheme-hilbert-samuel-test-presentations,
lem-per-scheme-normalized-hilbert-head, lem-trf-marked-ideal-numerical-resolution-engine,
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-submodule-finite.

4. If the greatest word is $m=(A,t)>\bot$, its locus $T$ is nonempty and closed. At each point of
$T$, use a presentation of the maximum head $A$ and restrict away from greater heads. Its
cosupport is the head-$A$ locus by [lem-per-scheme-normalized-hilbert-head], and removing the
initial $1$ identifies its full marked-word maximum with $T$ on that chart. The engine supplies a
smooth closed center on this exact locus, with the required normal crossings. Form
$C=T_{\mathrm{red}}$ by [lem-weil-pbc-reduced-induced-closed-subscheme]. On an etale presentation
chart its pullback is reduced by [lem-trf-etale-reduced-cartier-descent]; the smooth center is
reduced by [lem-sc-smooth-algebra-reduced-field]. The defining equations of the pulled-back $X_H$
vanish on all points of this reduced center, hence vanish in its coordinate rings; the center
therefore factors through the actual $X_H$. Uniqueness of the reduced closed structure identifies
these centers scheme-theoretically with the pullback of $C$, in both the ambient and intrinsic
schemes. Their ideals agree on overlaps. Uses: lem-per-scheme-normalized-hilbert-head,
lem-trf-marked-ideal-numerical-resolution-engine, lem-weil-pbc-reduced-induced-closed-subscheme,
lem-trf-etale-reduced-cartier-descent, lem-sc-smooth-algebra-reduced-field.

5. The center is regular: its local etale charts are smooth over $\mathbf Q$, hence regular by
[lem-weil-pbc-smooth-scheme-over-field-regular], and their maps to $C$ are etale by
[lem-weil-pbc-etale-scheme-base-change], hence their local maps are flat by
[def-weil-etale-morphism]. Apply [lem-weil-pbc-flat-under-regular] to these Noetherian local
rings. It is also coherent in both ambient and intrinsic schemes. Indeed the reduced-induced lemma
gives quasi-coherent radical ideals on affine charts; the coordinate rings are Noetherian by
finite type and quotient permanence [lem-weil-pbc-finite-type-over-noetherian,
lem-weil-pbc-surjective-image-noetherian]. Every such ideal is finitely generated by
[lem-weil-pbc-noetherian-submodule-finite], and [pqf-lem-coherent-ft-locnoeth] makes it coherent.
Uses: lem-weil-pbc-smooth-scheme-over-field-regular, lem-weil-pbc-etale-scheme-base-change,
def-weil-etale-morphism, lem-weil-pbc-flat-under-regular,
lem-weil-pbc-reduced-induced-closed-subscheme, lem-weil-pbc-finite-type-over-noetherian,
lem-weil-pbc-surjective-image-noetherian, lem-weil-pbc-noetherian-submodule-finite,
pqf-lem-coherent-ft-locnoeth.

6. At a generic point the current generically reduced scheme has a field as local ring by
[lem-per-generically-reduced-strict-transform-geometry], hence value $\bot$. Thus $T$ contains no
generic point and contains no nonempty open subset: an open containing a specialization also
contains its component's generic point. This proves nowhere denseness. The ambient blowup remains
smooth, separated and finite type by [lem-trf-smooth-center-blowup-geometry], using
regular-implies-smooth over the perfect field $\mathbf Q$ from
[lem-trf-regular-perfect-field-smooth] for $C$. Only the ambient assertion of the blowup lemma is
used; its reduced-strict-transform clause is not applicable. Generic reducedness of the new
scheme-theoretic strict transform is instead supplied by
[lem-per-generically-reduced-strict-transform-geometry]. Its test admissibility and the agreement
with controlled marked transforms follow from the presentation theorem and the engine. This
inductively constructs all finite maximum histories, starting with the given pair. Uses:
lem-per-generically-reduced-strict-transform-geometry, lem-trf-smooth-center-blowup-geometry,
lem-trf-regular-perfect-field-smooth, lem-per-scheme-hilbert-samuel-test-presentations,
lem-trf-marked-ideal-numerical-resolution-engine.

7. The centers avoid the inverse image of the INITIAL regular locus. Induct on history length. The
initial map is the identity. If earlier centers avoid that inverse image, the blowups and strict
transforms over it are identities by [lemma-nagata-strict-transform-over-complement]. Its local
rings therefore remain the original regular local rings, and the next center, whose word is
greater than $\bot$, misses it. The same induction works after restriction and smooth comparison,
since the normalized head detects regularity and is smooth invariant. A regular or empty initial
input has no nonbottom point and consequently no step. Uses:
lemma-nagata-strict-transform-over-complement, lem-per-scheme-normalized-hilbert-head.

8. For smooth comparison, [lem-per-generically-reduced-strict-transform-geometry] supplies the
actual pulled-back finite diagrams and their retained ideals, deleting just empty centers. The
presentation comparison, normalized head equality and marked-engine smooth functoriality show
pointwise equality of $\nu$; they apply equally to intrinsic smooth maps using local envelopes.
This has no relative-dimension restriction. If $S$ is any individual stratum, its reduced locally
closed structure pulls back to a reduced structure by [lem-trf-smooth-reduced-dense-pullback],
applied to the reduced locally Noetherian scheme $S$. On an open where $S$ is closed, uniqueness
in [lem-weil-pbc-reduced-induced-closed-subscheme] identifies the pulled-back ideal with the
reduced stratum ideal. The same argument in ambient charts gives the ambient ideal. This includes
empty inverse-image strata (unit ideals). For identical intrinsic histories the equalities in step
2 give the same ideals and are compatible with third embeddings. All these equalities commute with
further pullbacks because they identify the same functions and unique reduced structures, not
independently chosen centers. Uses: lem-per-generically-reduced-strict-transform-geometry,
lem-per-scheme-hilbert-samuel-test-presentations, lem-per-scheme-normalized-hilbert-head,
lem-trf-marked-ideal-numerical-resolution-engine, lem-trf-smooth-reduced-dense-pullback,
lem-weil-pbc-reduced-induced-closed-subscheme.

9. It remains to prove termination rather than infer it from strict lexicographic decrease. By
[lem-per-scheme-normalized-hilbert-head] the greatest heads cannot increase and can strictly drop
only finitely often. Suppose an infinite maximum history existed. After its last head drop the
greatest head would be fixed, say $A$. On that interval the maximum-center steps are exactly the
synchronized maximum steps of the presentations retaining $A$: their words all start with $1$, and
comparing their remaining tails is exactly comparing our words with head $A$. The marked engine
rules out an infinite synchronized fixed-head process, including finitely many patched
presentations; when their cosupports empty, the presentation theorem removes $A$, forcing another
head drop or regularity. This is a contradiction. All finite chart choices can be made at the
start of that interval, using Noetherian quasi-compactness as in step 3. Finite disjoint unions
are treated by the same union of presentations and the same maximum, so the argument also proves
their termination. We keep the actual scheme-theoretic strict transforms throughout, and take no
cleanup steps after regularity. Uses: lem-per-scheme-normalized-hilbert-head,
lem-per-scheme-hilbert-samuel-test-presentations,
lem-trf-marked-ideal-numerical-resolution-engine, lem-weil-pbc-finite-type-over-noetherian,
lem-weil-pbc-noetherian-submodule-finite.
-/
theorem exists_calculus :
    ∃ (V : Type (u + 1)) (_ : LinearOrder V) (_ : OrderBot V), Nonempty (Calculus.{u} V) := by
  sorry

end AlgebraicGeometry.GenericallyReducedResolution
