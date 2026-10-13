## What changed

Proved `AlgebraicGeometry.Scheme.traceDiscriminantSectionIdeal_germ_generator_mem`
from the existing finite-flat affine-basis and discriminant affine-restriction
lemmas and one new generic affine-cover ideal descent theorem. The assigned
statement, all existing public imports, and its original docstring are unchanged.
Added proof-only imports of `FiniteFlatAffineBasis`,
`TraceDiscriminantAffineRestriction`, and `AffineCoverIdealStalk`.

Private, fully proved helpers localize a finite basis to a principal open,
find a free affine neighbourhood inside U, and compare discriminant ideals in a
stalk using a common principal refinement. The main proof supplies the cover
and compatibility hypotheses of the generic theorem, identifies its dependent
intersection with the actual definition, and maps the discriminant generator.
No algebra or ideal is defined by choosing a witness of an unproved theorem.
The existing affine-basis theorem is used only inside a proof.

`AffineCoverIdealStalk` is a new module containing one generic theorem about an
arbitrary family of ideals on affine subcharts. Its docstring gives the full
quasi-coherent subsheaf gluing argument. This leaves the general descent step for
another worker; it does not move the discriminant statement under another name.

Unchanged copies of `FiniteFlatAffineBasis`, `TraceDiscriminantAffineRestriction`,
and `TraceDiscriminantSectionIdeal` are present solely to compile against this
machine's incomplete published snapshot. They have no delivery diff.

## Proved and sorry left

Closed the assigned hole in
`AlgebraicGeometry.Scheme.traceDiscriminantSectionIdeal_germ_generator_mem`
(node `lem-sbc-trace-discriminant-section-germ-generator`). There is no `sorry`
left in the assigned module, including its three private helpers.

Added one hole, the complete proof of the public theorem
`AlgebraicGeometry.Scheme.affineCoverIdeal_map_germ`
(node `lem-sbc-affine-cover-ideal-stalk`). This is a decomposition: one upper hole
closed and one generic descent hole added, net zero holes. The discriminant-specific
cover, compatibility, indexing, and membership arguments are fully proved in Lean.

Compilation of the assigned module and the generic module succeeds without warnings.
Edge cases checked mathematically: empty U or empty cover has no test point;
repeated charts and different local bases are handled by stalk compatibility;
zero and unit ideals satisfy descent; rank zero and zero discriminant cause no
change in the Lean proof. No nonvanishing, reducedness, or positive rank is assumed.

## No longer needed

None. Both original proof dependencies `lem-sbc-finite-flat-affine-basis` and
`lem-sbc-trace-discriminant-affine-restriction`, and the section-ideal definition,
are used. No original import was removed, no unit step bypassed, and no module
is claimed pruned. The new descent lemma does not import the assigned module or
the localization/gluing modules above it, so the proof introduces no cycle.

## Where the brief, the DAG or earlier work was wrong

The original single-step plan describes finite-cover descent but its named
prerequisites only provide free charts and discriminant restriction; neither
states the needed generic ideal descent assertion. The new node isolates that
missing step and the item node now follows the Lean argument in three steps.

The published local build initially lacks `TraceDiscriminantSectionIdeal.olean`.
Compiling unchanged dependency copies into the sandbox resolves this; no build
of the shared library or alteration of a dependency is needed.

Mathlib searches used leanfinder, loogle, grep, and leansearch through msearch.py.
The first three returned related IdealSheafData and affine stalk criteria, whose
source was read. IdealSheafData's constructors assume localization compatibility,
so applying them to the desired intersection would be circular. Leansearch returned
HTTP 500 and is recorded as unavailable, with no inference of absence.
The blueprint search for "compatible ideals" returned no match. Existing
`HilbertEmbeddedPointsGluing` concerns coherent modules and an additional supplied
family on all opens, rather than the present ideal intersection/stalk interface.

Source checks: [Stacks 0BVH](https://stacks.math.columbia.edu/tag/0BVH)
for the local determinant ideal; [01HR](https://stacks.math.columbia.edu/tag/01HR)
for associated sheaves and stalk localization;
[01I6](https://stacks.math.columbia.edu/tag/01I6) for the affine quasi-coherent
module equivalence; [01LA](https://stacks.math.columbia.edu/tag/01LA) for locality
of quasi-coherence. The local literature checkout is absent on this machine,
so these primary sources were read online. No statement or definition was changed.

## New nodes

`lem-sbc-affine-cover-ideal-stalk`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-affine-cover-ideal-stalk.json`, states that
compatible ideals on any affine cover of U have their expected stalks when their
U-section ideal is defined as the intersection of inverse images. Unlike the
assigned statement, it has no morphism, flat algebra, trace, discriminant, or basis;
it assumes the cover and compatibility which the assigned proof constructs.
Its proof in words glues the local quasi-coherent ideal subsheaves, identifies
sections by the sheaf axiom, and computes stalks by affine localization. It has
its own module, `Sheaf.AlgebraicGeometry.AffineCoverIdealStalk`, a source, and all
four searches actually recorded by msearch.py. No change record is required:
existing signatures and definitions are unchanged.

## Second reading by G2

1. Compared every sandbox module with the repository. The assigned theorem signature
   and existing docstring are byte-for-byte unchanged; its only interface additions
   are private proved helpers. The three dependency copies are byte-identical.
   The three added imports are proof-only. No definition or existing statement changes.
   Verdict: pass; no change record is needed.
2. Compiled all five files in import order with lcompile.py, without errors or
   unexpected warnings. An independent scratch copy with `#print axioms` checks the
   assigned theorem and the new theorem: only propext, Classical.choice, Quot.sound,
   and sorryAx occur. The single new direct hole is affineCoverIdeal_map_germ;
   none is hidden in a definition or private helper. No forbidden declaration form.
   Verdict: pass as a decomposition, not a completed axiom-free proof.
3. Read the generic descent theorem, its node and its full docstring argument.
   Equality of the local ideal stalks identifies the associated ideal subsheaves
   on overlaps. Gluing these subsheaves and the affine quasi-coherent equivalence
   identifies their global sections with exactly the displayed intersection.
   This proves the claimed stalk equality without commuting localization with an
   infinite intersection. Checked empty charts/cover, zero and unit ideals,
   repeated charts, rank zero and vanishing discriminants. The generic theorem
   supplies just descent; the assigned proof independently proves the cover and
   discriminant compatibility hypotheses. It is a distinct step, not a renamed item.
   Repeated leanfinder, loogle and grep searches with different queries (gluing ideal
   submodules and equality of prime localizations; Ideal.comap and Ideal.map).
   Read Mathlib IdealSheaf.Basic, including ofIdeals, and the library theorem
   existsUnique_coherent_submodule_of_affine_cover. Neither supplies this interface:
   ofIdeals only gives the largest compatible ideal sheaf below a family, and the
   coherent-submodule theorem requires an additional family on all opens.
   Verified the cited Stacks sections 01HR, 01I6 and 01LA directly.
   Verdict: true and needed; no short existing proof found to close the descent hole.
4. Read the reduction from the top: principal localization of a given basis,
   free affine cover construction, common-refinement discriminant comparison,
   generic descent, dependent-intersection identification, and generator membership.
   Every added import is used; both original proof dependencies remain used and
   No longer needed is complete (none). No unit step is bypassed. Read
   dag/units/sk-prop-input-spreading.json: its realized arrays are already empty,
   and this delivery makes no change to the unit or its route.
   Verdict: pass; one upper hole closed and one descent hole added, net zero.
5. Checked both node records against the Lean theorem and the three proof steps;
   existing node changes are confined to proof, proof_deps and proof_origin.
   The new node has its source, proof, dependency union, searches, creation record,
   blueprint provenance, chapter, unit and Lean declaration.
   Verdict: pass after making its lean.statement literally match the multiline
   Lean signature, as required by the new-node brief.

Second reading changed only the new node's lean.statement formatting to the verbatim
signature and added this review record. No Lean proof required repair.
