## What changed

Proved the unchanged declaration
`CategoryTheory.colimit_site_finite_section_colimit_presentation` from the existing,
proved coherent-section-diagram theorem and one new supplied-data comparison theorem.
The original module now constructs both sheaf comparison families by transposing units
through `sheafAdjunctionContinuous`, obtains `D`, the stage isomorphisms, the cocone and
point isomorphism from `colimit_site_abelian_section_diagram`, and constructs the source
natural transformation by composing each stage unit with the inverse stage isomorphism.
The existing private `exists_transition` from
`Sheaf.CategoryTheory.ColimitSiteAbelianStageImageRefinement` is reused through a
proof-only `import all`; the duplicate `sheaf_triangle_unit` declaration is removed.
A proved private `arrow_precomp` helper resolves the heterogeneous endpoint transports.
Naturality and both required additive-map unit equations are proved in Lean. Bijectivity
of the canonical `colimit.desc` is converted into `IsColimit` by reflection of isomorphisms
through the group forgetful functor and `IsColimit.ofPointIso`.

Added `Sheaf.CategoryTheory.ColimitSiteFiniteSectionComparisonBijective`, with a single
public theorem about the canonical comparison for supplied coherent data. Updated the
parent node's proof route and added a node for that comparison theorem. No existing
signature, definition or public import changed. No other existing module was adapted.
All data used by the parent are supplied by proved adjunction/diagram constructions;
the new unproved theorem supplies only a property of already constructed data.

Sources read: Stacks [0A35](https://stacks.math.columbia.edu/tag/0A35), presentation,
sheaf condition and adjunction paragraphs before exactness, and
[03CO](https://stacks.math.columbia.edu/tag/03CO) for the abelian extension.
The fixed unit `sk-thm-p1` and all of its realized statements and proof steps are retained.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.colimit_site_finite_section_colimit_presentation`
(node `lem-weil-pbc-colimit-site-finite-section-colimit-presentation`). Its proof contains
no `sorry`, and its signature is unchanged.

Added one hole:
`CategoryTheory.colimit_site_finite_section_comparison_bijective`
(node `lem-weil-pbc-colimit-site-finite-section-comparison-bijective`), in its own module,
with proof exactly `:= by sorry`, source, and complete proof in words. No other delivered
declaration contains `sorry`. This is a decomposition: one hole closed and one hole added,
not a net reduction in holes and not an axiom-free proof of the section formula.

The remaining assertion only proves bijectivity of the canonical comparison for a
supplied diagram/cocone and supplied unit-characterized sheaf maps. It supplies no
existential witnesses, source natural transformation, or source-unit compatibility.
Those parts are proved by the parent, using the existing diagram theorem and the
adjunction equations. The new assertion is therefore a strict part of the argument,
rather than the original existential statement renamed or repackaged as a hypothesis.

Edge cases checked before stating the helper: an empty source stage has no `U`, making
that case vacuous; filteredness excludes an empty indexing category; empty covers impose
the zero group without dropping the empty-product condition; at the zero sheaf the
comparison is the unique map between zero groups; identity and constant systems give
the usual identity section comparison. No extra nonemptiness or vanishing assumption
was added.

## No longer needed

Removed the proof imports `Mathlib.CategoryTheory.Adjunction.Mates`,
`Mathlib.CategoryTheory.Filtered.Final`, and
`Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit` from the original module.
Retained all original public imports and the used proof import
`Sheaf.CategoryTheory.ColimitSiteAbelianSectionDiagram`.

The explicit conjugate-equivalence unit lemma
`lem-weil-pbc-conjugate-iso-unit-equation` is no longer needed by this route: construction
uses the inverse equation of the sheaf adjunction hom equivalence directly. This does
not assert that the node is unreachable from every other target.
The following old parent proof dependencies are no longer direct proof dependencies:
`lem-weil-pbc-filtered-colimit-sets-elementwise`,
`lem-weil-pbc-filtered-colimits-commute-finite-limits`, and
`lem-weil-pbc-initial-functor-cofiltered-criterion`. They remain in the comparison
helper's mathematical proof plan; they are moved below the parent, not globally pruned.
The four definition nodes `def-weil-pbc-arrows-functor`,
`def-weil-pbc-category-colimit`, `def-weil-pbc-finite-precoverage`, and
`def-weil-pbc-sites-and-cohomology` remain statement dependencies (and are recorded
in the helper's plan), rather than separate steps in the parent's formal proof.
This accounts for every removed entry of the old parent's `proof_deps`.
The duplicate local `sheaf_triangle_unit` proof is no longer needed; its two uses
now apply the existing `exists_transition`. The stage-image-refinement node is
a dependency only for that proved private helper, not for its full representative
theorem. No library module is claimed globally pruned.

The earlier attempt's extra import `Sheaf.CategoryTheory.ColimitSiteAbelianInverseImage`
was removed. That module, `ColimitSiteAbelianSectionUniversality`, and
`ColimitSiteAbelianSectionEventualEquality` are not dependencies of this proof.
The explored `ColimitSiteAbelianSectionRepresentatives` route was also omitted to avoid
the planned DAG dependency through source-unit zero detection. No unrelated library
module has been deleted or claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The previous attempt sought to import `ColimitSiteAbelianInverseImage`, but
`import_direction.py` reports that it already reaches this module through section
universality, eventual equality and finite-unit zero detection. It cannot be used here.
The returned duplicate private `sheaf_triangle_unit` has been removed entirely.
The same proved construction already exists as private `exists_transition` in
`Sheaf.CategoryTheory.ColimitSiteAbelianStageImageRefinement`; a proof-only
`import all` exposes it for reuse at both call sites. `import_direction.py may`
accepts this dependency. No library module or visibility is changed, and the
independent coherent-diagram theorem is still used.

Endpoint transports do not require a new unproved glue statement: equality induction
on the target object gives `arrow_precomp`, after which the unit equations and
isomorphism cancellations prove the required direct morphism equalities.

Although `ColimitSiteAbelianSectionRepresentatives` has no Lean import path to this item,
its matching-lift node's planned proof cites finite-unit zero detection, whose proof
uses this item. Using that planned route here would create a DAG cycle. The new
comparison theorem instead follows the direct presentation/sheaf/adjunction argument
of 0A35 and assumes no source-unit zero-detection theorem.

Searches: LeanSearch returned an internal server error (no result assessed). LeanFinder
found componentwise presheaf limits and condensed Kan-extension comparisons, with
inapplicable hypotheses. Loogle found `IsColimit.ofPointIso`, used after bijectivity.
Mathlib grep found no `sheafPullback`/colimit formula. Project and blueprint searches found
no independent supplied-data comparison result; the existing universality interface
is circular here. The recorded new-node searches reproduce these actual calls.

## New nodes

`lem-weil-pbc-colimit-site-finite-section-comparison-bijective` is stated in
`lean/Sheaf/CategoryTheory/ColimitSiteFiniteSectionComparisonBijective.lean` by
`CategoryTheory.colimit_site_finite_section_comparison_bijective`. It isolates steps 2–4
of the parent plan: presentations, finite-cover sheaf descent, adjunction identification
and the comparison property for supplied coherent data. Its proof plan uses the existing
object/arrow equality, finite-limit commutation, finality and sheaf adjunction nodes,
and never this parent or its zero-detection consequences. There are no change records,
since no existing statement or definition changed.

Repair validation: both sandbox modules compile through `lcompile.py --all` without
errors or warnings. The sole remaining hole is the comparison theorem listed above.


## Second reading by H1

1. Interface: PASS. Compared both delivered modules with the repository. The new
   comparison module is new; the sole existing public theorem signature is byte for
   byte unchanged. All existing public imports are unchanged. There are no changed
   definitions, target statements, forced adaptations, or change records.
2. Proof: PASS as a decomposition. Compiled both files locally in import order,
   without errors or warnings. Scratch copies with `#print axioms` show exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` for both public theorems.
   Only the listed comparison theorem has `sorry`; its body is exactly `by sorry`.
   No prohibited declarations or hollow definitions occur. The choices of alpha,
   theta and coherent diagram data use proved adjunction and diagram constructions;
   the new open theorem is used only for bijectivity of an already supplied map.
3. Split statement: PASS. Read the complete signature and proof docstring against
   Stacks 0A35 and the abelian extension 03CO. Adjunction uniqueness fixes alpha and
   theta from their unit equations on every source object. The endpoint Arrow
   equations identify all transitions and cocone legs, so supplied data cannot
   evade the canonical comparison. Checked identity/constant systems, zero sheaves,
   empty covers (zero sections), empty source stages (no U), and exclusion of an
   empty indexing category by filteredness. The remaining comparison property is
   strictly part of the original existential conclusion: source naturality and
   both unit equations are proved in the parent. Independent LeanFinder, Loogle,
   Mathlib grep and project rg searches found no acyclic applicable replacement.
   The remaining presentation/descent/adjunction construction is substantial and
   cannot responsibly be closed in a few minutes. One old hole is closed and one
   new hole added: net zero, not an axiom-free proof of the formula.
4. Route and pruning: PASS. Read the coherent diagram construction and the reused
   private `exists_transition`; checked the naturality, cancellation and final
   point-isomorphism argument. The report accounts for every removed old proof
   dependency. The unit sk-thm-p1 and its realized statement and steps are untouched;
   this comparison lies below those fixed nodes. No globally pruned library module
   is claimed. Tested removal of the new module's Grp.FilteredColimits import:
   compilation then fails to synthesize HasWeakSheafify in the public signature.
   Restored it, since it supplies required sheafification instances, not just proof
   lemmas. Existing public imports were retained as required by interface stability.
5. DAG: PASS. Both node Lean signatures match their declarations verbatim; both
   proof_deps lists equal the union of their proof-step uses. Existing node changes
   are confined to proof, proof_deps and proof_origin. The new node has source,
   full proof, searches, creation, blueprint, chapter/unit and Lean records. Its
   transitive statement/proof dependency closure does not reach the parent, so the
   comparison plan is not circular. The stage-image-refinement node is accurately
   documented as the source of a proved private helper, not an invocation of its
   full theorem.

Second reading changed only this review report and the new node's independent-search
record. No Lean changes were needed. Final local compilation and explicit axiom probes
passed after the import-minimality experiment was reverted.
