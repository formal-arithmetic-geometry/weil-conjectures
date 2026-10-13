## What changed

Replaced the hole in
`AlgebraicGeometry.schemeOpenModuleImageComplex_localized_comparisons` by a proof
with unchanged signature. Added proof-only imports of
`Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction`,
`Sheaf.AlgebraicGeometry.OpenImageComplexComparisonUnit`, and
`Mathlib.CategoryTheory.Adjunction.Restrict`.

The single-open computation is transported through the fully faithful derived
open-site equivalence using `Adjunction.restrictFullyFaithful`, then normalized
by `rightAdjointUniq` for the supplied adjunction. Its unit identity follows
from `schemeOpenModuleImageComplexComparison_unit`. Postcomposition by the image
of the supplied representative isomorphism gives comparisons for E. For nested
opens, restriction of the larger underived unit is invertible: restrict first
to the larger open, use its invertible counit and the left triangle, restrict
further, and transport through the nested-restriction isomorphism. Exact
localization preserves this invertibility. It permits cancellation into the
smaller right adjoint. The termwise unit-restriction identity and the adjunction
left triangle then prove the desired mate equality.

All helpers are private and proved. The chosen comparisons are normalized by
their unit identity, which uniquely determines their morphisms: transpose and
cancel the invertible restricted unit. No arbitrary undetermined object is
chosen, and no definition or existing interface changes.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.schemeOpenModuleImageComplex_localized_comparisons`
(node `lem-pc-localized-open-image-complex-comparisons`).

Added 0 holes. No sorry remains in the delivered module. No new modules or
intermediate unproved statements are introduced. Existing dependencies retain
their own proof status; this delivery does not claim to close their transitive
holes.

## No longer needed

The route does not use `lem-pc-open-image-complex-comparison-restriction` or its
module `Sheaf.AlgebraicGeometry.OpenImageComplexComparisonRestriction`. The
corresponding proof-dependency edge is removed. Instead the already proved unit
comparison and a direct adjunction calculation suffice. This is pruning from
this item's route; other library users may still require that module.

No original import is removed: the original file had only the public
`KInjectiveMayerVietorisData` import, which remains necessary for the statement.
The open-image comparison construction, common-universe open localization, and
exact-derived-functor machinery remain needed. No unit-level statement or step
is bypassed (`sk-thm-picard-duality` has no realization attached to this node).

## Where the brief, the DAG or earlier work was wrong

The original plan was valid but used more machinery than necessary for the
nested-open equality. Unit compatibility and invertibility of the larger unit
after smaller restriction determine the equality without transporting the
open-scheme restriction-comparison theorem itself.

Read the Stacks source pages at https://stacks.math.columbia.edu/tag/08BV,
https://stacks.math.columbia.edu/tag/08BS, and
https://stacks.math.columbia.edu/tag/079W. The local literature files named by the
node and the unit are absent; the unit JSON contains the unit statement and
route. Checked empty opens and repeated opens: the proof uses only equivalence,
restriction, and adjunction identities, without nonemptiness, a covering,
termwise injectivity, or distinctness hypotheses.

Searches: LeanFinder returned ordinary scheme open restriction adjunctions,
Loogle returned no exact match, and grep found generic right-adjoint uniqueness.
Project search found the already proved single-open comparison and its unit
identity used here.

Validation: the cleaned module compiled with `lcompile.py`, exit code 0, no
warnings, in 30.6 seconds with the default heartbeat limit. The declaration
scanner reports the original hole closed, no remaining or added holes, and no
changed statements or added public declarations. All delivered source lines
are at most 100 characters. Both added project imports passed the import-cycle
permission check.

The previous generated-probe long-line failure is repaired in the delivery
wrapper. The first retry reached static preflight and exposed file-level
elaboration options as an interface change. Removed the redundant file-level
`autoImplicit` option (the compiler already applies it), and scoped
`synthInstance.maxSize` and `backward.isDefEq.respectTransparency` to individual
declarations with `set_option ... in`. No file-level option or interface change
remains, so no change record or downstream adaptation is needed.

Final validation: `deliver3.py D4
Sheaf.AlgebraicGeometry.LocalizedOpenImageComplexComparisons --no-push` printed
`OK (dry run)`: the proof compiles and passes preflight except for the second
reading, which the designated second reader writes. No second reading is
claimed here, and nothing was pushed. Closed 1 hole, added 0 holes.

## Second reading by D4

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof-only imports, private helpers, and the target proof differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it exits successfully with no warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations, and no hollow definitions. A scratch-copy `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Checked the proof route and helper statements against the imported library and DAG. The private helpers are strictly intermediate categorical facts, true and no stronger than needed; no split-off statements or nodes were added. Similar cancellation and mate helpers in other modules are private and cannot be reused; the available public unit identity is reused. Verdict: pass.
4. Checked pruning and imports. The removed restriction-comparison dependency is unused by the proof; the three added imports are proof-only and necessary. The unit route remains intact, and the node proof and proof_deps match the implementation. Verdict: pass.
5. Checked the node and report metadata, declaration names, line lengths, and the no-longer-needed entry. The node statement remains unchanged and records the delivered proof route. Verdict: pass.

Changed in this second reading: added this review record only. No Lean source, node statement, or proof was changed.
