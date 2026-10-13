## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.sectionCohomology_unit_comparisons`
with a complete Lean proof from the untwisted resolution comparison. Its signature and
existing public imports are unchanged. Added private, explicitly constructed recursive
unit-power and coefficient-twist isomorphisms. Proved their sectionwise scalar-power
identity by induction, identified the nonvanishing open with the inverse image of the
base basic open, and assembled the requested additive equivalences using cohomology
functors. The restriction equation follows from naturality for the coefficient-twist
isomorphism; the scalar equation follows from its morphism identity and the untwisted
scalar equation at `a ^ n`.

Added proof-only imports of `SectionCohomologyUntwistedComparisons` and
`NonvanishingGeneratingLocus`. The former isolates the resolution comparison
on arbitrary nested base opens. It has no tensor powers, twisted coefficient groups,
nonvanishing condition, or power-transition equation. Its proof now explicitly constructs
the restricted resolution and proves both laws. Updated the parent node's proof route and
added the new node with its statement, source and proof in words.

## Proved and sorry left

Closed both declarations:
`AlgebraicGeometry.Scheme.Modules.sectionCohomology_unit_comparisons` and
`AlgebraicGeometry.Scheme.Modules.sectionCohomology_untwisted_comparisons`. No sorry
remains in either delivered module, and the raw comparison is proved by an explicitly
restricted injective resolution. No holes were added; the net change is one original hole closed and zero new holes added.

Both delivered modules compile individually using `lcompile.py`, with the parent
compiled against the sandbox version of the fully proved raw comparison. The unchanged target
signature retains every original binder and conclusion. The added statement was checked
on empty opens, zero coefficients, degree zero and arbitrary scalar r, including zero:
restriction and scalar maps exist in every case, and no inverse of r is used.

## No longer needed

No existing import was removed and no global library-module removal is claimed.
The three existing public imports provide the original statement's vocabulary and are
retained to preserve the module's public interface. The proof does not use the fraction
quotient or its generators; `CohomologyFractionPresentation` supplies the public tensor
section vocabulary used in the original signature.

The parent node no longer directly needs `lem-weil-pbc-module-open-restriction-injectives`,
`lem-pc-open-restriction-module-cohomology`, or
`lem-pc-resolution-sections-homology-scalar`. They are not needed by the new raw comparison either: it constructs the restricted
resolution directly using `RestrictInjectiveResolution` and
`OpenRestrictionAdjunctionExact` and proves scalar compatibility degreewise. Thus the
three planned nodes and their modules `ModuleOpenRestrictionInjectives`,
`OpenRestrictionModuleCohomology`, and `ResolutionSectionsHomologyScalar` are pruned
from this item's proof route. Other targets may still require them.

The already-stated `ResolutionUnitTwistComparison` does not supply this comparison:
it leaves its unit section unspecified and controls a scalar transition on the top open,
whereas this item fixes the pullback section and needs scalar action on the smaller open.
It was not imported. No unit statement or realized unit proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement change was needed. The original plan omitted a
simultaneous untwisted comparison carrying both restriction and scalar laws: the existing
open-restriction natural isomorphism is natural in coefficients, and the scalar comparison
is for specified restricted-resolution section choices, so neither alone supplies the
required open-restriction square. This glue is made explicit and fully proved in the new node.

LeanSearch returned an Internal Server Error; it was recorded as unavailable rather than
as evidence of absence. Loogle, LeanFinder and source searches supplied the generic
resolution-comparison tools. The locally mirrored literature contains citation lists but
not the Stacks source text; Tags [01E1](https://stacks.math.columbia.edu/tag/01E1) and
[01E4](https://stacks.math.columbia.edu/tag/01E4) were read on the Stacks website.

## New nodes

`lem-pc-section-cohomology-untwisted-comparisons` states the simultaneous additive
comparisons on arbitrary nested opens, with restriction and scalar compatibility. It is
strictly the resolution part of the original argument: all tensor-power isomorphisms,
power identities, nonvanishing/basic-open identifications and their assembly remain in
the proved parent. Its source is the section-complex calculation in Stacks Tag 01E4 and
restriction of injectives in Tag 01E1. No change record or forced adaptation is needed.

## Second reading by B2

1. Compared both delivered modules against the repository versions. Existing declaration signatures are unchanged; the parent proof only replaces `sorry`, while the untwisted comparison is a separately named new declaration. No target statement or definition was altered.

2. Compiled the delivered modules with `lcompile.py`; the proofs contain no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The explicit recursive unit isomorphisms and sectionwise induction cover zero powers and arbitrary scalars, including zero.

3. Checked the new untwisted statement and node against its Lean declaration. It is a strict resolution-level comparison needed by the parent, with restriction and scalar laws, and does not duplicate an existing library declaration. Its source and proof dependencies are recorded in the node.

4. Checked pruning and the route. The parent keeps the unit route through nonvanishing/basic-open identification, the untwisted comparison, recursive tensor-unit identifications, and cohomology assembly. The three old direct proof dependencies listed under `## No longer needed` are absent from the new proof; no public import was removed.

5. Checked DAG consistency and the realized unit route. The parent node's proof and `proof_deps` match the code, and the new untwisted node records its Lean module, declaration, source, and proof. No statement change or forced adaptation is present.

I changed only this report by adding this second-reading record; no Lean proof or node correction was needed.
