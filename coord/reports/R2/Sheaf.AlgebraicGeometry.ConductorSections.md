## What changed

Replaced the sorry in AlgebraicGeometry.Scheme.Modules.conductor_sections with a complete
Lean proof combining a bijective additive restriction map, the kernel description of
closed restriction, and the fibre criterion for nonvanishing. The existing signature,
universes, hypotheses, conclusion, definitions, and public imports are unchanged.

Added three modules, each with one public theorem and a matching DAG node:
ConductorSectionsRestriction, ClosedImmersionIdealTensorSections, and
NonvanishingTensorPullback. The latter two are proved from existing declarations and
Mathlib. The main proof explicitly constructs the inverse extension, proves uniqueness
by injectivity, and proves equality of loci pointwise using the component cover.

The closed-restriction proof handles the different adjunction choices by
Adjunction.rightAdjointUniq: their units differ by an isomorphism, so have equal kernels.
The nonvanishing proof identifies the fibre with the quotient by the maximal ideal,
then applies the existing invertible_pullback_tensor fibre formula and faithful flatness
of a field extension. All added proof imports are non-public.

All four sandbox modules compile together without warnings. No library build was run.

## Proved and sorry left

Closed the original hole:
AlgebraicGeometry.Scheme.Modules.conductor_sections
(lem-sc-conductor-sections).

Added and proved:
AlgebraicGeometry.Scheme.Modules.closedImmersion_ideal_tensor_sections
(lem-sc-closed-immersion-ideal-tensor-sections), and
AlgebraicGeometry.Scheme.Modules.nonvanishing_tensorPullback
(lem-sc-nonvanishing-tensor-pullback).

The only sorry left in the delivery is:
AlgebraicGeometry.Scheme.Modules.conductor_sections_restriction
(lem-sc-conductor-sections-restriction), in its own new module. It is exactly the
additive section-restriction bridge, without the ambient extension, uniqueness, or locus
conclusion. Its docstring and node give the complete mathematical argument. This is a
decomposition, closing one original hole and adding one strictly smaller hole; it is not
an axiom-free proof of the original theorem. Existing imported conductor, quotient and
fibre statements still have their existing sorries, which this delivery does not edit.

Edge cases checked mathematically: m=0 gives structure-module ideal restriction;
a single component gives Z empty and the full ideal; disjoint components give extension
by zero; for k[x,y]/(xy), the complementary ideals (x) and (y) meet in zero and (x) maps
isomorphically to its image on the distinguished branch. Closed restriction to the empty
scheme has the whole module as kernel. Nonvanishing is empty for a zero section and on an
empty scheme. Field extension preserves zero and nonzero fibre values. Neither helper
assumes Noetherianity, separatedness, or finite presentation of the scheme.

## No longer needed

Removed the main module's direct proof imports
Sheaf.AlgebraicGeometry.ConductorIdealRestriction and
Sheaf.AlgebraicGeometry.ConductorIdealZeroIntersection. Both remain needed by
ConductorSectionsRestriction; no corresponding node or module is globally pruned.

No original proof-dependency nodes or modules become unnecessary: the original
conductor argument remains inside the strictly smaller restriction bridge. No unit
statement or realized unit step is bypassed. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

The two conductor declarations do not directly state the map used by this module.
conductorIdealZeroIntersection is expressed using categorical image objects and the
image of an adjoint ideal map, whereas conductor_sections uses the module of the comap
ideal and uncorestricted ideal tensor products. It also chooses the adjunction via
nonempty_tensorPullbackAdjunction and places the tensor power after pullback. The
remaining helper records the missing comparison, including adjunction and tensor-power
transport; it does not assume that the expressions are definitionally equal.

No original statement was changed or disputed. The source .tex files are absent from
this remote checkout, but Stacks Tags 09NW, 09NX and 08KS were read on the official web
pages. LeanSearch returned HTTP 500 for all three new-statement queries; the search log
and node records report unavailable, not no match. LeanFinder and source grep completed.

## New nodes

lem-sc-conductor-sections-restriction, at
 dag/nodes/sec-curve-estimates/lem-sc-conductor-sections-restriction.json:
the additive bijection and inclusion compatibility only, with the component hypotheses
unchanged; the only new remaining hole. Its module is
lean/Sheaf/AlgebraicGeometry/ConductorSectionsRestriction.lean.

lem-sc-closed-immersion-ideal-tensor-sections, at
 dag/nodes/sec-curve-estimates/lem-sc-closed-immersion-ideal-tensor-sections.json:
a proved kernel/range characterisation for any closed immersion, independent of the
component cover. Its module is
lean/Sheaf/AlgebraicGeometry/ClosedImmersionIdealTensorSections.lean.

lem-sc-nonvanishing-tensor-pullback, at
 dag/nodes/sec-curve-estimates/lem-sc-nonvanishing-tensor-pullback.json:
a proved pointwise pullback criterion for an invertible module, independent of all
conductor hypotheses. Its module is
lean/Sheaf/AlgebraicGeometry/NonvanishingTensorPullback.lean.

Blueprint searches for nonvanishing pullback, conductor sections, and ideal tensor
sections found no matching imported blueprint node. All three keep the item's nearest
blueprint ancestor and unit. There are no change records because no existing statement
or definition changes.

## Second reading by R2

1. I compared the delivered `ConductorSections.lean` with the repository version. The
original declaration signature is unchanged; only its proof and proof-only imports were
changed. The three added modules have new declarations with their recorded signatures.
Verdict: pass.

2. I compiled all four delivered modules with `lcompile.py --all`; they compile without
errors. The only remaining `sorry` is the named public theorem
`conductor_sections_restriction`, with its matching node and complete proof docstring;
no definition contains `sorry`, and no forbidden declaration was added. Scratch-copy
`#print axioms` checks of all four declarations report exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The helpers still depend on existing
unproved quotient and fibre-comparison theorems; none is described as axiom-free.
Verdict: pass.

3. The split restriction theorem is a strict reduction: it gives only the additive
bijection and inclusion compatibility, while the original theorem additionally requires
unique ambient extension, vanishing on the complementary closed subscheme, and the
nonvanishing-locus equality. The closed-immersion and pullback nonvanishing lemmas are
independent helper statements and compile from existing declarations. Small cases in the
worker report cover one component, the empty complementary union, disjoint components,
and `k[x,y]/(xy)`. I independently checked the affine argument: reducedness and
`V(I) ∪ V(J) = Spec A` imply `I ∩ J = 0`, hence `I → (I+J)/J` is an
isomorphism; tensoring with a locally free rank-one module preserves it. The
closed-immersion helper includes the empty subscheme and power zero; field extension
preserves zero/nonzero fibre values. I reread the official Stacks pages
[09NW](https://stacks.math.columbia.edu/tag/09NW),
[09NX](https://stacks.math.columbia.edu/tag/09NX), and
[08KS](https://stacks.math.columbia.edu/tag/08KS). A fresh LeanFinder search for
sections supported on one member of a reduced closed cover found open-cover
vanishing/gluing results, not this closed-cover restriction statement. Source searches
for pullback/nonvanishing, ideal tensor sections, `support_comap`, and
`ker_subschemeι` found the already used conductor/quotient APIs and ideal-support
results, no shorter exact result. Closing the remaining image/comap and adjunction
comparison bridge requires substantial new formal transport, rather than a short
application of these search results. Verdict: pass.

4. The main proof follows the recorded route: restriction bijection, kernel
characterisation, and fibrewise nonvanishing. It keeps the unit route and the three
helper nodes; only the two direct conductor imports are no longer used by the main proof,
and they remain dependencies of the split restriction node. Verdict: pass.

5. The node records agree with the Lean declarations and proof dependencies, and the
unit is unchanged: `sk-thm-curveestimate.realized.statement` still names
`thm-sc-proper-cohomology`, and its steps list is unchanged. The new nodes record their sources, proof origins, searches, and
modules. Verdict: pass.

I changed only this second-reading report section; no Lean statement or proof was changed
while reviewing.
