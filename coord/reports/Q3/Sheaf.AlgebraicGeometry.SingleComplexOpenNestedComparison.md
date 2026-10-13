## What changed

The item now compiles. Its proof constructs the canonical smaller-open isomorphism and the
pullback-pasting isomorphism, invokes the explicit coefficient-coherence and source-coordinate
transport lemmas, and cancels the resulting source and target isomorphisms. Two strictly lower
statements were split into their own modules: `exists_derivedBaseChange_source_iso` and
`singleComplex_nested_coefficient_coherence`.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.singleComplexOpenComparison_nested_isIso_iff`
(node `lem-pc-single-complex-open-nested-comparison`). There are no holes left in the item.
Added 2 lower holes, so this is a decomposition, not a net reduction in holes.
The lower declarations `AlgebraicGeometry.exists_derivedBaseChange_source_iso` and
`AlgebraicGeometry.singleComplex_nested_coefficient_coherence` remain `sorry`, each with its
own DAG node and complete proof plan in its docstring:
`lem-pc-derived-base-change-source-iso` and
`lem-pc-single-complex-nested-coefficient-coherence`, respectively.
All three modules compiled together in import order through lcompile.py. No definitions or existing signatures were changed. The second reading narrowed the
new coherence module’s public import to DerivedPullbackComposition. These are genuine parts of the mate and
composition calculations, rather than restatements of the item.

## No longer needed

No existing import was removed; no modules are claimed pruned. The second reading removed
an unnecessary proof import of `Mathlib.AlgebraicGeometry.Restrict` from the item
(it is exported by the coefficient-coherence module), and replaced the new coherence
module's unnecessarily broad public import of `Sheaf.AlgebraicGeometry.SingleComplexOpenComparison`
with `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`.
Both old direct proof dependencies absent from the new item node are accounted for:
`lem-pc-derived-base-change-pasting` is used in the source-coordinate lemma's proof plan;
`def-pc-derived-base-change-map` remains used through the explicit open comparison and
source-coordinate lemma. Neither node or module is pruned from the import closure.

## Where the brief, the DAG or earlier work was wrong

The imported plan omitted the need to state the long source-coordinate mate calculation and
the long twice-restricted coefficient coherence as separately usable intermediate statements.
The original theorem itself is unchanged. Mathlib already supplies the geometry through
`Scheme.Opens.isoOfLE`, `pullbackLeftPullbackSndIso`, and `pullback.map` along isomorphisms.
The two existing source-coordinate lemmas for changing the base and upper-left vertex do not
supply simultaneous transport of the source complex and a general coefficient morphism.
The LeanSearch service returned Internal Server Error; LeanFinder/Loogle and source searches
were available. The cited Stacks .tex files are absent on this machine; the corresponding
Tags 08HY, 0D5S and 0DJ9 were read online. The proof origins record the agent-written
expansions of their constructions. No unit statement or unit route was bypassed (the unit's
realized arrays are empty).

Edge cases: neither lower statement asserts invertibility of an open immersion's unit.
Only the source coordinate isomorphisms have invertible units and counits. No coefficient
object or morphism is chosen from a bare existence theorem. The coefficient isomorphisms
are explicit composites. The source-coordinate theorem eliminates its existential
isomorphisms only into the propositional invertibility conclusion. Zero coefficients,
empty opens, Z = W and W = X are included by the same categorical identities.

## New nodes

`lem-pc-derived-base-change-source-iso` is stated in
`lean/Sheaf/AlgebraicGeometry/DerivedBaseChangeSourceIso.lean`.
`lem-pc-single-complex-nested-coefficient-coherence` is stated in
`lean/Sheaf/AlgebraicGeometry/SingleComplexNestedCoefficientCoherence.lean`.

## Second reading by Q3

1. Compared every delivered module with the repository. The sole existing module changes
   only its proof and proof imports; its existing declaration signature is byte for byte
   unchanged. The two added modules are new. No definitions or target statements change.
2. Compiled the three modules in import order with lcompile.py. Only the two reported
   public named lower theorems have `sorry`, as their entire proofs; no prohibited
   declarations or hollow definitions occur. Explicit axiom checks of all three
   declarations show only propext, Classical.choice, Quot.sound and sorryAx. The original
   theorem is a checked reduction conditional on the lower statements, not a complete
   axiom-free proof.
3. Read both lower statements, docstring arguments and nodes against the canonical
   composition and pinned-adjunction definitions, and Stacks Tags 08HY, 0D5S and 0DJ9.
   Their source-coordinate and coefficient identities are valid for arbitrary coefficients,
   zero coefficients, empty opens, identity coordinates, Z = W and W = X. The coefficient
   lemma contains no direct image or invertibility assertion; the source-coordinate lemma
   has no opens and requires the precise coefficient compatibility equation. Thus each is
   strictly part of the argument and neither is a restatement. Independent LeanFinder
   searches for counit-mate naturality and pseudofunctor iterated pullback found generic
   mates and pseudofunctor coherence, not these scheme-derived identities. Source searches
   and reading DerivedBaseChangeTopIso, CoordinateNaturality, DomainIso, CodomainIso and
   Pasting found no simultaneous source-coordinate theorem with coefficient transport.
   Neither remaining calculation can be closed by a short application of those results.
4. Checked the explicit smaller-open and pullback-pasting constructions, coefficient
   composites, structural equalities and cancellation of a.hom and b.hom. No data are
   chosen from the new existence theorem: its witnesses are eliminated only into a
   proposition. Removed unnecessary imports as recorded above. All old proof dependencies
   omitted from the new direct dependency list are accounted for in No longer needed.
   The unit sk-thm-picard-semicon has realized.statement = [] and realized.steps = [[]];
   no realized route is bypassed or altered.
5. Compared node proof steps, dependency unions and proof origins with the Lean reduction.
   New nodes have source, complete proof plans, searches, split status, creation and
   blueprint metadata, the same chapter and unit, and verbatim Lean signatures. Verdict:
   the DAG agrees with this decomposition. No new holes were added by this reading.

Second-reading changes: narrowed the new coefficient-coherence module's public import,
removed the item's redundant Restrict proof import and an extra blank line, and completed
this report's dependency accounting. The existing theorem and both lower statements stay
unchanged. Net holes closed minus added is -1 (one closed, two added).
