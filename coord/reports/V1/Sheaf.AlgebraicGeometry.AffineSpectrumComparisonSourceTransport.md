## What changed

The original theorem is reduced to the canonical comparison square for P and its
termwise spectrum pullback Q. The natural functor isomorphism is constructed in
`IsoPullbackStalkCohomology.lean` with complete proofs. The original module then
corrects arbitrary representative isomorphisms using `exists_comparisonSourceIso`
and `comparisonIntoPullback_naturality`, and proves the diagram calculation in a
private generic categorical helper. All existing signatures are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_comparisonIntoPullback_transport`.
Added one strictly smaller hole:
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_canonicalComparison_square`
(blueprint: `lem-pc-affine-spectrum-canonical-comparison-square`). This is a decomposition,
with zero net holes closed. The canonical square excludes the original theorem's
natural-isomorphism construction and arbitrary representative corrections; both
are proved in Lean here. No sorry remains in the original module or in
`IsoPullbackStalkCohomology.lean`.

## No longer needed

No original imports were removed. In the new stalk-cohomology helper,
`StalkComparisonPullbackNaturality` was replaced by the smaller
`StalkComparisonSourceTransport` interface; the canonical-square module imports
representative naturality explicitly because its statement uses comparisonIntoPullback. The original node directly needs only the new
isomorphism construction, canonical square, source transport, representative
naturality, and affine derived coordinates. Its former direct dependencies
`def-pc-base-derived-tensor-cohomology-model`,
`def-pc-single-complex-base-change-stalk-condition`,
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-pc-stalk-derived-extension-comparison`, `lem-weil-pbc-module-stalk-exact`, and
`lem-weil-pbc-module-stalk-pullback` are no longer direct proof dependencies.
They remain used transitively or by the canonical-square item, so no whole existing
module is claimed globally pruned. The new proved helper uses Mathlib restriction
stalks and uniqueness of adjoints instead of constructing ring-equiv tensor inverses.

## Where the brief, the DAG or earlier work was wrong

The planned existing lemmas concern fixed stalk rings and do not themselves state
the comparison square between different affine-spectrum stalk rings. That missing
square is now isolated on the canonical representative. The construction of the
natural cohomology isomorphism is proved using Mathlib's restriction-stalk iso,
exact homology factors and localization lifting, independently of that square.
The original theorem, its hypotheses and conclusion are unchanged; the unit's
realized route is unchanged. Source pages 0DJ8, 0098 and 0D5S were read online.
LeanSearch returned Internal Server Error, recorded as unavailable. Loogle,
LeanFinder and source searches found component facts, with no exact theorem match.
Edge cases checked: zero complexes and rings impose no nonzero assumptions;
empty schemes have no z0; arbitrary degrees and unbounded complexes are allowed;
the source representative automorphism corrects independent e and e0, so even
nontrivial automorphisms of the zero-differential complex are covered. No comparison
map is assumed invertible.

## New nodes

`lem-pc-iso-pullback-stalk-cohomology` records the proved natural cohomology iso and
its concrete supporting constructions. Its module contains no holes.

`lem-pc-affine-spectrum-canonical-comparison-square` records the remaining counit
square with the fixed canonical representative isomorphism and fixed concrete
natural stalk iso. It has one named theorem with exactly `by sorry`, a full proof
in words, and its source. No definition chooses an arbitrary witness from this hole.
There are no interface changes, change records, or forced adaptations.

## Second reading by V1

1. Compared the delivered transport module with the repository version. The existing theorem
   signature is byte for byte unchanged; the added helper modules and canonical-square node are
   the declared decomposition. Verdict: pass.
2. Compiled all three sandbox modules with `lcompile.py --all`; compilation succeeds. Searched
   for forbidden declarations and unlisted `sorry`s. The only remaining `sorry` is the named
   canonical-square theorem, matching its node and this report. Verdict: pass.
3. Checked the new statements against their definitions and edge cases in the report, and
   confirmed the split theorem is strictly narrower than the original (fixed canonical d and no
   arbitrary representatives). No duplicate library declaration was found in the delivered
   modules. Verdict: pass.
4. Checked the proof routes and imports. The transport proof uses the explicit stalk isomorphism,
   canonical square, source transport, and pullback naturality; the imports are minimal for those
   declarations and the original unit route remains represented by the canonical-square split.
   Verdict: pass.
5. Checked the DAG records against the Lean declarations: proof steps and `proof_deps` for the
   transport node follow the actual proof, and both new nodes carry source, blueprint, Lean record,
   and split status. Verdict: pass.

Changed only this report during second reading; no proof or interface repairs were needed.
