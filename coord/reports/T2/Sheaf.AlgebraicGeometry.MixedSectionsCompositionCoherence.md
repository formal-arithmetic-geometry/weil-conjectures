## What changed

Replaced the first worker's two unproved transport/representative lemmas with a complete
resolution-and-naturality proof in `MixedSectionsCompositionCoherence.lean` and one genuinely
restricted calculation in `MixedSectionsCompositionKInjective.lean`. The latter takes a cochain
complex `I` and the explicit hypothesis `[I.IsKInjective]`; it only asserts coherence at
`Qh(quotient I)`. No existing statement, definition, visibility, or public import changed.
The original module adds only plain proof imports of the new module and upstream
`RightDerivedFunctor.KInjective`.

The proof forms the two natural transformations, chooses a K-injective representative using the
proved upstream resolution theorem, cancels the target functor's image of the representative
isomorphism, and uses naturality to reduce to the restricted calculation. Acyclicity and the
normalized-unit algebra remain entirely in the lower calculation, whose docstring gives all
steps. Its global-sections acyclicity import is private, as it only serves the planned proof.

## Proved and sorry left

Upper hole closed (complete Lean reduction):
`AlgebraicGeometry.mixedSections_composition_coherence`, node
`lem-sc-mixed-sections-composition-coherence`.

Lower hole added and left open:
`AlgebraicGeometry.mixedSections_composition_coherence_on_kInjective`, node
`lem-sc-mixed-sections-composition-kinjective`, in the new module
`Sheaf.AlgebraicGeometry.MixedSectionsCompositionKInjective`.

This is a decomposition: one upper hole closed and one strictly restricted representative hole
added, net zero. It is not an axiom-free proof of the item. The first worker's two proposed holes
were never landed and are not counted as closed holes. There is no separate transport theorem
left open and no new definition.

Both delivered modules compiled through `lcompile.py --all` without errors or warnings.
A scratch copy with `#print axioms` for both declarations reported exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The target module contains no `sorry`; the sole
new `sorry` is the named theorem above with its source, complete proof docstring, and DAG node.
No axiom, unsafe declaration, opaque declaration, extern, or implemented_by is introduced.

## No longer needed

No original import was removed and no existing library module was pruned. The first worker's
unlanded `MixedSectionsCompositionCoherenceTransport` module and its two proposed nodes were
removed from the delivery; this is not library pruning.

Every old direct proof dependency of the target is replaced by the new K-injective calculation:
`lem-sc-mixed-global-sections-direct-image-iso`,
`lem-pc-ringed-spaces-derived-direct-image-composition`,
`def-pc-global-hom-pullback-comparison`,
`lem-pc-ringed-space-direct-image-kinjective-acyclic`, and
`lem-pc-direct-image-global-sections-kinjective-acyclic`.
The mixed Leray, composition, scalar-restriction and global-sections acyclicity dependencies are
recorded on the new lower node. The separate successive-direct-image acyclicity premise is not
needed by the lower argument: the normalized composition equation identifies its pasted units
with the invertible composite-direct-image unit and inverse comparison. Its module remains in
other dependencies' import closures; no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The first worker's report called the reduction a proof, although it added two holes for one.
Its representative statement quantified over every homotopy object without a K-injectivity
hypothesis, so the proposed unit cancellation did not apply directly; its transport was also
left `sorry` although upstream already proves existence of a K-injective representative.
The existing target-node update omitted the representative lemma actually applied in Lean.
Those proposed nodes had circular statement references to the target and incomplete proof
docstrings. They are removed, rather than retained as apparent progress.

A scalar-factor compatibility calculation and a generic categorical pasting argument were
proved in scratch using upstream `mapDerivedCategoryCompIso_fach` and
`mapDerivedCategoryNatIso_fach`. Instantiation of the full unit argument for concrete sheaf
functors remained unfinished within the single-file limit. These experiments do not constitute
additional delivered proofs. The final delivery does not split a completed proof across files
or alter an expensive definition to hide the limit; it leaves the mathematical unit calculation
open and delivers the independently complete resolution/naturality reduction.

The literature normalization was checked against
[Stacks 0D5T](https://stacks.math.columbia.edu/tag/0D5T) and
[Stacks 0D5W](https://stacks.math.columbia.edu/tag/0D5W). The detailed pinned-unit calculation is
an argument written by the second reader from the equations of the existing library.

## New nodes

`lem-sc-mixed-sections-composition-kinjective` records coherence only on explicitly K-injective
complexes, in `MixedSectionsCompositionKInjective.lean`. Its natural-language and verbatim Lean
statements agree, its proof separates unit normalization from resolution transport, and its
proof dependencies name the existing normalized comparisons and acyclicity. Actual Lean Finder,
Loogle and grep searches, and an unavailable LeanSearch attempt, are recorded in `searches.jsonl`; no exact theorem was found. Direct
source searches also found the upstream generic scalar-factor compatibility lemmas, not an
existing mixed-sections coherence theorem. No change record is needed: all existing interfaces
are unchanged.

## Second reading by T2

1. Compared the original module with the repository using `diff`, then checked the existing
   theorem signature byte for byte. Verdict: unchanged. The only existing-module edits are
   its proof and two private proof imports. No target or shared definition was altered.
2. Compiled both modules through the authorized launcher, inspected every delivered declaration,
   and checked both `#print axioms` outputs in a scratch copy. Verdict: clean compilation, one
   documented lower `sorry`, no forbidden declaration or hollow definition, only the allowed
   axioms plus `sorryAx`. The upper result is conditional on the lower open calculation.
3. Tested the lower statement conceptually on the zero complex, identity morphisms and empty
   schemes, and followed the full normalized-unit proof in its docstring. Verdict: true and
   restricted to exactly the representatives needed by the upper proof. Explicit K-injectivity
   supplies the missing invertibility premise. It is strictly the representative step, not the
   unrestricted target renamed: the resolution/naturality step is proved in the original module.
   Repeated searches with different terms found generic categorical infrastructure only.
4. Read the proof from the target downward, inspected upstream resolution/naturality and scalar
   compatibility lemmas, and checked import visibility and pruning. Verdict: the transport uses
   already-proved upstream infrastructure; all original public imports serve existing signature
   data. The lower proof route retains the canonical mixed/direct-image/scalar comparisons.
   `dag/units/sk-thm-picard-duality.json` has unchanged `realized` statement and step records;
   no protected unit or chapter route is bypassed. The no-longer-needed list accounts for all
   old target proof dependencies, without claiming global pruning.
5. Compared both node records with the final Lean. Verdict: the target names the one calculation
   actually applied; the new node has the complete required fields, exact Lean statement,
   source, proof, dependencies, search records, creation provenance, chapter and unit. There is
   no circular reference back to the target in its statement dependencies.

The first dry run rejected the new node's search metadata because Lean Finder and Loogle count
as the same search kind. An actual LeanSearch attempt returned Internal Server Error; this
unavailability is recorded alongside the successful other search kinds.

Changed in second reading: removed the two unproved and inaccurately described proposals;
proved the resolution/naturality reduction in the original module; added the explicit
K-injective restriction and complete proof/source for the remaining unit calculation; repaired
DAG dependencies and provenance; corrected the report's hole accounting and import visibility.
