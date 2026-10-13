## What changed

Decompose `AlgebraicGeometry.affineBaseChangeTildeModuleMap_localized` into
ordinary localized tensor comparison and compatibility of the canonical target
coordinate. Its statement is unchanged. The combining proof factors the module
map, applies composition of localized module maps, uses the two comparison
squares, and unfolds the prescribed stalk arrow.

`AffineTensorPullbackStalkCoordinates` constructs its ordinary target coordinate
from actual tilde, homology, tensor-pullback and stalk isomorphisms, with an
explicit localization instance. `AffineBaseChangeOrdinaryStalkComparison`
isolates ring-model localization before the derived counit and representative
isomorphism. No existing definition or statement is changed.

## Proved and sorry left

Closed original hole: `AlgebraicGeometry.affineBaseChangeTildeModuleMap_localized`
(`lem-pc-affine-base-change-tilde-stalk-comparison`). The combining proof and both new modules compile locally.

Two new intermediate holes:

- `AlgebraicGeometry.affineTensorPullbackHomologyStalkIso_coordinates`
  (`lem-pc-affine-tensor-pullback-stalk-coordinates`).
- `AlgebraicGeometry.exists_affineBaseChangeOrdinaryStalkComparison`
  (`lem-pc-affine-base-change-ordinary-stalk-comparison`).

This is a decomposition, not a complete mathematical proof. No definition has a
hole. The attempted direct target-coordinate proof is retained in scratch work
only; it exceeded the single-file compilation budget.

## No longer needed

Removed the proof-only `import all
Sheaf.AlgebraicGeometry.AffineDerivedCohomologyPresentation` from the earlier
sandbox draft. No original public imports are removed. None of the original
mathematical dependencies is globally pruned: derived tensor localization,
exact localization and tilde stalk localization remain dependencies of the
ordinary comparison. The parent proof directly uses the two new nodes.

## Where the brief, the DAG or earlier work was wrong

The earlier report was stale: the coordinates prerequisite is now locally
available and compiles. The revised coordinate definition needed an explicit
`IsLocalizedModule` instance for its local stalk germ map. The final map factorization uses `erw`
to compare homology-functor object expressions with complex homology. No mathematical error
in the target statement is known. The unit route stays unchanged; its realization
lists are empty.

The local Stacks perfect.tex file is absent. The official
[Tag 0DJ8 page](https://stacks.math.columbia.edu/tag/0DJ8) was read instead; both proof plans carry that source and explicitly
record their agent-written interface decomposition.

## New nodes

`lem-pc-affine-tensor-pullback-stalk-coordinates` constructs the canonical ordinary
pullback target localization coordinate and states compatibility with the inverse
pullback counit and representative isomorphism. It requires no base square,
base-derived tensor model or K-flatness. Source: Stacks Tags 01I9, 01HV and 0DJ8.

`lem-pc-affine-base-change-ordinary-stalk-comparison` states localization of the
module comparison before the inverse derived counit and representative
isomorphism, without K or e. Source: Stacks Tags 0DJ8, 06Y6, 01HV and 01I9.
Semantic, Loogle and source searches found the constituent interfaces, but no
existing theorem with either composite statement. No change record is needed.

## Second reading by Q2

1. I compared the delivered item module with the repository version. Existing
 declarations retain byte-for-byte identical signatures; the target statement is
 unchanged. Verdict: pass.
2. I compiled all three sandbox modules in dependency order. The only remaining
 `sorry`s are the two named split-off theorems, and no definition contains a
 hole or forbidden declaration. Verdict: pass.
3. I searched the library interfaces and Mathlib-facing declarations for the
 two split-off composites. They are new, true interface statements, and each is
 strictly below the original target. Verdict: pass.
4. I checked the proof dependencies against the actual imports and proof route.
 The parent proof uses both split nodes and the coordinate definition; no
 unused original public import was removed. Verdict: pass.
5. I checked the unit record and the DAG proof routes. The unit route remains
 the same, and the node metadata matches the Lean declarations and their
 remaining holes. Verdict: pass.

I added this second-reading record; no code or statement changes were needed
 after the compilation review.
