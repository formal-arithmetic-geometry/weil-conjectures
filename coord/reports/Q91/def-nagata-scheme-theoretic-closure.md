## Worker report

Files written:

- `dag/nodes/sec-nagata-compactification/def-nagata-scheme-theoretic-closure.json`: existing definition, now a Mathlib leaf. The statement is unchanged. The match names `AlgebraicGeometry.Scheme.Hom.image` and explains the inclusion and closed-immersion instance with their actual source lines. Existing definition dependencies now also cover immersion, quasi-compactness and quasi-separatedness.
- `citations.json`: `[]`, since this definition and Mathlib leaf has no proof steps.
- `searches.jsonl`: actual msearch records, retained in full.

Attachments: none. The search of `lean/WeilConjectures/` for the exact blueprint id and the closure notion found related constructions and uses, not a project declaration defining this exact object. The actual definition is in Mathlib, so this is a leaf delivery rather than an ATTACH claim.

WANTED: none.

The imported node had a tentative Mathlib name without a `mathlib_match`, and only an old text-search entry. I supplied current logged LeanFinder, Loogle, LeanSearch and grep evidence and checked the local pinned source. No new nodes were needed. No proof was moved to another node, and no theorem about minimality, openness, density or base change was silently added to this definition.

The neighbouring `def-nagata-scheme-theoretic-image` has an obsolete imported statement saying “largest closed subscheme.” Its `blueprint_update` corrects this to the kernel-ideal construction. I read and followed that update and the main-20261015 source. This delivery does not edit the neighbouring item. The present item's definition agrees verbatim with its current blueprint and needs no statement correction.

Unfinished work: none for this item; the required dry run and delivery are the next tool operations.

## Blueprint and duplicate search

Read the chapter and unit records and the current main-20261015 unit source. The unit starts with the image of a quasi-compact immersion and then asserts separate openness, density and uniqueness results. This node merely names the image closure object and does not replace any part of that route.

Ran `python3 tools/blueprint_refs.py search 'scheme-theoretic closure'`, `ancestor def-nagata-scheme-theoretic-closure`, and searched the whole DAG for the notion. The general image definition already includes the closure terminology, the minimality node is a theorem about it, and the Chow nodes concern its properties in specific settings. Reused the image definition; created no duplicate or special-case node. `blueprint.same_as` is `[]`: there is no second blueprint definition with this same standalone hypothesis-and-construction statement. The imported node's `blueprint.from` is correctly null.

## Review by Q91

I read the unchanged item in both blueprint snapshots, especially main-20261015 `sec-nagata-compactification/sk-lem-nagata-sketch-closure/def-nagata-scheme-theoretic-closure.md`, order 75. It assumes a quasi-compact, quasi-separated immersion a:T→Y and defines its closure as SIm(a) with its closed inclusion. It contains no additional assertion that needs a proof split.

For the source meaning I read Stacks `morphisms.tex`, `definition-scheme-theoretic-image` (Tag 01R7) and `lemma-quasi-compact-scheme-theoretic-image` (Tag 01R8). The latter identifies the image with the kernel-ideal closed subscheme for quasi-compact maps. I then read Mathlib `AlgebraicGeometry/IdealSheaf/Basic.lean`: `Hom.ker` at lines 693–694 uses the largest quasi-coherent ideal inside the componentwise kernel, and `Hom.ker_apply` at 702–703 gives the actual affine kernel under quasi-compactness. This matches the corrected neighbouring definition. No theorem comparing two different closure constructions is needed: the blueprint explicitly uses this Mathlib image notion.

I read `AlgebraicGeometry/IdealSheaf/Subscheme.lean` at 662 and 665. They define `a.image := a.ker.subscheme` and `a.imageι := a.ker.subschemeι`. I also read `AlgebraicGeometry/Morphisms/ClosedImmersion.lean` at 94–95, whose instance proves `IsClosedImmersion I.subschemeι` for every ideal-sheaf datum I. Apply it with I=a.ker. Thus the recorded match includes both the scheme and the specified closed inclusion. The definitions accept arbitrary scheme morphisms, so specializing to an immersion satisfying the two given properties introduces no hypothesis. The quasi-compactness assumption suffices for the affine-kernel identification; no Noetherian, reduced, affine-target or finite-type hypothesis is used. Quasi-separatedness is retained in the item even though this construction does not require it.

I opened each added statement dependency: `def-weil-closed-immersion` explicitly defines immersions as closed then open immersions, `def-weil-finite-type-morphism` explicitly defines quasi-compact morphisms by preimages of affine opens, and `def-weil-quasi-separated-morphism` defines quasi-separatedness by its quasi-compact diagonal. The original image dependency supplies SIm. These statements define exactly the notions taken from them. There are no proof-step node citations, so the citation manifest is empty, rather than fabricated quotations of sources or dependencies.

I checked small cases directly from the construction: the empty immersion has unit kernel and empty image; the identity has zero kernel and image Y; a closed affine immersion Spec(A/I)→Spec(A) retains I and gives Spec(A/I), including its nilpotents. For example A=k[e]/(e²) and the identity retain the nonreduced scheme, so the definition has not accidentally become the reduced topological closure. The construction is available for the empty target as well. These checks expose no false clause.

Against delivery-errors B–E: there is no new statement-only node to audit, no proof sketch masquerading as a statement, no new notion without an existing definition, and no source tag standing in for meaning. The original TeX and hypotheses are preserved. Actual searches are recorded with their real results; the first LeanFinder query returned related immersion API, while Loogle and LeanSearch returned the exact image definition. I read local source lines before accepting those hits. There are no non-elementary inline steps, long steps, uncited facts, circular citations or relabelled clauses. The correction made here is the leaf classification and missing notion dependencies, not a mathematical weakening.
