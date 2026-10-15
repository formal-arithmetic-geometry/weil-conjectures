## What changed

Proved `CategoryTheory.FormalSplitAttachment.exists_split_truncated_extension` with exactly
its original signature. The proof constructs a compatible cone on the prescribed new family,
builds every simplicial operator by epi--mono image factorization and split normalization,
checks composition, proves splitness and the nondegenerate-index characterization, and uses
matching-object uniqueness for the prescribed boundary restriction. Finiteness is proved from
finite ordinal hom sets, finite nondegenerate subsets, finite sigma types and finite sums.

Moved the twelve original shared definitions, without signature or body changes, into
`Sheaf.Paper.SiteHypercoverFiniteExtensionBase`, publicly re-exported by the item. Added four
further modules: `SiteHypercoverAttachmentOperators`, `SiteHypercoverAttachmentComposition`,
`SiteHypercoverFiniteExtensionConstruction`, and `SiteHypercoverFiniteExtensionSplit`.
Every construction is explicit. Inverse normalization uses the given bijective label map;
no object is chosen from an unproved existence assertion.

All six modules compile without warnings. The unchanged source of the direct importer
`Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence` also compiles against the sandbox
outputs; it is not part of the delivery. Mechanical comparison confirms that all original
signatures, and all twelve relocated definition bodies, are identical. `#print axioms` for
the completed original theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.
The formulas apply unchanged to n=0 and empty families; the ordinal image bound handles all
old/top cases, including non-surjective endomorphisms of the new top degree.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.FormalSplitAttachment.exists_split_truncated_extension`
(node `lem-weil-pbc-site-hypercover-finite-extension`).

Added zero holes. There is no remaining `sorry` in any of the six delivered Lean modules.
This is a full proof, not a decomposition with outstanding obligations.

The main proved supporting theorems are
`CategoryTheory.FormalSplitAttachment.attachmentMap_comp`,
`CategoryTheory.FormalSplitAttachment.exists_attachment_operators`, and
`CategoryTheory.FormalSplitAttachment.split_attachment_of_degeneracies`.
The explicit operator module also proves its normalization, factorization, mixed composition,
identity, and invertible-degeneracy APIs; the base module proves `finite_labels`.

## No longer needed

Removed the direct public imports `Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic` and
`Mathlib.AlgebraicTopology.SimplicialObject.Basic` from the item: the shared base module
publicly imports both, so the dependency and public interface remain available.

No existing node or module is pruned. Both original mathematical proof dependencies
(`def-weil-pbc-simplicial-coskeleton` and `def-weil-pbc-formal-coproduct`) are still used through
the shared data node. No unrelated Sheaf theorem was imported. The item's DAG route now lists
its actual data, realization, and splitness dependencies rather than pretending that the full
construction and composition check are a single elementary step.

## Where the brief, the DAG or earlier work was wrong

No statement was found false, and no statement or definition was weakened. The formal
`BoundaryCone` already supplies all compatible lower projections, so the missing-value
construction in the old node's step 2 is unnecessary in the Lean proof: compose its projections
with v directly. This uses exactly the original interface. The difficult omitted composition
verification from Stacks 0DAV is now proved in Lean by image-factorization identities and all
eight old/top degree cases. No unit statement or realized unit proof step was bypassed.

The definition relocation is recorded in
`coord/changes/site-hypercover-finite-extension-definitions.md`. No forced adaptations were
needed, and no file held by another group was changed.

## New nodes

`def-weil-pbc-site-split-attachment-data` attaches
`Sheaf.Paper.SiteHypercoverFiniteExtensionBase`: relocated shared definitions, the unique
normalization equivalence, epi precomposition of labels, and the proved finite-label API.
Its existing definition bodies retain their exact meanings.

`def-weil-pbc-site-split-attachment-operators` attaches
`Sheaf.Paper.SiteHypercoverAttachmentOperators`: explicit normalized operators, their
factorization-independent formulas, mixed composition identities, identities, and invertible
epi components. All accompanying theorems are proved.

`lem-weil-pbc-site-split-attachment-composition` attaches
`Sheaf.Paper.SiteHypercoverAttachmentComposition`: the proved contravariant composition law
for every pair of ordinal maps, by all eight old/top degree cases and equality transport.

`lem-weil-pbc-site-split-attachment-operators` attaches
`Sheaf.Paper.SiteHypercoverFiniteExtensionConstruction`: the proved realization theorem,
including strict old restriction, explicit new and old faces, and the top epi index/component API.

`lem-weil-pbc-site-split-attachment-split` attaches
`Sheaf.Paper.SiteHypercoverFiniteExtensionSplit`: the proved transfer of splitness to the new
functor and exact characterization of its top nondegenerate indices from the epi API.

The parent node's statement is unchanged; its proof, proof dependencies, proof origin and Lean
declaration attachments follow the implemented route. Each new node records the actual three
kinds of Mathlib search, including the unavailable LeanSearch response. No new node has any
remaining proof obligation. Change record:
`coord/changes/site-hypercover-finite-extension-definitions.md`.

## Second reading by D3

1. **Existing interface: pass.** I compared the repository module with the six delivered
   modules. The original theorem signature is byte-for-byte identical. All twelve relocated
   definition/structure signatures and bodies are byte-for-byte identical (only their docstring
   blueprint tags change). The relocation and public re-export are documented in the change
   record. `downstream.py` confirms its eleven downstream modules; the unchanged direct
   importer `Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence` compiles against the
   sandbox overlay. No target, existing statement, or definition meaning changed.

2. **Proof and construction: pass.** I read all six modules and compiled them with
   `lcompile.py --all`; each compiles without warnings, in 1.1–4.3 seconds. None contains
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC`.
   A scratch import resolved explicitly against the sandbox `.lbuild` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound` for
   `CategoryTheory.FormalSplitAttachment.exists_split_truncated_extension`. The delivery
   dry run also checks every delivered declaration's axioms. Normalization is the inverse of
   the assumed bijective label-index map, hence is uniquely determined; the family, operators,
   and functor are constructed explicitly. No arbitrary witness is chosen from an open theorem.

3. **Supporting statements and sources: pass.** I read Stacks
   [0DAV](https://stacks.math.columbia.edu/tag/0DAV), construction and final composition
   paragraph, and [0DAU](https://stacks.math.columbia.edu/tag/0DAU), splitness characterization.
   The source `.tex` is absent on this machine, so I checked the official pages. The base
   module's normalization and finite-label results, explicit operators, composition law,
   realization theorem, and splitness theorem match their nodes and are all proved. I checked
   image dimension bounds for top-to-old maps, proper top endomorphisms, and epi endomorphisms
   (which are identities). The formulas still apply for n=0 and empty new/old index families:
   the top family is exactly the displayed sum, and the nondegenerate characterization uses
   disjoint sum constructors without nonemptiness assumptions. No new hole is split off.
   Additional `msearch.py` searches used LeanFinder's query about prescribed nondegenerate
   summands and compatible boundaries, Loogle `"Truncated", "nondegenerate"`, and grep
   `matching.*split|split.*matching|nondegenerate.*extension|extension.*nondegenerate`.
   They found no attachment theorem. Searches of `lean/Sheaf`, `lean/WeilConjectures`, and
   the local upstream source also found no replacement for this construction.

4. **Top-down argument and pruning: pass.** The main proof first composes v with the boundary
   cone, constructs L, and applies the independently proved splitness criterion. Matching
   uniqueness supplies b and its restriction to v; old restriction and finite label/sum
   instances supply finiteness. I checked all eight old/top composition branches against
   their face/lift/end identities. The proof-only construction, splitness, composition,
   and finite-type imports are plain imports; public imports supply declarations used in
   signatures or preserve the relocated interface. The two removed direct Mathlib imports
   remain public through the base module. The original formal-coproduct and simplicial
   proof dependencies remain used transitively through the data node; no old dependency
   becomes unused and no module is pruned.

5. **DAG and unit route: pass.** For each of the six node files, `proof_deps` is exactly the
   union of the proof steps' `uses`. The existing parent node changes only `lean`, `proof`,
   `proof_deps`, and `proof_origin`; its mathematical statement is unchanged. The new nodes
   have the required source, creation, blueprint, search, and Lean records. The dependencies
   follow the actual base → operators → composition → realization route and the separate
   splitness route. I read `dag/units/sk-thm-properbasechange.json`: its realized statement
   and three proof steps remain unchanged. This attachment is a supporting node below those
   unit steps; no realized unit node is replaced or bypassed.

Second reading changed only this report: added the review evidence above. No Lean proof,
statement, definition, node, or change record required repair.
