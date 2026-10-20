## What changed

Proved `CategoryTheory.exists_pointSystem_refinement_all` with its signature unchanged.
The proof uses the declared one-cover theorem `CategoryTheory.pointSystemRefine` and
fully proved infrastructure for strict refinements, directed unions, posetal replacement,
and transfinite scheduling of a set of persistent lifting requests.

The category of poset-indexed diagrams has explicit filtered colimits: the index poset
uses Mathlib's PartOrdEmb colimit; compatible object assignments descend to it; arrows
descend by common-stage representatives. The universal property is proved. In the
under-category of the original diagram, good extensions have directed indices and keep
the two classes distinct. Directed unions stay good by the finite-witness criterion.

A missing request is solved using the existing one-cover result. Its preorder output
is restricted to representatives of its antisymmetrization, fixing each original index.
The restriction is cofinal, so the lift survives. Mathlib's SuccStruct iteration over a
well-order of cardinality greater than the request set eventually satisfies every request:
otherwise the newly solved requests would inject that well-order into the request set.
The final representative is extracted from the Hom colimit and gives the required composite.

Moved `pointSystemRefinementMap` to a public-imported helper module with its signature
and body unchanged. Its preorder generalization is the new declaration
`pointSystemRefinementMapOfPreorder` (same body), identified with it on partial orders by
`pointSystemRefinementMap_eq_ofPreorder` (`rfl`). Added its representative, composition and
naturality lemmas. Change record: `coord/changes/K3-pointSystemRefinementMap-preorder.md`.
(Reviewer correction: the delivered version generalized `pointSystemRefinementMap` itself,
which broke `Sheaf.CategoryTheory.Sites.PointSystemSaturation`, a user passing the
`PartialOrder` instances explicitly; the old signature was restored.)

All nine delivery Lean files compile cleanly through `lcompile.py --all`. The three
unchanged downstream modules (`FinitarySiteEnoughPoints`, `FinitarySliceEnoughPoints`,
and `ProEtaleEnoughPoints`) also compile cleanly against the delivered modules in a
scratch copy; those copies are not included in the delivery.
A temporary axioms probe verified that every new mathematical component, including
`exists_pointSystem_refinement_chain`, uses only propext, Classical.choice and Quot.sound.
No source-library file was modified. No target signature was changed.

## Proved and sorry left

Closed 1 of 1 assigned holes: `CategoryTheory.exists_pointSystem_refinement_all`
(node `lem-trf-point-system-refine-all`). Added zero holes, split off zero unfinished
statements, and left zero sorry occurrences in every delivered Lean file.

All eight new modules are fully proved. The principal proved results are
`pointSystemRefinementMap_comp`, `pointSystemRefinementMap_naturality`,
`PointSystemChain.ne_of_stage_ne`, `PointSystemDiagram.unionIsColimit`,
`PointSystemDiagram.Extension.good_of_isColimit`, `exists_pointSystem_posetal_replacement`,
`exists_pointSystem_posetal_refine`, `exists_object_all_requirements`, and
`exists_pointSystem_refinement_chain`.

The assigned theorem still inherits sorryAx from the existing declared dependency
`CategoryTheory.pointSystemRefine` in `Sheaf.Paper.PointSystemRefine`
(node `lem-trf-point-system-refine`); that module is unchanged. This delivery proves the
assigned theorem from that stated dependency, as required by stage 3, and adds no axiom.

## No longer needed

Removed the item's direct proof import `Mathlib.CategoryTheory.Limits.Types.Filtered`;
its use belongs to the chain-union helper. Removed the redundant direct public imports
`Mathlib.CategoryTheory.Category.Preorder` and `Mathlib.CategoryTheory.Limits.Types.Colimits`: the
public map-helper import re-exports both, so the visible import closure is retained. Kept
transfinite iteration, posetal replacement, and filtered-colimit proof imports private in
the new modules where only theorem proofs use them. No DAG node or project module is pruned:
the one-cover result and filtered-colimit elementwise criterion remain necessary, and
the site and colimit definitions remain statement dependencies. No upstream declaration
is removed or weakened. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The first dry run found metadata errors: LeanSearch is a separate required search
kind (LeanFinder plus Loogle count as one kind), and definition signatures omit
`noncomputable` in the delivery parser. Ran LeanSearch for every new node, recorded
the results, and synchronized every new node signature with the official signature
reader. These repairs change no Lean proof or statement.

The one-cover declaration supplies a preorder and a colimit lifting witness, while the
assigned theorem requires a partial order and an explicit morphism. Neither is an obstacle:
the new posetal replacement retains the original embedding exactly and its cofinality
retains the witness; colimit joint surjectivity extracts the morphism. The original node
already flagged this interface mismatch. Its proof metadata now records the implemented
missing-request scheduling route rather than a literal predetermined enumeration.

Edge cases checked: an empty request set is handled by the scheduling theorem; an empty
alternative type cannot be chosen by the step hypothesis; equivalent preorder indices
cannot contain two different original indices because that index is antisymmetric.
The representative selection therefore preserves every original index. Universe w for
the requests, refined index and scheduling ordinal is retained throughout; P may lie in
Type(max w t). No arbitrary object is selected from a holed existence theorem in a definition.

## New nodes

`def-trf-point-system-refinement-map` (definition), module `Sheaf.CategoryTheory.PointSystemRefinementMap`: Canonical maps for strict refinements. Fully proved; no new sorry.

`lem-trf-point-system-chain-union` (statement), module `Sheaf.CategoryTheory.PointSystemChain`: Separation in a directed union of nested systems. Fully proved; no new sorry.

`def-trf-point-system-diagram` (definition), module `Sheaf.CategoryTheory.PointSystemDiagram`: The category of poset-indexed diagrams and its filtered unions. Fully proved; no new sorry.

`lem-trf-point-system-extension-union` (statement), module `Sheaf.CategoryTheory.PointSystemExtensions`: Directed unions of pointed refinements preserving two classes. Fully proved; no new sorry.

`lem-trf-point-system-posetal-replacement` (statement), module `Sheaf.CategoryTheory.PointSystemPosetalReplacement`: Preorder representatives retaining an embedded poset. Fully proved; no new sorry.

`lem-trf-point-system-posetal-refine` (statement), module `Sheaf.CategoryTheory.PointSystemPosetalRefine`: Retaining a lifting equation under posetal replacement. Fully proved; no new sorry.

`lem-trf-point-system-schedule` (statement), module `Sheaf.CategoryTheory.PointSystemSchedule`: Transfinite scheduling of persistent requirements. Fully proved; no new sorry.

`lem-trf-point-system-refinement-chain-exists` (statement), module `Sheaf.CategoryTheory.PointSystemRefinementChainExists`: Scheduling all single-step refinement requests. Fully proved; no new sorry.

Change record: `coord/changes/K3-pointSystemRefinementMap-preorder.md`.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
