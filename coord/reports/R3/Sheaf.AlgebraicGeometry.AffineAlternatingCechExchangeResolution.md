## What changed

Replaced the proof hole in `AlgebraicGeometry.exists_affineAlternatingCech_exchange_resolution`
by combining two strictly smaller intermediate theorems. Its existing signature and
public imports are byte-for-byte unchanged. Added proof-only imports of the new core
and exchange modules; removed redundant direct imports carried by those modules.
No definition or arbitrary chosen data was added.

## Proved and sorry left

Closed the hole in `AlgebraicGeometry.exists_affineAlternatingCech_exchange_resolution`.
Added two named holes: `AlgebraicGeometry.affineAlternatingCech_resolution_core`
(node `lem-pc-s3-affine-alternating-cech-resolution-core`) and
`AlgebraicGeometry.affineAlternatingCech_resolution_exchange`
(node `lem-pc-s3-affine-alternating-cech-resolution-exchange`).
This is a decomposition, not a sorry-free mathematical proof: one upper hole closed,
two lower holes added, net holes closed minus added = -1. The core constructs the
resolution and four comparison isomorphisms, retaining a representative with finite
products of affine open pushforward terms. The exchange theorem proves only ordinary
exchange on complexes with these terms; it asserts none of the augmentation or
right-derived-unit comparisons. Neither split-off hole was closed by the second reader.

## No longer needed

Removed redundant direct proof imports from the item:
`Sheaf.AlgebraicGeometry.AffineOpenPushforwardAcyclic`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`,
`Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`, and
`Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange`.
Their required statements remain dependencies of the new core/exchange modules.
No original proof-dependency node or module becomes unnecessary in the transitive
argument; no module is claimed pruned from the targets' closure. In particular the
original model, acyclicity, affine pushforward base-change and affine sections nodes
remain used below the new nodes.

## Where the brief, the DAG or earlier work was wrong

The first worker's exchange theorem applied to an arbitrary homotopy complex D,
with no link to the Cech resolution. Its proposed proof works only on complexes
whose terms are finite products of affine open pushforwards. Repaired this by
requiring an actual complex representative with that degreewise term property,
and by making the core theorem supply it. This is a change to newly proposed
statements only; no existing declaration's signature changes.

The first worker included an unchanged copy of DerivedBaseChangeUnitCompatibility;
it was removed from the delivery. The searches recorded on the new nodes were
replaced by queries actually run during this second reading, including a valid
Loogle query after an initial unknown-identifier response.

The nonexistent local blueprint-file path is not used as new source attribution.
The source facts were checked directly in
[Stacks Tag 02KG](https://stacks.math.columbia.edu/tag/02KG) and
[Stacks Tag 02KH](https://stacks.math.columbia.edu/tag/02KH): the equality of Cech
complexes uses arbitrary affine base change; flatness is used only for passage to
cohomology, which the new exchange theorem does not assert.

## New nodes

`lem-pc-s3-affine-alternating-cech-resolution-core` records the construction,
augmentation, explicit model comparison and four resolution/unit isomorphisms,
plus the representative's degreewise affine-open finite-product term property.
Its source, proof in words and verbatim Lean statement are recorded.

`lem-pc-s3-affine-alternating-cech-resolution-exchange` records ordinary exchange
only for homotopy complexes possessing such a representative. Its proof uses
affine arbitrary base change on the open inclusion and its composite with f,
vertical pasting, finite biproducts, and naturality. Cover and quasi-compactness
hypotheses unused by this step were removed.

Change record: `coord/changes/linter-unused-variables.md`, for the target's unused
existential model-comparison binder warning suppression.

## Second reading by R3

1. Compared the item with the repository using diff and checked its complete
existing theorem signature byte-for-byte up to `:=`. Verdict: unchanged signature,
visibility, docstring and public imports; changes confined to proof imports, proof,
and recorded linter option. No existing definition changed. Removed the unchanged
extra module from the delivery.
2. Compiled every delivered module locally in import order with lcompile.py.
Verdict: no errors or non-sorry warnings, exactly the two named theorem holes
listed above, and no forbidden declarations or hollow definitions. Independent
`#print axioms` checks show exactly `propext`, `Classical.choice`, `Quot.sound`
and `sorryAx` on all three declarations; the delivery probe found no other axioms.
3. Reviewed both new statements and their edge cases. Verdict after repair: the
core handles empty covers (forcing X empty), zero and negative degrees, repeated
indices and empty finite products; the exchange handles arbitrary differentials
on its permitted terms, empty products, and nonflat base change. The original
arbitrary-D exchange statement was rejected and repaired. Mathlib searches by
leanfinder, loogle and grep, plus direct searches of upstream and lean/Sheaf,
found no exact existing result. LeanSearch returned Internal Server Error and
is recorded as unavailable. Upstream affine Cech exactness concerns the
all-tuples section complex and does not provide this representative or ordinary
exchange. Both lower lemmas have mathematical proofs in their docstrings and
matching nodes; neither is the original theorem renamed.
4. Reviewed the top-down reduction, imports and pruning. Verdict: the target
uses the core's term property in the exchange step, so the proof cannot invoke
exchange on an unrelated D. Removed redundant direct imports; all original DAG
proof dependencies are retained transitively. Read the unit record
`dag/units/sk-thm-picard-f-representable.json`; this lower-level refinement alters
none of its realized statement/step entries or its representability route.
5. Checked the Lean against the node records. Verdict: each new lean.statement
matches its declaration, proof_deps is the union of proof-step uses, and the
existing node's proof now records the representative-dependent combination.
New nodes have source, searches, creation, blueprint, chapter, unit and lean
attachment fields. Existing node fields outside the permitted proof record
are unchanged.

Second-reading changes: repaired the false arbitrary-complex exchange lemma;
retained representative term data in the core; updated the target proof and DAG;
expanded the new docstring proofs; removed unnecessary hypotheses/imports and
an unchanged extra module; replaced unverifiable searches and source attribution;
corrected the report to state the decomposition and negative net hole count.
