## What changed

Closed all four direct holes in `Sheaf.Paper.HypercoverFreeResolution` by applying
the already-existing declarations of
`WeilConjectures.AlgebraicGeometry.HypercoverFreeResolution`. All four signatures
are identical apart from their names, including universe levels, qcqs hypotheses,
canonical augmentation maps, injectivity of the degree-zero section map, its
kernel/range assertion, and positive-degree homology vanishing. Lean checked all
four direct applications successfully. No declaration signature, docstring,
visibility, definition, instance, or public import changes.

Added the single proof-only import of the canonical source module and removed
three unused proof-only imports. Reattached the existing node
`lem-weil-pbc-hypercover-free-resolution` to the canonical source declarations;
the unchanged mathematical proof plan and dependencies remain available for
proving those obligations. The item retains its existing compatibility theorem
names and interface for the parent modules.

No parent module is adapted. The delivery checkout refused the attempted
withdrawal/import replacement because `Sheaf.Paper.HypercoverCohomologyAbelian`
is held by another group and the import replacement is not forced by a compiler
failure. Retaining the existing theorem signatures avoids that adaptation.

Validation: `lcompile.py` accepted all four source applications in the item's
original signatures (19.3 s). The required dry run recompiles the final version. Its optional shared cache
was disabled with the supported `WEIL_DELIVERY_CACHE_DISABLE=1` setting after
prolonged contention on `library-builder.lock`; no validation check is disabled.
LeanFinder, Loogle, and Mathlib grep were run through `msearch.py`. No competing
Mathlib hypercover resolution theorem was found; the exact matches were found
by `rg` in the source library. The import-direction check permits the new import.

## Proved and sorry left

The following four direct `sorry` proofs are closed by reuse of existing library
declarations (all belong to `lem-weil-pbc-hypercover-free-resolution`):

- `AlgebraicGeometry.SplitEtaleHypercover.freeAbelian_augmentation_quasiIso_sheaf`
- `AlgebraicGeometry.SplitEtaleHypercover.injective_abelian_section_cohomology_sheaf`
- `AlgebraicGeometry.SplitEtaleHypercover.freeModule_augmentation_quasiIso_sheaf`
- `AlgebraicGeometry.SplitEtaleHypercover.injective_module_section_cohomology_sheaf`

No `sorry` remains in the item, and no hole or split-off is added. The canonical
source module enters the current target import closure: its four pre-existing
holes replace the four duplicate item holes, so that consolidation alone closes
no mathematical obligation. Eight Sheaf modules are pruned; seven pre-existing
direct holes in those modules leave the current target import graph. The pinned
sorry ledger remains the authority for progress accounting. This consolidates
duplicate obligations; it does not claim a new mathematical proof of the four
canonical source results. The unchanged source module still has its four existing
holes, now named by the existing node's Lean attachment:

- `AlgebraicGeometry.SplitEtaleHypercover.freeAbelian_augmentation_quasiIso`
- `AlgebraicGeometry.SplitEtaleHypercover.injective_abelian_section_cohomology`
- `AlgebraicGeometry.SplitEtaleHypercover.freeModule_augmentation_quasiIso`
- `AlgebraicGeometry.SplitEtaleHypercover.injective_module_section_cohomology`

## No longer needed

Removed these unused proof imports from the item:

- `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`
- `Sheaf.CategoryTheory.MatchingObjectCoskeleton`
- `Sheaf.Paper.CechNerveFreeHomology`

The current project's import graph loses these Sheaf modules from the
`TargetsCheck` import closure (repository graph compared with the proof-import
replacement; the item itself remains as a compatibility module):

- `Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan`
- `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`
- `Sheaf.CategoryTheory.CoskeletonMatchingTuples`
- `Sheaf.CategoryTheory.MatchingObjectCoskeleton`
- `Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`
- `Sheaf.Paper.CechNerveFreeHomology`
- `Sheaf.Paper.ImagePresheafSheafificationIso`
- `Sheaf.Paper.TrivialKanHomotopyEquivalence`

Their corresponding nodes are:

- `lem-weil-pbc-coskeletal-map-trivial-kan` (`Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan`)
- `lem-weil-pbc-coskeleton-free-homology-comparison` (`Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`)
- `lem-weil-pbc-coskeleton-matching-tuples` (`Sheaf.CategoryTheory.CoskeletonMatchingTuples`)
- `lem-weil-pbc-matching-object-coskeleton` (`Sheaf.CategoryTheory.MatchingObjectCoskeleton`)
- `lem-weil-pbc-truncated-coskeleton-finite-limits` (`Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`)
- `lem-weil-pbc-cech-nerve-free-homology` (`Sheaf.Paper.CechNerveFreeHomology`)
- `lem-weil-pbc-image-presheaf-sheafification-iso` (`Sheaf.Paper.ImagePresheafSheafificationIso`)
- `lem-weil-pbc-trivial-kan-homotopy-equivalence` (`Sheaf.Paper.TrivialKanHomotopyEquivalence`)

These branches are unnecessary for the compatibility proofs. The canonical
source obligations remain open; their future proofs may use the existing Cech
and coskeleton lemmas. The canonical node's mathematical dependency list and
source proof plan are retained, rather than claiming those mathematical steps
have been proved or are no longer needed by the source obligations.

## Where the brief, the DAG or earlier work was wrong

The assigned module duplicates four declarations already present in the source
root, differing only by the `_sheaf` suffix. Reusing those declarations is the
shortest route required by principle 2 and removes the four duplicate direct
proof holes without adding new statements. The node's former Lean attachment
pointed to the duplicate; its new attachment points to the source obligations.

The local shared checkout appeared to show both direct parents as unclaimed,
but the delivery checkout's claim check refused an unforced adaptation. No
parent changes or withdrawal are included in this final delivery. No target
statement or definition changes, and no source statement is disputed.


## Second reading by R2

1. I compared the delivered module with the repository version. All four existing theorem signatures are byte for byte unchanged; only proof bodies and imports changed. The node now records the canonical source declarations used by the proofs, with no target or definition changes.

2. I compiled the module with `lcompile.py`; it succeeds without errors. The four compatibility theorems have only the permitted foundational axioms plus `sorryAx` inherited from the still-open canonical source theorems. There are no new `sorry`s, axioms, unsafe declarations, hollow definitions, or split-off statements.

3. The proofs are direct applications of the corresponding canonical declarations in `WeilConjectures.AlgebraicGeometry.HypercoverFreeResolution`. I searched the local library and Mathlib for competing declarations and found no alternate theorem that would improve the route. The import is proof-only, and the three prior Sheaf proof imports are unused and removed.

4. The canonical node and its unit route remain intact: the source node retains its original Stacks proof plan and dependencies. The compatibility module is a reduction to those canonical declarations, so it does not bypass the unit's mathematical route. The report's pruning list names the imports and nodes no longer needed by this module.

5. The DAG Lean attachment names the canonical source declarations, which still have their original holes; its retained proof, proof_deps, and proof_origin describe their outstanding mathematical argument. This agrees with the compatibility reduction and avoids falsely marking those source obligations as proved. No new statement or node was added. I corrected the report's claim of zero closure change: consolidation replaces four direct holes with four existing ones, while the eight pruned Sheaf modules contain seven further direct holes. The unit realized record is unchanged and contains no entry for this node. I independently verified the signatures, four axiom reports, searches, and import graph. The optional delivery cache is disabled using its supported setting because its builder lock was contended; no validation check is disabled.
