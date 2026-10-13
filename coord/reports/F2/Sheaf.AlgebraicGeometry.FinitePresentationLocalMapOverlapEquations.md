## What changed

Replaced the hole in `AlgebraicGeometry.finitePresentation_local_maps_eventual_overlap_equations`
by a finite common-bound argument over ordered pairs of cover indices, construction of a
componentwise descent morphism, and composition with the arbitrary prescribed maps κ and ρ.
The theorem signature is unchanged. Finite presentation and quasi-coherence of tensor pullbacks
are transferred through uniqueness of left adjoints. Affineness is proved by base change.
Added a real generic pairwise compatibility predicate and its proved morphism constructor
in `Sheaf.AlgebraicGeometry.LocalMapPairCompatibility`, to avoid unfolding chosen
pullback models while checking component squares. Added the independent single-pair obligation in
`Sheaf.AlgebraicGeometry.FinitePresentationLocalMapPairEventually`.

## Proved and sorry left

Closed in the main module: `AlgebraicGeometry.finitePresentation_local_maps_eventual_overlap_equations`
(node `lem-pc-fp-local-map-overlap-equations`). Added one hole:
`AlgebraicGeometry.finitePresentation_local_map_pair_eventually`
(node `lem-pc-fp-local-map-pair-eventually`). This is a decomposition, with net zero holes closed,
not a complete proof of overlap descent. The lower statement concerns one ordered pair,
requires no finite cover, asserts no assembled morphism or affineness of the whole cover,
and has no arbitrary outer composition maps. The main proof supplies those missing steps.

Validation: all three delivery modules compile locally. The published snapshot initially
lacked `LocalMapPullbackFamily` and `LocalMapRecovery`; they became available during the
final dry runs. The main proof's unused binder and heartbeat-comment warnings were fixed.
The generic compatibility interface compiles without holes; the single-pair obligation
is the only newly added hole. The 60-second per-file subprocess limit is unchanged.
No scratchpad file is part of the delivery.

## No longer needed

Removed the direct proof import of `Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent`;
the single-pair obligation uses its proved test-scheme wrapper instead. The zero-map theorem
remains transitively needed, so no module is claimed pruned from the targets' import closure.
No unit-level route is bypassed. The unit record has no realized node naming this auxiliary item.

## Where the brief, the DAG or earlier work was wrong

The original plan correctly identifies the overlap-defect argument but combines the
single-pair comparison calculation, finite simultaneous bound, and arbitrary outer composition
in one step. The delivery exposes only the first part as its remaining obligation.
The new statement was checked on empty overlaps, equal pair indices, zero modules,
identity transitions, and a singleton directed preorder; it needs neither Noetherianity nor
local finite presentation or quasi-compactness of f. A supplied k ensures the index type is nonempty.
The blueprint ancestor search tool returned no ancestor for this created item;
the new node follows the existing item's recorded `blueprint.from.node` instead.

## New nodes

`lem-pc-fp-local-map-pair-eventually` isolates persistent compatibility of one pair of prescribed
local maps. Its complete defect-vanishing proof is in its docstring and node; its existing
proof dependency is `lem-pc-fp-test-map-zero-eventually`. The node's source is Stacks Tag 01ZR (3),
first proof by Zariski gluing. LeanFinder, Loogle and grep searches ran; LeanSearch returned
HTTP 500 and is recorded as unavailable. Blueprint searches for `local map overlap` and `01ZR`
found no equivalent imported blueprint statement. The generic compatibility node `def-pc-local-map-pair-compatibility` adds only a
real Prop structure and a fully proved constructor and component API. No existing
interface changes or forced adaptations.

## Second reading by F2

1. Compared the delivered overlap module against the repository version. The theorem signature and all existing declarations are unchanged; only proof code, proof-only imports, and the documented auxiliary modules differ. Verdict: pass.

2. Compiled the generic compatibility module and the single-pair module locally, and inspected declarations for forbidden constructs. The generic constructor is proof-complete; the only remaining `sorry` is the named single-pair theorem, matching its node. Verdict: pass subject to the documented split.

3. Reviewed the split statement and node. The single-pair proposition is strictly weaker than the original finite-cover overlap theorem, has a source, proof sketch, and edge-case discussion, and introduces no hollow definition. Verdict: pass.

4. Checked the proof route and imports. The finite common-stage argument, tensor-pullback properties, pairwise theorem, and descent assembly follow the unit route; the former direct zero-map import was removed and retained transitively through the pair theorem. Verdict: pass.

5. Checked DAG agreement. The main node proof dependencies now match the declarations used in the proof, and the added pair node records its module, declaration, source, proof, and blueprint relation. Verdict: pass.

Changed after review: added a theorem-scoped unused-variable linter setting for the pre-existing unused `V₀` let binder, retaining the signature unchanged. All three modules compiled. A scratch import with `#print axioms` for both eventual theorems and both constructor declarations showed only `propext`, `Classical.choice`, `Quot.sound`, and the documented `sorryAx` on the eventual theorems. Also corrected the main DAG proof’s first step to mark the tensor/native pullback transfer as elementary, rather than incorrectly citing the pair-compatibility constructor. The proof and all signatures remain unchanged. Independent repository and Mathlib searches for eventual pair compatibility found no existing replacement. The removed direct proof dependency is `lem-pc-fp-zero-map-descent`; it remains transitively used by the split theorem.

Preflight documentation repairs: recorded all three search kinds and the parser-level structure signature in the generic node. Added `coord/changes/finitePresentation_local_maps_eventual_overlap_equations-local-attributes.md` for the conservative attribute-command interface flag; no definition or theorem statement changed, and no downstream adaptations are needed.
