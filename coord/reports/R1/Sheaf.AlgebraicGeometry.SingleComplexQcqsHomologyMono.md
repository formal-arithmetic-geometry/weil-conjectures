## What changed

Implemented `AlgebraicGeometry.singleComplexBaseChange_homology_mono` without changing
its signature, universes, visibility, public imports or existing docstring. The proof
uses target locality, the existing affine comparison, quasi-compact-open induction,
and top-open normalization, then applies the homology functor to the resulting
isomorphism. Added five proof-only imports, all used by that proof.

Added `Sheaf.AlgebraicGeometry.SingleComplexOpenAffineUnion`, containing only the
Mayer--Vietoris induction step for adjoining an affine open. Its explicit three
local-isomorphism premises are essential, and it assumes neither the stalk
condition nor the global conclusion. Updated the parent node's proof route.
Both delivered modules compile individually through lcompile.py (under six seconds).

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.singleComplexBaseChange_homology_mono`
(node `lem-pc-single-complex-qcqs-homology-mono`). No sorry remains in the item's module.

Added one hole:
`AlgebraicGeometry.singleComplexOpenComparison_affine_union`
(node `lem-pc-single-complex-open-affine-union`). This is a decomposition, one hole
closed and one added, not a claim of a net reduction in the reachable sorry count.
The proof from this local gluing statement to the unchanged original statement is
complete Lean. Imported declarations may still depend on existing sorries.

## No longer needed

No original import was removed: all four public imports support the unchanged
public statement. The planned direct dependency `lem-pc-single-complex-open-union`
(module `Sheaf.AlgebraicGeometry.SingleComplexOpenUnion`) is replaced by the strictly
restricted affine-adjoining step. No import of that module or of
`Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction` remains. This does not claim
that either module is absent from other targets' import closures. The lower
Mayer--Vietoris/nested-comparison arguments are still needed to prove the new step;
none of their nodes is claimed pruned. All other planned parent dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The named `SingleComplexQcqsInduction` theorem already has precisely the needed
isomorphism conclusion, but importing it closes a source import cycle. The planned
`SingleComplexOpenUnion` import also closes a cycle (confirmed by
`tools/import_direction.py may`). The latter runs through RelativeMayerVietoris,
its pinned vertex comparisons, DerivedBaseChangeMayerVietorisMaps,
AffineGlobalHomBaseChangeMap, GlobalHomAdjunctionIso, DQCoheratorAdjunction,
DerivedQCohCompactGeneration, PerfectComplexRepresentatives, the affine direct-image
library, proper-flat coefficient results, and StandardFlatSingleBaseChangeMono,
back to this item. Thus simply copying the existing induction proof is not a
valid delivery despite compiling against cached objects. No unheld module was
changed. The new specialization isolates the needed local step with a cycle-free
statement interface. Its future proof should construct the relative Mayer--Vietoris
comparison independently of the above higher-coherence import chain; the existing
relative Mayer--Vietoris declaration cannot currently be imported here either.

Read Stacks Tag 0DJ9 at https://stacks.math.columbia.edu/tag/0DJ9: its induction step
is exactly this comparison of two relative Mayer--Vietoris triangles. The local
literature checkout lacks perfect.tex, so the authoritative online text was read.
LeanFinder and local searches found the existing project criterion; Mathlib searches
for the gluing step found no exact match, and LeanSearch returned HTTP 500, recorded
as unavailable. Blueprint searches for single-complex and Mayer found no duplicate
blueprint statement for this restricted step. The unit's realized arrays are empty;
the same target-locality/affine/source-induction/Mayer--Vietoris route is preserved.

Edge cases: empty U or V, redundant covers, zero coefficients, and arbitrary degrees
use the same distinguished-triangle argument. Affineness of V gives compactness;
quasi-separatedness gives compact intersection. There is no separatedness, flatness,
boundedness, or global-base compactness assumption added to the parent statement.

## New nodes

`lem-pc-single-complex-open-affine-union` is the strictly local affine-adjoining
Mayer--Vietoris step in `lean/Sheaf/AlgebraicGeometry/SingleComplexOpenAffineUnion.lean`.
It has the parent's chapter/unit, the source and full proof in words, and actual
logged Mathlib searches. It specializes the existing union statement to the exact
induction step while avoiding its cyclic proof imports. Its DAG proof plan records
the existing lower Mayer--Vietoris and nested-coordinate statements. No change
record is needed: no existing interface, definition, or downstream file changes.


## Second reading by R1

1. **Interfaces: PASS.** Compared the delivered parent module with the repository
   using `diff -u`. Only its proof and five plain proof imports differ. The existing
   signature, universes, visibility, four public imports, and docstring are byte for
   byte unchanged. The other module is new. No definitions or change records were
   added, and no other existing Lean module was adapted.
2. **Proof and axioms: PASS as a decomposition.** Compiled both delivered modules in
   import order through `lcompile.py --all`; both compile without warnings or errors.
   Independently compiled scratch copies with `#print axioms` for both declarations:
   each reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   Scanned the delivered Lean sources: the only literal sorry is the reported named
   `singleComplexOpenComparison_affine_union`; no forbidden declarations or hollow
   definitions occur. The parent obtains an isomorphism and uses functorial
   preservation of isomorphisms to produce exactly the requested monomorphism.
3. **Split statement: PASS with existing-result limitation documented.** Read the
   new statement, its complete docstring argument, its node, the explicit ambient
   comparison definition, nested-comparison transport, and relative Mayer--Vietoris.
   Checked the induction step against https://stacks.math.columbia.edu/tag/0DJ9.
   Affineness of V gives compactness, quasi-separatedness over affine S gives the
   compact intersection, and restricting to W=U union V supplies the required
   two-open cover. Empty opens, U=V, one open contained in the other, and zero
   coefficients introduce no exceptions. There is no stalk premise or whole-source
   conclusion in the split statement: it is strictly the local gluing part of the
   argument. Repeated searches with different wording using msearch LeanFinder and
   Loogle, and rg on both Lean roots. Mathlib has the abstract triangle isomorphism
   criterion, but not the canonical derived comparison gluing statement. The
   project's existing general union theorem subsumes this specialization, but is
   unavailable here: import_direction.py independently confirms its import would
   close a cycle back to the parent. The full qcqs criterion also closes a cycle.
   The new hole isolates this unavailable local step; it does not claim a new
   mathematical result or net sorry reduction. Closing it via the present relative
   Mayer--Vietoris proof chain would reintroduce the same cycle, so it remains open.
4. **Route and pruning: PASS.** Read the existing affine comparison, target-locality
   reduction, quasi-compact-open induction, and top normalization against each
   application in the proof. Each of the five added imports supplies a used
   declaration and is correctly plain `import`. All original public imports serve
   the signature. The old direct proof-dependency list loses only
   `lem-pc-single-complex-open-union`; it is explicitly listed under No longer needed.
   The new argument retains the target-locality/affine/source-induction/gluing route.
   Read dag/units/sk-thm-picard-coherence.json: its realized statement and step arrays
   are empty, and neither its statement nor its route is changed by this delivery.
5. **DAG: PASS.** Compared the parent node with the repository: changes are confined
   to proof, proof_deps, and proof_origin. Their steps and dependency union match the
   actual proof. Checked the new node's verbatim Lean signature, source, statement
   dependencies, complete proof plan, proof-dependency union, search records,
   creation metadata, blueprint provenance, chapter/unit, and Lean module record.
   Its lower-node citations describe the mathematical plan for the remaining hole;
   they are not claims that those cyclic modules have been imported or applied.

Second reading changed only this report: added the independent checks, axiom
results, and the explicit limitation on reuse of existing cyclic results. No Lean
proof, statement, definition, import, or node needed repair. One original hole is
closed and one local hole added; this remains a decomposition with net zero holes.
