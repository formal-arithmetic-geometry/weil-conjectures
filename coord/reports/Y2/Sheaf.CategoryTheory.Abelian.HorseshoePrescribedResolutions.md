## What changed

Proved `CategoryTheory.InjectiveResolution.exists_horseshoe_prescribed_resolutions`
from a new fixed-initial-row construction theorem, without changing its signature.
The Lean proof performs the initial injective extension and proves its monomorphy.
It then proves all resolution verification: injective middle terms using split rows,
positive-degree exactness using the homology sequence, the augmentation quasi-isomorphism
including degree zero, and both equations for every degreewise biproduct isomorphism.
Added proof-only imports of `HomologicalComplexAbelian`, `HomologySequenceLemmas`, and
`Sheaf.CategoryTheory.Abelian.HorseshoePrescribedRows`.
Updated the parent node's proof and dependencies to match this reduction.
Both modules compile without warnings through lcompile.py (about 1--2 seconds each).

## Proved and sorry left

The item's one original sorry is closed by a complete Lean proof from named statements.
The sole new sorry is
`CategoryTheory.InjectiveResolution.exists_horseshoe_prescribed_rows`, node
`lem-sp-horseshoe-prescribed-row-construction`, module
`Sheaf.CategoryTheory.Abelian.HorseshoePrescribedRows`.
It only extends a fixed initial embedding to a complex with exact rows and degree-zero
exactness. It does not supply an injective resolution, positive-degree exactness,
a quasi-isomorphism, or the final degreewise biproduct identifications.
Those are proved in the parent rather than assumed under a renamed theorem.
The existing snake-lemma dependency remains below this construction.

## No longer needed

No existing node or module is pruned from the target's reach: the original injectivity
and snake-lemma ingredients remain necessary in the construction node.
Removed `lem-weil-pbc-snake-lemma-abelian` from the parent
`proof_deps`: the parent no longer applies the snake lemma directly. It remains in
`proof_deps` of `lem-sp-horseshoe-prescribed-row-construction`, so it is not pruned
from the target closure. There were no original imports to remove. Removed two experimental,
unneeded proof imports (`Mathlib.Algebra.Homology.QuasiIso` and
`Mathlib.CategoryTheory.Preadditive.Biproducts`) after successful compilation without them.
Do not use `HorseshoeResolutions` as an input: it already imports this item.

## Where the brief, the DAG or earlier work was wrong

The listed proof dependencies supply injectivity and the snake lemma but do not supply
an existing declaration that carries out the recursive horseshoe assembly.
The previous plan hid this construction inside its induction step; it is now a named
Lean statement with its full cokernel induction recorded in its docstring and node.
No target statement or existing definition was changed.
The designated local Stacks source file is absent on this machine. Read the official
page https://stacks.math.columbia.edu/tag/013T instead. The parent's source attribution
mentions a last sentence prescribing both outer resolutions, which is absent from the
current official statement. Its Step 2 does describe the biproduct construction;
the fixed-outer-resolutions object version follows the parent's cokernel argument.
This is a citation issue, not a counterexample or a reason to weaken the statement.
The recorded unit's realization lists are empty; this delivery does not alter the unit
or chapter route and keeps the prescribed-endpoint horseshoe construction.

## New nodes

`lem-sp-horseshoe-prescribed-row-construction` is in
`dag/nodes/sec-abelian-varieties/lem-sp-horseshoe-prescribed-row-construction.json`.
Its Lean module is `lean/Sheaf/CategoryTheory/Abelian/HorseshoePrescribedRows.lean`.
The source is the object horseshoe construction associated with Tag 013T, specified
as a cokernel induction with a fixed initial lift. Search found no Mathlib constructor
for compatible prescribed rows. LeanFinder and Loogle returned single-resolution
operations and row splitting; grep found no horseshoe implementation; LeanSearch
returned Internal Server Error and is recorded as unavailable.
Small cases checked: if either end is zero, the construction specializes to extension
of the remaining prescribed resolution; if the sequence splits, any initial lift may
differ by a map through C, and the next embeddings absorb this difference.
No assertion requires the given initial lift itself to be mono: its pair with the
right augmentation is mono, as proved explicitly in the parent. No change records.


## Second reading by Y2

1. **Existing interface unchanged: pass.** Read the complete repository/sandbox
   `diff -u` for `HorseshoePrescribedResolutions.lean`. The only Lean changes are
   three plain proof imports and the body replacing its original `sorry`.
   The existing declaration's signature, namespace, universes, public import,
   and docstring are byte for byte unchanged. No definition or target changed,
   and no change record is required. The second module is new.
2. **Kernel-checked reduction: pass, with one explicit open dependency.** Compiled
   both modules together through `lcompile.py --all`, without errors or warnings.
   Scanned the delivered Lean for forbidden declarations and attributes: none.
   The only `sorry` is the complete body of the new named row-construction theorem;
   there are no definitions or hidden proof holes. Scratch copies with
   `#print axioms` show exactly `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` for both theorems. Thus the parent has no local sorry but is not yet
   an axiom-free proof of the horseshoe lemma: its row construction remains open.
   Read the initial extension/mono proof, splitting and injectivity transfer,
   degree-zero exact-and-mono quasi-isomorphism criterion, positive-degree
   homology argument, and both biproduct equations. They prove the stated clauses.
3. **Split statement and proof: pass.** Read the full new Lean statement and its
   docstring against its new node. The initial lift is arbitrary subject to its
   restriction along S.f; pairing with S.g followed by the right augmentation is
   mono, without a mono assumption on the lift. In the induction the outer
   cokernels embed in the next prescribed terms by resolution exactness; extending
   the left embedding and pairing with the right embedding gives the next mono
   middle embedding and a short exact cokernel row. Quotient-then-embedding
   differentials have zero square and commute with the row maps. This also proves
   the required degree-zero exactness. Checked the zero sequence, either zero
   endpoint (allowing a nonzero acyclic resolution of zero), and a split initial
   sequence with an arbitrary lift: the same argument works. No EnoughInjectives
   assumption is needed because all terms used are supplied injectives.
   The lemma isolates assembly, not a renamed resolution conclusion: injectivity,
   positive-degree exactness, the augmentation quasi-isomorphism, and the final
   biproduct equations are derived in the parent. The fixed degree-zero lift is
   used to prove the augmentation mono.
   Repeated Mathlib searches via msearch.py with different queries: LeanFinder
   for extending a degree-zero monomorphism into fixed injective endpoint
   complexes; Loogle `CochainComplex, CategoryTheory.ShortComplex.ShortExact`;
   grep `injective.*(cokernel|short.exact)|cokernel.*injective` in
   CategoryTheory/Abelian. Results were general factorizations, truncation and
   mapping-cone short exact sequences, not this constructor. Searched repository
   lean/ and the upstream abelian-resolution modules as well. Existing horseshoe
   existence imports this item and cannot supply it without a cycle. Consulted
   https://stacks.math.columbia.edu/tag/013T: Step 2 supplies the biproduct idea,
   while the fixed-endpoint cokernel induction is the explicitly recorded agent
   adaptation; the source does not state a last sentence prescribing both ends.
4. **Route and pruning: pass.** The parent uses Mathlib's initial extension,
   mono-diagram lemma, injective splitting, homology sequence, and degree-zero
   criterion before leaving only recursive assembly open. There is no quick
   library replacement or few-minute proof of that assembly. Scratch deletion
   tests confirm `HomologicalComplexAbelian` is required for
   `shortExact_of_degreewise_shortExact`, and `HomologySequenceLemmas` for
   `exactAt_X₂`; the new row module is used explicitly. All added imports are
   proof-only and the public Resolution import is required by the signature.
   The old direct snake dependency is removed from the parent but retained below
   the construction, as now explicitly listed under No longer needed. No old
   dependency becomes unreachable from the target. Inspected
   dag/units/sk-prop-av-pqf-finite.json: its realization lists are empty, unchanged;
   no unit statement or route is bypassed by this prescribed-endpoint argument.
5. **DAG/Lean agreement: pass.** The parent proof steps and proof_deps match the
   initial embedding, construction, splitting, degreewise short exactness and
   homology exactness actually used. The corresponding existing nodes are
   Mathlib matches for splittingOfInjective, the degreewise short-exact criterion,
   and homology_exact₂ (used through exactAt_X₂). The new node has its full
   signature, source, complete induction, statement/proof dependencies, agent
   proof origin, three successful search kinds, split status, creation record,
   blueprint origin, chapter/unit and Lean record. Its Lean signature matches the
   module verbatim. Existing-node edits are confined to proof, proof_deps and
   proof_origin. The inherited inaccurate parent source attribution is reported
   above; it is not a statement change or a reason to weaken the theorem.

Second reading changed only the report: made the removal of the parent's direct
snake-lemma dependency explicit and recorded this independent review. No Lean or
node repairs were necessary.
