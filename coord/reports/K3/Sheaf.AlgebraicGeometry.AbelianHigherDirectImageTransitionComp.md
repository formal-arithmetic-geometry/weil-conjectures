## What changed

`Sheaf.AlgebraicGeometry.AbelianHigherDirectImageTransitionComp` now proves
`AlgebraicGeometry.Etale.abelianHigherDirectImage_transition_comp` from the narrower
canonical-coefficient composition identity in the new proof-only import
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImageCoreComp`.

Repair of the import-pruning return: removed both private generic lemmas
`AlgebraicGeometry.Etale.transition_naturality` and
`AlgebraicGeometry.Etale.coefficient_transition_naturality`. Their existing copies
in `HigherDirectImageTransitionNaturality` are private and cannot be used by an
importer. The repaired proof instead uses Mathlib's `NatTrans.naturality`:
whisker the derived unit, pullback comparison and counit to obtain the transition
natural transformation, compose with the single-complex comparison, and whisker
with homology. Its naturality equation supplies the coefficient argument directly.
No generic naturality theorem is restated or reproved, and no module-coefficient
specialization is imported. The DAG proof text now records this construction.

The remaining private helpers prove coefficient postcomposition, abelian
coefficient naturality, arbitrary-coefficient composition and equality transport.
The final proof uses `D.map_comp`, `hφcomp`, and proof irrelevance.
All existing public signatures, visibility, and docstrings are unchanged.
The hypothesis `hφid` is not needed for composition and remains in the signature.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.abelianHigherDirectImage_transition_comp`
(node `lem-sbc-abelian-higher-direct-image-transition-comp`). No sorry remains in
the item's module or in its private helpers.

Added one hole:
`AlgebraicGeometry.Etale.abelianHigherDirectImage_core_comp`
(node `lem-sbc-abelian-higher-direct-image-core-comp`), in its own new module.
This is a decomposition: one upper hole closed and one lower hole added, not a
sorry-free proof or a positive net hole count. The lower theorem treats only a
single sheaf and canonical pullback coefficients, without arbitrary coefficient
maps, an indexing diagram, or coefficient coherence hypotheses. The original
proof supplies the entire coefficient-naturality and diagram-transport argument.
Its remaining geometric argument is documented in the new theorem and DAG node.

## No longer needed

No original import was removed. No original dependency node or module is pruned:
derived adjunction, inverse-image composition, and derived inverse image all remain
needed, directly for naturality or below the canonical-coefficient identity.
The two duplicate generic helper declarations are removed. An experimental direct
Mathlib Whiskering import was also removed: the original statement imports already
expose its constructions, so the repaired proof adds no further import.
The new module imports only `AbelianHigherDirectImageMap`, sufficient for its
statement. The module-coefficient analogue and its continuity-related dependencies
are not imported and do not enter this proof.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two private generic lemmas already stated in
`HigherDirectImageTransitionNaturality`. The earlier report incorrectly treated
the lack of a public abelian specialization as sufficient reason to copy those
lemmas. This repair deletes both copies and uses the existing Mathlib naturality
interface instead. No statement or definition change, forced adaptation, or new
hole was needed to repair the return. The previous second reading covered the
returned version and has been removed so the second reader can review this repair.

## New nodes

`lem-sbc-abelian-higher-direct-image-core-comp`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-abelian-higher-direct-image-core-comp.json`,
states the canonical pullback-coefficient case of the original geometric composition
step. Its docstring and proof steps explain adjunction transposition, cancellation,
derived inverse-image associativity, single-complex compatibility and homology.
Identity maps, zero sheaves and degree zero need no extra hypotheses. LeanSearch was
unavailable; LeanFinder found ordinary scheme/module pullback composition, and grep
found no relevant derived comparison. The whole blueprint search for transition
composition and Tag 09Z1 found no abelian canonical-coefficient duplicate. There are
no change records or forced adaptations, since no existing interface was changed.


## Second reading by K3

1. Compared both delivered modules with the repository. The existing public theorem's
   signature is byte for byte unchanged, including hφid and hφcomp; its docstring and
   visibility also agree. The only new import in that module is proof-only. No existing
   definition, target, or external module is changed. No change record is required.
2. Both files compile locally in import order. A scratch copy with `#print axioms`
   checks the public theorem, all four private helpers and the new core theorem:
   only propext, Classical.choice, Quot.sound and the permitted sorryAx occur.
   Coefficient postcomposition, naturality and transport have no sorryAx. The only
   delivered sorry is the named core theorem, with its proof docstring and matching
   node; there are no definitions or forbidden trust mechanisms in the delivery.
3. Read the split identity against the definition of abelianHigherDirectImageMap.
   Its comparison has the correct orientation (ba)^*F → b^*a^*F; both composite
   maps have exactly the same source and target. Identity triangles reduce to
   adjunction triangle identities and coherent pullback unit comparisons; zero F
   gives maps between zero objects; p = 0 is the ordinary comparison on sheaves.
   None needs a positivity, cartesianness or properness assumption. This is strictly
   the canonical-coefficient part: arbitrary coefficient naturality and diagram
   transport are actually proved above it, rather than restated as another hole.
   Independently searched using adjunction-comparison terminology and read the
   upstream derived coherence and module-coefficient transition/single comparison
   files. Mathlib supplies adjunction primitives; the public local analogues require
   ModuleCat coefficients and their generic single helpers are private. No usable
   duplicate for this AddCommGrpCat statement was found. Closing the core requires
   derived adjunction composition and single-complex coherence together, rather
   than a short application of an existing public theorem.
4. Read the proof top down. It factors coefficients, obtains naturality directly
   from Mathlib's NatTrans.naturality of whiskered transformations, applies just
   the canonical core identity, and transports D.map_comp and hφcomp by equality.
   Imports are needed: AbelianHigherDirectImageMap supplies the statement and
   construction, Coherence supplies upperStarId in hφid, and CoreComp supplies the
   proof. All three old proof dependencies remain used, so the pruning list is
   complete (none). The unit sk-lem-failure-field has empty realized fields in the
   repository; this auxiliary node does not replace or bypass any realized step.
5. Checked both node Lean statements verbatim against their declarations. The
   revised upper node's proof and proof_deps describe the four private helpers and
   the core application accurately. The new node has its source, complete proof
   steps, dependencies, searches, creation/blueprint metadata and Lean record.
   Existing node changes stay within proof, proof_deps and proof_origin.

Verdict: passes as a decomposition (one original hole closed, one narrower hole
added, net zero), not as an axiom-free completion. No Lean repair was necessary.
Second reading added independent search evidence to the new node and this review;
the compiled proofs and their signatures are unchanged.
