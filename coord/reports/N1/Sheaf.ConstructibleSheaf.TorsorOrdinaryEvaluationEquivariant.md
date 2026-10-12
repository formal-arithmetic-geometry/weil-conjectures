## What changed

Proved `AlgebraicGeometry.Scheme.GaloisCover.ordinarySectionEvaluation_equivariant`
with its signature and docstring unchanged. Added the proof-only import
`Sheaf.ConstructibleSheaf.TorsorNormalizedGraphEvaluation` and the proved private
helper `AlgebraicGeometry.evaluation_of_local_presentation`.

The open fibre of ordinary graph evaluation supplies a pointed etale neighbourhood.
Injectivity of the existing graph-evaluation theorem proves the local section equality.
Naturality and diagonal normalization evaluate the section there. Changing its map to
the torsor by the deck transformation and restricting its label by the inverse deck
transformation gives the desired equivariance. The elaboration transparency option is
scoped to the two proofs. The node's proof, dependencies and origin follow this argument.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.GaloisCover.ordinarySectionEvaluation_equivariant`.
The private helper `AlgebraicGeometry.evaluation_of_local_presentation` is fully proved.
There are no `sorry`s in the delivered module, and no new holes or nodes are added.

The proof uses the existing
`AlgebraicGeometry.Scheme.GaloisCover.ordinaryGraphEvaluation_bijective`
(node `lem-weil-pbc-torsor-normalized-graph-evaluation`), which remains `sorry` in its
own module. This is a proof from an existing stated dependency, not a claim that the
whole import closure is axiom-free. Local compilation is clean, with no warnings.

## No longer needed

No original imports were removed: both public imports are needed by the unchanged
statement. The retained attempt's provisional `TorsorSectionLocalPresentation` module
and `lem-weil-pbc-torsor-section-local-presentation` node are discarded. Its provisional
`ordinarySectionEvaluation_equivariant_of_local_presentation` theorem and
`lem-weil-pbc-torsor-ordinary-evaluation-equivariant-local` node are discarded as well.
Neither new statement is required: local presentation follows from existing graph
evaluation, and the deck calculation is proved directly. These were sandbox proposals,
not landed library modules; they do not count as pruning landed modules.

The old direct proof dependencies no longer used directly are
`def-weil-connected-scheme`, `def-weil-pbc-inverse-image`, and
`def-weil-pbc-constant-sheaf`. These remain statement dependencies and enter the
existing normalized graph-evaluation theorem; they are not pruned from the statement,
its mathematical prerequisites, or the import closure. No landed module is pruned.
No realized step of `sk-thm-p1` is bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained attempt unnecessarily left two holes, included overlong Lean lines, used
placeholder new-node statements, and wrote a second-reading section that belongs to
the independent reader. This delivery replaces that attempt with a proof from the
existing graph-evaluation declaration and removes its provisional nodes and second
reading. The original DAG's local-section argument is valid; its presentation can be
obtained from normalized graph evaluation rather than new unproved theory.

The graph-evaluation module was initially absent from the copied compiled library.
Once the refreshed build included it, the existing theorem could be used and both
provisional holes eliminated. The module's new import is acyclic (`import_direction.py may`).


## Second reading by N1

1. **Interfaces: pass.** Compared the sole delivered Lean module with the repository
   by `diff` and checked the existing theorem's signature byte for byte. Its signature,
   docstring, visibility, and both public imports are unchanged. The only additions
   are a plain proof-only graph-evaluation import, a proved private helper, scoped
   elaboration options, and the proof. No definition or target is changed; no change
   record or forced adaptation is needed.
2. **Proof and axioms: pass.** Independently compiled the module using `lcompile.py`
   without errors or warnings and scanned for forbidden declarations and holes.
   There are no local `sorry`s or forbidden constructs. In a scratch copy,
   `#print axioms` for `evaluation_of_local_presentation` gives only `propext`,
   `Classical.choice`, and `Quot.sound`; the main theorem gives those plus `sorryAx`
   from the existing `ordinaryGraphEvaluation_bijective`. All local objects are
   explicitly constructed; no arbitrary witness is chosen from an unproved theorem.
3. **Split statements: pass (none).** No new public statement, node, or hole is split
   off. Read the existing graph-evaluation theorem used for injectivity: it assumes
   neither equivariance nor this result, so the reduction is not circular. The local
   helper follows directly from naturality and diagonal normalization. Checked the
   empty-object case (no point to evaluate), zero coefficients, and the identity
   group: the same construction and inverse-deck identities apply.
4. **Route and pruning: pass after report repair.** Read the proof from the goal down:
   the open fibre of the explicitly defined graph value gives a pointed neighbourhood;
   graph-evaluation injectivity identifies the two restricted sections; naturality
   evaluates the label; inverse-deck cancellation gives equivariance. Searched the
   library by graph, section, and deck terminology and inspected the Mathlib open-fibre
   and pullback identities. Existing equivariant graph results already assume the
   property being proved and cannot replace ordinary graph injectivity. All three
   imports are needed, and the added import is correctly private to the proof.
   Checked `dag/units/sk-thm-p1.json` and its `realized` steps: none is bypassed.
   The report now explicitly names every old direct proof dependency removed.
5. **DAG agreement: pass.** Compared both node records: only `proof`, `proof_deps`,
   and `proof_origin` change. The unchanged Lean statement record matches the module.
   The three proof steps describe the actual local construction, helper application,
   and deck calculation; their dependency union equals `proof_deps`. No new node
   requires additional fields or searches.

Second reading changed only this report: made the three removed direct proof
dependencies explicit and added these independent review findings. The Lean proof
and node record needed no repair. Closed one original hole, added zero holes;
this is a proof from an existing open dependency, not a new decomposition or a
claim of an axiom-free target closure.
