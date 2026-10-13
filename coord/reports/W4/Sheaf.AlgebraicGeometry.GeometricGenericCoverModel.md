## What changed

Repaired reviewer X-c640f's E2 return (head c640f97a9). Removed the entire false
`AlgebraicGeometry.refine_geometric_generic_cover_model_data` declaration and
its documentation. Replaced the invalid combining proof of
`AlgebraicGeometry.exists_geometric_generic_cover_model` by `:= by sorry`.
Its signature and complete natural-language proof docstring are unchanged.

Retained the complete proof of
`AlgebraicGeometry.exists_geometric_generic_cover_model_data`, its proof-only
import `Sheaf.AlgebraicGeometry.GenericFibreClosedAvoidance`, and its updated
model-data node. For nonempty I this uses the identity model and whole-space
closed subsets. For empty I, surjective field base change forces an empty
original generic fibre, and closed avoidance gives an open neighbourhood
with empty pullback.

Cleared the main node's invalid combining proof and proof_deps. Retained the
refinement node as historical with lean null, proof [], and proof_deps []. Both
proof_origin records explain why the decomposition was withdrawn.
The interface removal is documented in
`coord/changes/refine_geometric_generic_cover_model_data.md`.
No other modules are adapted; no definitions or target signatures change.

## Proved and sorry left

Hole closed by proof: `AlgebraicGeometry.exists_geometric_generic_cover_model_data`
(node `new-lem-sbc-geometric-generic-cover-model-data`). This closes one of the
two original sorries by a genuine Lean proof using the already proved
`AlgebraicGeometry.exists_open_generic_fibre_closed_avoidance`.

Hole added relative to the repository (restored after an unsound reduction):
`AlgebraicGeometry.exists_geometric_generic_cover_model`
(node `lem-sbc-geometric-generic-cover-model`). This hole is reopened by the
repair because its previous combining proof used a false refinement.
Removed, not proved: `AlgebraicGeometry.refine_geometric_generic_cover_model_data`
(node `new-lem-sbc-geometric-generic-cover-model-refinement`). Its historical
node no longer records a Lean declaration. Zero holes split off; the removal
is not counted as a proof. One direct sorry remains in the module.

## No longer needed

The main theorem no longer uses
`new-lem-sbc-geometric-generic-cover-model-data` or
`new-lem-sbc-geometric-generic-cover-model-refinement` as proof dependencies:
the invalid decomposition is withdrawn. The refinement declaration is removed.
The proved model-data declaration remains as authorized by the reviewer.

No imports are removed in this repair. The first worker's proposed
GenericFibreClosedCoverSpread import was already replaced during the previous
second reading by GenericFibreClosedAvoidance, so the retained model-data proof
does not use `lem-sbc-generic-fibre-closed-cover-spread` or generic flatness.
The finite-separable-extension spreading, reduced closures, and irreducibility
spreading plan are unnecessary for the weak model-data conclusion. They are
still needed for a correct proof of the main theorem; no claim is made that
those modules leave the targets' closure. The unit sk-prop-normal-form has
empty realized statement and steps; no realized unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The removed refinement is false, not merely difficult to prove. Over Spec k,
take X = S = T = Spec k, the maps to be identities, I = Bool, and both A_i = univ.
Take C_false = empty and C_true = univ. The hypotheses hold. The conclusion for
C_false requires an empty geometric fibre to be IsIrreducible, which includes
nonemptiness. Also A_false intersects A_true, while C_false intersects C_true
is empty. Thus both conclusions fail.

The hypotheses do not identify the generic traces of C_i with A_i, and the
conclusion does not allow shrinking the given arbitrary model. The old combining
proof therefore does not prove the main theorem soundly. A disputed warning was
insufficient; this repair removes the false declaration and restores the main
hole without changing its true intended statement or its full proof docstring.
The historical refinement node's old statement remains only as history; its
invalid proof and Lean record have been withdrawn under the change record.

Repository-wide rg and tools/downstream.py --uses identify the sole Lean user
as exists_geometric_generic_cover_model in the same W4-held module. Its proof
is the only caller requiring repair. All downstream signatures are preserved.


## Second reading by W4

1. Compared the entire delivered module with the read-only repository and checked
   declaration tables: both retained signatures are byte-for-byte unchanged;
   no definitions or targets change. The sole removed declaration is the false
   refinement, explicitly covered by
   `coord/changes/refine_geometric_generic_cover_model_data.md`. Repository-wide
   searches confirm that its sole caller is the main theorem in this module.
   Verdict: pass as a recorded interface repair.
2. Compiled the module and a fresh scratch copy with `#print axioms` for both
   retained declarations and the avoidance theorem. The model-data theorem and
   avoidance theorem use only `propext`, `Classical.choice`, `Quot.sound`.
   The main theorem additionally uses `sorryAx`, exactly as its single complete
   named sorry predicts. No forbidden declaration forms or data holes occur.
   Verdict: model-data proved; main theorem remains open.
3. No new statement or split-off hole is introduced. Checked the nonempty index
   case (including a singleton), where the identity model and whole-space cover
   satisfy precisely the weak conclusion. For an empty index type the covering
   hypothesis makes the base-changed generic fibre empty; surjectivity onto the
   original fibre and closed avoidance yield an empty pullback on an open model.
   Independently verified the Spec k / Bool counterexample to the removed
   refinement. New LeanFinder, Loogle and grep searches found no direct replacement;
   `Scheme.isEmpty_pullback_iff` is a possible alternative for the elementary
   emptiness step, but does not replace closed avoidance. Verdict: pass.
4. Read the proof from its conclusion downward. It uses the elementary identity
   shortcut first and the already proved avoidance theorem only for empty I.
   All three public imports supply signature vocabulary; the avoidance import
   is proof-only. No unused import remains. The report lists both removed main
   proof dependencies; the model-data node formerly had no proof dependencies.
   The unit's realized statement and both realized steps are empty, and no unit
   route is replaced. Verdict: pass; no module-pruning claim.
5. Compared all three node files with the repository. Only permitted Lean/proof
   metadata fields differ. The model-data proof steps and dependency union match
   the code; the main invalid reduction is cleared and the removed refinement
   has `lean: null` and no proof. No new nodes require creation fields.
   Verdict: pass.

Second reading changed the report to distinguish the genuine model-data hole
closure from the main hole restored by repair, and refreshed the stale scratch
axiom copy. No Lean proof or node repair was needed. The removed false hole is
not counted as proved, and the main target is not counted as proved. Of the two
retained declarations, one is proved and one remains sorry; zero holes split off.
The existing model-data docstring still describes the old closure route and
mentions a refinement below; the actual shorter route is documented in this
report and its node, and the existing docstring was preserved. This declaration
is no longer a dependency of the main proof.
