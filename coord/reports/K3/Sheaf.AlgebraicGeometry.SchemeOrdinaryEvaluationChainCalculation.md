## What changed

Replaced the sorry in AlgebraicGeometry.schemeOrdinaryEvaluation_chain_calculation
by an existential elimination, an application of the conditional component-action
identity, and conjunction/existential introduction. Two new proof-only imports
separate steps 1–2 (construction and augmentation, independent of F) from step 3
(the action equation for a factor map). No existing signature or definition changes.

## Proved and sorry left

Closed: AlgebraicGeometry.schemeOrdinaryEvaluation_chain_calculation
(node lem-pc-scheme-ordinary-evaluation-chain-calculation).
This is a decomposition, not a sorry-free proof of the mathematical result.
Added two holes, each strictly part of the original argument:
- AlgebraicGeometry.schemeOrdinaryEvaluation_chain_map_exists
  (node lem-pc-scheme-ordinary-evaluation-chain-map-exists).
- AlgebraicGeometry.schemeOrdinaryEvaluation_chain_action
  (node lem-pc-scheme-ordinary-evaluation-chain-action).
No sorry remains in the item's module. Net holes: 1 closed, 2 added.

## No longer needed

No modules pruned: the new obligations retain the original construction and
component-calculation route. The parent's old direct proof_deps are all transferred
into the new obligations rather than removed from the mathematical argument:
- def-pc-scheme-ordinary-evaluation-formula;
- def-pc-scheme-tensor-unit-action;
- lem-pc-sheaf-modules-tensor-closed;
- lem-pc-tensor-hom-uncurry-differential;
- lem-sc-hom-complex-projections.
The parent now directly uses only the two new nodes. No existing public imports removed,
since all three existing imports supply symbols in the unchanged public statement.
The chain-map existence obligation requires neither F nor f nor hf nor tensor-unit
action, and imports only the explicit uncurrying interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The differential module's general uncurrying
calculation is private: its public API targets only a K-injective resolution,
so it does not directly construct evaluation into the unresolved single unit.
The local compiled baseline initially lacked SchemeTensorUnitAction; unchanged
source dependencies were compiled locally only to validate the sandbox.
Zero complexes and the empty scheme give zero component equations; no boundedness,
flatness, or derived-category hypothesis was added. The conditional action lemma
is true for every factor map because eta_O is degreewise monic and hence fixes e.

## New nodes

lem-pc-scheme-ordinary-evaluation-chain-map-exists: original steps 1 and 2,
with only Y and P as parameters; construction of the evaluation chain map and
naturality in the coefficient augmentation.

lem-pc-scheme-ordinary-evaluation-chain-action: original step 3, conditional
on the first equation, but asserting only the second equation. Its proof uses
monicity to identify the supplied e's components before the ordinary formula.
No change record is needed; existing interfaces are unchanged.

## Second reading by K3

1. PASS: Diffed the existing module against the repository. Its declaration
   signature, docstring, options, visibility and definitions are unchanged;
   the only edits are two plain proof imports and the proof body. No other
   existing Lean module is delivered. The existing node differs only in proof,
   proof_deps and proof_origin. No change record is needed.
2. PASS as a decomposition: all three modules compiled through lcompile.py,
   without errors or warnings. Scratch-copy #print axioms checks of all three
   public theorems give exactly propext, Classical.choice, Quot.sound and sorryAx.
   Only the two reported new named theorems contain sorry. No definitions,
   forbidden declarations, or arbitrary data choices were added. The existential
   witness is eliminated only inside a proposition proof.
3. PASS: The existence obligation omits F/f/hf and proves only the coefficient
   factorization. The action obligation assumes that factorization and proves
   only the action equation. Neither restates the full parent theorem. Read the
   projection construction, the ordinary component predicate and tensor action.
   The signed differential argument constructs the evaluation chain map; the
   augmentation is monic by monoQuasiIso_toKInjectiveResolution_app, so the action
   hypothesis determines e. For P=0 or F=0 all applicable maps are zero; for the
   empty scheme the sheaf category is trivial. For complexes concentrated in
   single degrees the equation reduces to the tensor-Hom inverse laws and unit
   action; outside q+r=0 the single unit component is zero. Both new statements
   have complete construction/calculation proofs in their docstrings and matching
   nodes. Repeated searches using different words with LeanFinder, Loogle and rg;
   results provide component tools only. Existing unit-source evaluation lemmas
   have the wrong source, and localized naturality does not factor through the
   unresolved coefficient. The general hom_uncurry_comm calculation is private;
   neither new obligation closes by a short application of the public API.
4. PASS: The parent eliminates the first existential and applies the conditional
   second step. Its public imports supply the three interfaces in its signature;
   new proof-only imports are plain imports. New modules publicly import only
   interfaces used in their signatures. The five old direct proof_deps remain
   dependencies of the new obligations and are now listed under No longer needed
   as transferred, not pruned. sk-thm-picard-duality's existing realized fields
   are unchanged; the original construction and action route is retained.
5. PASS: Read every delivered node. Their Lean signatures are verbatim, their
   proof_deps equal the union of step uses, their proof origins describe the
   decomposition, and both new nodes have source, searches, created, blueprint,
   unit/chapter and Lean records. The parent's proof matches the Lean body.

Changed only reporting and new-node search metadata: corrected the first search
kind from leansearch to leanfinder to match searches.jsonl, recorded independent
searches, and explicitly listed transferred old proof dependencies. No Lean
proof or statement repairs were necessary. One upper hole closed, two holes
added: a decomposition with net -1 holes closed, not a completed mathematical
proof. No module pruned.

Dry-run repair: added a separate genuine LeanSearch attempt to both new nodes;
the service returned Internal Server Error, recorded as unavailable without an
absence claim. Sources also checked online at Stacks Tags [08DJ](https://stacks.math.columbia.edu/tag/08DJ),
[08DM](https://stacks.math.columbia.edu/tag/08DM) and [08DQ](https://stacks.math.columbia.edu/tag/08DQ);
the chain statements concern evaluation identities, not the perfectness-dependent
derived isomorphisms of the latter two tags.
