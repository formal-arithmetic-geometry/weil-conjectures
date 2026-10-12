## What changed

Repaired `lean/Sheaf/ConstructibleSheaf/ConstantFiniteFreeDualNaturality.lean` after landing was refused by `import_prune_check.py`. The four private declarations duplicating the existing `ModuleCat` contraction statements were removed. Their calculations are now local proofs inside `finiteFreePairing`, so no duplicate library declarations are introduced and the public theorem and all signatures remain unchanged.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.Scheme.constantFiniteFreeDualNaturality` (node `lem-constant-finite-free-dual-naturality`). Added zero holes. No `sorry` remains in the delivered module; no statement was split off. The explicit axiom checks of the theorem and all named helpers show only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The four private duplicate declarations `contractLeft_zag`, `contractLeft_zag'`, `contractLeft_zig`, and `contractLeft_zig'` are no longer needed as declarations; their proof calculations remain inline where used. No imports or DAG nodes were removed.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced private declarations whose statements duplicated contraction lemmas already present in the imported ModuleCat closed-monoidal source, causing `import_prune_check.py` to reject the landing. The repair keeps the same explicit pairing proof while avoiding those duplicate declarations. The original target statement and DAG node are unchanged.

## Earlier second reading (a previous round; superseded)

A second reading verified the repaired module compiles with `lcompile.py`, preserves the target theorem signature and all public interfaces, and contains no `sorry`. The local contraction calculations are strictly proof-local and do not recreate imported declarations. The existing DAG node and change record remain applicable.

The related change record is `coord/changes/constant-finite-free-dual-private-helpers.md`.

## Second reading by C1

1. Compared the sole delivered module with its repository version. The existing public
   theorem signature is byte for byte identical, with the same universes, commutative-ring
   hypothesis, every natural number, and every linear map. Added declarations are private;
   the monoidal instance is local. No public imports or definitions changed. Verdict: pass.
2. Compiled the module locally without errors or warnings. Compiled a scratch copy with
   `#print axioms` for coefficient evaluation, its curried comparison, both naturality
   lemmas, the explicit finite-free pairing, comparison invertibility, and the target.
   Every result uses only the three allowed axioms, with no `sorryAx`. No forbidden
   declaration or holed definition occurs. Coevaluation is the explicit coordinate sum,
   not an arbitrary witness chosen from an unproved existence result. Verdict: pass.
3. No new public statement, new node, or split-off hole is delivered. Checked the local
   triangle calculations against the upstream ModuleCat dual-basis proofs: those helpers
   are private upstream, so they cannot be applied here. The coordinate decomposition and
   tensor extensionality prove both triangles, also for rank zero and the zero ring.
   Naturality is evaluation of both composites as φ(g(x)) for arbitrary modules and maps.
   Searched the library for dual comparisons and exact-pairing transport; the existing
   nonempty comparisons do not give the naturality square required here. Verdict: pass.
4. The proof uses the existing proved exact-pairing transport and invertible-curried-
   evaluation results; it introduces no lower holes. All proof-only imports are plain
   imports; the public imports supply types and monoidal-closed instances in the signature.
   Scratch compiles removing each proof import failed respectively on `contractLeft`,
   `BraidedCategory.exactPairing_swap`, and `ExactPairing.map`; all three are needed.
   The old node has no proof dependencies, so there are none to list as removed.
   Checked `dag/units/sk-thm-p1.json`: this node is below the unit's realized steps and
   bypasses none of them. Verdict: pass.
5. Read the delivered node against the proof. Its four steps correctly describe the
   coordinate pairing, monoidal sheafification and transport, curried naturality, and
   inversion/cancellation. `proof_deps` remains empty, and `proof_origin` names the actual
   upstream calculations and categorical results. All other existing node fields match
   the repository. No new node fields are required. Verdict: pass.

Changed in this reading: removed the empty section of `variable` and `include` commands
left after removing duplicate private contraction helpers; updated the private-scope
change record accordingly; clarified the report's holes closed/added and axiom evidence.
