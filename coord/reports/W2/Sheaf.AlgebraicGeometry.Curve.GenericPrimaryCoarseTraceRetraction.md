## What changed

The original declaration `AlgebraicGeometry.IsConnectedCurve.exists_generic_primary_coarse_trace_retraction` keeps its raw signature and docstring unchanged. Its proof now obtains a generic filtration with a compatible finite etale cover, then applies a proved rescaled-trace/conjugation theorem.

Added `Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData`: the single pending construction includes the commuting generic-point square, the degree coprime to ell, a power of ell annihilating M, and an isomorphism from the pullback of M to the terminal filtration term. It asserts no retraction.

Repaired `Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceMaps`: the trace step is now fully proved from the prescribed-degree trace formula, `Nat.gcd_eq_gcd_ab`, pushforward composition isomorphisms and functoriality. Its assumptions explicitly include the annihilator, coprimality, commuting square and terminal-sheaf identification. All proof-only imports are plain imports.

Updated the original node's proof and immediate proof dependencies, and replaced both new nodes with complete statements, verbatim Lean signatures, source-backed proof steps and recorded searches. No existing definition or public import changed; no change record or forced adaptation is required.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.IsConnectedCurve.exists_generic_primary_coarse_trace_retraction` (node `lem-sc-generic-primary-coarse-trace-retraction`). Its reduction has no direct sorry.

Added one hole: `AlgebraicGeometry.IsConnectedCurve.exists_generic_primary_coarse_filtration_data` (node `lem-sc-generic-primary-coarse-filtration-data`), in its own new module. Its entire proof is a named public theorem with a source and complete natural-language construction in its docstring. This theorem was NOT pre-existing in the repository.

Also proved the new `AlgebraicGeometry.IsConnectedCurve.exists_generic_primary_coarse_trace_maps` (node `lem-sc-generic-primary-coarse-trace-retraction-maps`); no sorry remains in that module. Removed the first worker's false trace-maps hole and unused `comp_eq_id_of_left_inverse` tautology and its node.

This is a decomposition: one original hole closed, one construction hole added, net zero from these declarations. The original theorem is not claimed axiom-clean: the construction and existing trace infrastructure remain open. No data definition or arbitrary witness chosen in a definition was added.

## No longer needed

Removed the four direct proof imports from the original module:
- `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`
- `Sheaf.RepresentationTheory.SylowModuleFiltration`
- `Sheaf.FieldTheory.OpenSubgroupFixedField`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree`

The first three remain needed through the new filtration-construction module. Their nodes `lem-exc-abelian-sheaves-gmodules`, `lem-sc-sylow-module-filtration` and `lem-exc-etale-open-subgroup-fixed-field` remain transitive proof dependencies; they have not been discarded from the route. The original immediate proof dependencies are now the two new nodes.

`lem-weil-pbc-finite-etale-trace-degree` and its module `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree` are no longer needed on this route: the trace helper uses the more precise existing `lem-weil-pbc-finite-etale-trace-degree-trace`, whose module accepts a prescribed degree. This is a local import/route pruning, not a claim that the former module has disappeared from all targets' import closure.

The unused first-worker identity helper and its new node were removed. No existing DAG node was deleted. The unit `sk-prop-cd-affine` has empty `realized.statement` and four empty `realized.steps`; nothing here bypasses a realized unit statement or step.

## Where the brief, the DAG or earlier work was wrong

The first worker's trace-maps theorem was false: take n = 0 and every filtration term zero. Its assumptions then allow a nonzero finite primary M, but its conclusion makes eta_* M a retract of zero. It provided neither an identification of F(n) with the pullback of M nor a prime-to-ell degree or commuting square. Its one-line docstring was not a complete proof, its node lacked blueprint provenance and searches, and its Lean statement record was an ellipsis.

The first worker's filtration-data theorem was new, not pre-existing as the initial report claimed. Without a terminal identification its zero-length chain is vacuous and cannot justify the trace step. The repaired construction is exactly the geometric/Galois part of the original plan, with the missing data retained. The original target signature itself was correct and was not changed.

## Second reading by W2

1. Compared every delivered module against the repository. The original module is the only existing one changed. Checked both the declaration parser and a raw byte comparison of its full pre-proof signature: unchanged. Its existing docstring and public imports are unchanged; no existing definition was altered. The two other modules and two supporting nodes are new. Verdict: pass after repair.

2. Compiled all three modules in import order using lcompile.py. There is exactly one textual sorry, the whole proof of the public named construction theorem. No axiom, unsafe, opaque, extern, implemented_by, anonymous hole or definition was added. Scratch-copy #print axioms checks for all three declarations returned exactly propext, Classical.choice, Quot.sound and sorryAx. The helper has no direct hole; its sorryAx is inherited from the existing trace/inverse-image infrastructure. The delivery probe also checks the transitive trust dependencies. Verdict: pass subject to the explicitly reported open construction and imported holes.

3. Rejected the original trace theorem by its n = 0 edge case. The repaired trace statement is proved; its m = 1 case forces M to be zero, and its d = 0 case with coprimality forces m = 1, so both degenerate cases are valid. With m = 0, coprimality forces d = 1 and the trace formula itself gives the splitting. In the construction the zero stalk uses n = 0 and F(n) is identified with q^* M; a nonzero stalk cannot use that degenerate identification. Repeated terms have rank-zero quotients. The construction states the Sylow/fixed-field/normalization steps without the retraction and is a strict part of the argument. Searched with different phrases via leanfinder, loogle and grep, plus leansearch (unavailable, recorded honestly). Also read the corresponding upstream affine-curve result, group filtration, fixed-field and stalk equivalence modules; none supplies this full construction. Verdict: pass after replacing the false statement and completing metadata/docstrings.

4. The proof follows the original plan's Galois/Sylow/fixed-field normalization route and uses the shorter prescribed-degree trace theorem. The trace rescaling and conjugation step is now proved rather than split off. Removed unused direct imports and the unused tautological identity helper. The report accounts for every old immediate proof dependency, and the unit's realized route is untouched. Verdict: pass.

5. Read and repaired the original node's proof/proof_deps/proof_origin and both new nodes. New nodes have complete source-backed steps, the union of their used nodes as proof_deps, blueprint provenance, exact Lean statements, creation records and all three search kinds. The target proof assembles the data and calls the proved trace theorem, matching the DAG. Verdict: pass.

Changes made by the second reader: replaced the false universal trace assertion with a proved trace lemma; strengthened the new construction to retain the cover, degree, annihilator and terminal identification and moved it to its own module; removed the unused identity helper/node; repaired all node records, searches, imports and the inaccurate hole accounting.

## New nodes

`lem-sc-generic-primary-coarse-filtration-data`, module `Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData`: one pending geometric/Galois construction, carrying the full filtered cover data and terminal identification needed by the proved trace step.

`lem-sc-generic-primary-coarse-trace-retraction-maps`, module `Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceMaps`: proved rescaled finite etale trace after a commuting generic square and terminal-sheaf identification. No new sorry in this node.

No change records: all existing signatures, definitions and public import visibility remain unchanged.
