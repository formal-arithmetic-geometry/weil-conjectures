## What changed

Retained the proofs of the five original holes of
`Sheaf.Paper.CondensedQbarPullbackCube`. Composition specializes the existing generic
`derived_pull_comp` and `bounded_comp_hom` calculations. Equality transport and
rectangle pasting produce the square of isomorphisms. The proved private
`coefficientCube_of_iso` takes hom components and cancels the invertible comparisons,
then specializes to the original public `coefficientPullbackCube` conclusion.

Repaired the return by deleting the copied private `rectangle`, `mapped_rectangle`,
`mapped_iso_rectangle` and `inverse_square`, together with the local generalized
`inverse_mapped_square`. Restored `import all
Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` and use its existing
`mapped_iso_rectangle` and `inverse_mapped_square` directly. The four reported
statements are neither reproved nor renamed. The original two proof imports remain.

Only the item module, its existing node, this report and
`coord/changes/E1-qbar-pullback-projection-cache.md` are delivered. The public theorem
signature is byte for byte identical to the shared source. The four retained private
signatures differ only by line wrapping. No imported module, definition, instance,
public import, target statement or visibility changes. No consumer needs adapting.

## Proved and sorry left

Five original holes closed:

- `qbarPullIso_comp`
- `qbarPull_eq`
- `qbarPull_square_cube_iso`
- `qbarPull_square_cube`
- `AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_pullback_cube`

Zero holes added; zero split-offs; zero `sorry` left in the delivered module.
`coefficientCube_of_iso` is proved from the existing inverse cancellation lemma.
Pre-existing imported obligations remain; closing these local holes does not claim
that their entire imported dependency closure is sorry-free.

Current validation: the repaired module compiles without warnings in 38.5 seconds through
`lcompile.py`. The unchanged direct consumer
`Sheaf.Paper.CondensedQbarExchangeLeftAdjunct` also compiles cleanly in 11.7 seconds.
The public theorem signature is byte-identical, all Lean lines meet the 100-column
limit, and the node dependency list equals the union of its proof-step dependencies.
The required delivery dry run separately checks the final compile and axiom probe.
The independent second reading of the repaired delivery is recorded below.

## No longer needed

Removed unused private projection helpers `qbar_map_hom`, `qbar_obj_obj`,
`upper_map_hom` and `upper_obj_obj`. Removed all five local diagram copies named above;
only the generic `coefficientCube_of_iso` wrapper is needed locally.

No imports or DAG dependency nodes are pruned: both original proof imports are used.
The integral exchange adjunct module supplies generic proved helpers, without using
its specialized exchange theorem. All three existing `proof_deps` remain used. No
unit statement or realized unit step is bypassed. No push comparison, exchange
morphism, properness or Cartesianity is used. No whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The returned proof copied elementary diagram statements already present in
`ContinuousIntegralExchangeTargetAdjunct`. The import-pruning check correctly refused
those duplicates. The repaired proof imports and reuses the existing statements.
The earlier report's claimed pruning of that import is withdrawn.

The retained generic isomorphism-to-cube wrapper avoids the concrete final cancellation
that previously hit a kernel timeout. No source-library cache or instance changes are
needed. The node describes the implemented argument and retains the original statement.
The earlier independent review covered the returned version; the repaired version must
receive the normal new second reading.


## Second reading by E1

1. **Signatures and visibility: PASS.** Read the entire delivered module and its diff
   against the shared repository. The public theorem signature is byte-identical.
   The four retained private signatures differ only in whitespace; the change record
   declares those reflows and the removal of four unused private projection lemmas.
   Imports are byte-identical, including the two non-public `import all` proof imports.
   No definition, instance, target statement or exported visibility changes. The node's
   refreshed `lean.statement` is byte-identical to the current theorem signature;
   the repository's prior recorded signature was stale.
2. **Proof and axioms: PASS.** Independently compiled the delivered file through
   `lcompile.py`: exit 0, no warnings, 35.0 seconds. Compiled a scratch copy with
   `#print axioms` for all five repaired declarations and `coefficientCube_of_iso`:
   exit 0, 33.7 seconds. The generic helper uses only `propext`, `Classical.choice`
   and `Quot.sound`. The five repaired declarations additionally reach `sorryAx`
   through pre-existing imported obligations. No other axiom appears. There is no
   `sorry`, forbidden declaration mechanism or new data definition in the module.
3. **Split-offs and elementary arguments: PASS.** There are no split-offs or new
   obligations. Read the imported `derived_pull_comp`, `bounded_comp_hom`,
   `mapped_iso_rectangle` and `inverse_mapped_square` statements and their proofs.
   The new private wrapper only takes hom components and invokes the existing inverse
   cancellation lemma. Identity comparisons give the unit equations; zero objects give
   the unique morphisms, and equality transport reduces by substitution. No properness,
   Cartesianity, exchange or push-comparison hypothesis is introduced. Searched both
   library roots for the cube predicate and diagram helpers: the four duplicate diagram
   statements named in the return are absent from the delivery and their existing
   versions are imported and used.
4. **Route and pruning: PASS.** The proof specializes generic composition coherence,
   transports along `sq.w.symm`, pastes the two compositions using the existing square
   component API, and cancels isomorphisms. The two proof imports are both needed.
   All three original `proof_deps` remain used, so `No longer needed` correctly claims
   no node or module pruning. Read `dag/units/sk-thm-properbasechange.json`, including
   its `realized` statement and steps: none is replaced or bypassed. No shorter existing
   cube theorem was found in the library search; the reusable diagram calculations are
   already used directly.
5. **DAG and records: PASS.** Read the original and delivered node, the proof dependencies
   and the change record. Only `proof`, `proof_origin` and the stale `lean.statement`
   are updated. The union of the proof-step `uses` is exactly `proof_deps`. The prose
   describes the actual composition specialization, equality transport, rectangle
   pasting and inverse cancellation. No new nodes require auditing. The report correctly
   names five original holes closed, zero added and zero split off; imported holes
   remain explicitly outside that local count.

Second reading changed only this report: added the independent five-point review,
recorded fresh compile and axiom results, and replaced the pending-review sentence.
No Lean proof or node repair was necessary.
