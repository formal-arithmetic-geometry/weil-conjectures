## What changed

Replaced the worker's invalid restatement reduction with a real reduction from the
additive ordinary square to a module-linear square. In the item, construct the
B-linear lift of the given additive chain map by tensor induction. Prove exact
restriction/forgetful homology transport and apply its naturality to that lift.
The new module SecondLocalizationOrdinaryBSquare now states only the module-linear
counit identity. Its import in the item is proof-only. Existing signatures,
definitions, visibility and public imports are unchanged.

## Proved and sorry left

Closed the body of `RingTensorCohomology.secondLocalization_ordinary_square`
(node `lem-pc-second-localization-ordinary-square`). Proved four private transport
helpers: `map_homology_pi`, `forget_restrict_cyclesIso`,
`forget_restrict_homologyIso`, `forget_comparison_transport`.
Added one named hole: `RingTensorCohomology.secondLocalization_ordinary_B_square`
(node `lem-pc-second-localization-ordinary-B-square`). No other holes are added.
This is a decomposition: 1 upper hole closed, 1 smaller module-linear hole added,
net 0. The target still depends on sorryAx; it is not an axiom-free proof of the
ordinary counit compatibility.

## No longer needed

No old proof-dependency node or import is pruned. The old dependency
`lem-pc-second-localization-map` remains used transitively and directly through
its definitions in the signature; its public import stays. The obsolete private
`homologyMap_congr_of_pure_tmul` and its reflexive use were removed.

## Where the brief, the DAG or earlier work was wrong

The submitted B-square was byte-for-byte the parent additive statement under a
new name. Applying tensor extensionality with phi equal to itself did not reduce
the problem. Its node claimed a B-linear theorem that the Lean did not state and
its recorded signature flattened whitespace. Replaced all three with the actual
module-linear interface and verbatim signature. Searches were rerun with different
queries; they find exactness and naturality machinery, not this model-specific
counit identity. The local Stacks TeX is absent, so the reader read the official
pages https://stacks.math.columbia.edu/tag/06Y6 and
https://stacks.math.columbia.edu/tag/0DJ8. The new proof is an agent's explicit
formal-interface argument following their derived scalar-extension route.

## Second reading by E1

1. Compared the delivered item against the repository using diff. The existing
   theorem signature, section variables, visibility and all definitions are
   byte-for-byte preserved. Only private proof helpers, one plain import, the
   theorem proof change. No change record is needed.
2. Both modules compiled locally with lcompile.py. There are no prohibited
   declarations or data chosen from new existence holes. The only new sorry is
   the named B-square theorem. Axiom probes check the allowed standard axioms
   and the explicitly reported sorryAx dependency.
3. Rejected the original duplicate split. The replacement assumes B-linearity;
   the parent proves it from the additive pure-tensor hypothesis, checks chain
   compatibility, and proves the forgetful homology transport. Checked zero and
   additive tensors, multiplication of coefficient scalars, identity coefficient
   maps, zero complexes, and zero rings: the equations use no faithfulness,
   injectivity, or flatness of D. The B-square has a full proof docstring and node.
   Searched Mathlib with leanfinder, loogle, and grep through msearch.py (LeanSearch
   returned HTTP 500 and is recorded as unavailable), and
   searched lean/Sheaf and lean/WeilConjectures. Related transport helpers in
   FirstLocalizationOrdinarySquare and ScalarExtensionHomologySquare are private;
   the private transport argument here follows the former without changing its
   interface. No accessible theorem supplies the remaining counit calculation.
4. The public imports are needed by statements; the B-square import is plain.
   No old dependency is unused: SecondLocalizationMap supplies the characterized
   map and remains in the lower proof plan. sk-thm-picard-semicon.realized is
   unchanged (empty realization lists); no unit route is bypassed.
5. Rewrote the parent's proof/proof_deps/proof_origin to record scalar-linearity
   construction and homology transport. Rewrote the new node to match the actual
   B-linear statement, its exact Lean signature, source, proof and fresh searches.
   Its statement does not cite the parent and introduces no dependency cycle.

Changed in this reading: removed the reflexive tensor detour and identical
additive hole; constructed the B-linear lift, proved four transport helpers,
changed the new hole to a genuine module-linear interface, and repaired the DAG
and report. The remaining universal counit calculation is substantial and was
not represented as already proved.

Axiom audit: a scratch copy compiled with #print axioms for the parent, lower
B-square, and all four private helpers. Each helper uses only propext,
Classical.choice and Quot.sound. The parent and the lower square additionally
use sorryAx, exactly as reported above. The parser comparison also confirms no
existing statement changed.

## New nodes

- `lem-pc-second-localization-ordinary-B-square`: the module-linear counit
  compatibility, with the additive lifting and forgetful transport removed.
