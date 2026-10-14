## What changed

Copied and delivered `lean/Sheaf/AlgebraicGeometry/GlobalHomAdjunctionIso.lean`.
Relative to the freshly fetched delivery base, the proof of
`exists_schemeHomTensorPullbackIso` packages the canonical family as a natural
transformation first and proves its components invertible using monoidal realization.
All existing signatures and definition bodies stay unchanged. No imports changed.
Removed the two unused certificate lemmas present in the initial sandbox but absent
from the refreshed base, avoiding unnecessary public additions and new nodes.

## Proved and sorry left

All declarations in `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso` have complete
local proofs; there are no textual `sorry` declarations and no new holes were added.
Holes closed by this delivery: none (the repository already has these proofs).
Holes added: none. This is verification only, with net progress zero.
The global adjunction map, its isomorphism theorem and its isomorphism definition
still depend on `sorryAx` through existing upstream statements; they are not
axiom-clean target proofs. In particular,
`schemeGlobalHomAdjunctionMap_isIso` is fully proved, and
`schemeGlobalHomAdjunctionIso` is defined from its componentwise `IsIso` result.

## No longer needed

None. Every import retained by the module is used by its declarations or proofs.

## Where the brief, the DAG or earlier work was wrong

The source module already contains the completed stage-3 proof rather than the
`sorry` described by the work brief. The DAG route is consistent with the code;
no statement or dependency correction was needed. The initial local checkout was
ahead of the fetched delivery base; the second reading below records that difference.

## New nodes

None.

## Earlier second reading (a previous round; superseded)
The module compiles and preserves the target statement and route; no new nodes or statements were introduced.

## Second reading by P2

1. Compared the delivered module with the read-only repository using `diff -u`.
   Initially the only difference was a dated verification comment. The dry run
   refreshed the checkout to the delivery base, revealing the tensor-existence
   proof adjustment and two public certificate additions. Removed both unused
   additions (schemeHomTensorPullbackIso_isCanonical and
   schemeHomTensorPullbackIso_unique). Every existing signature, definition body,
   visibility, import and option remains byte-for-byte unchanged.
   No target or interface was altered; no change record is required.
2. Compiled the module successfully with lcompile.py, without warnings. Scanned
   for forbidden declarations and proof escapes: none; no textual sorry occurs.
   Compiled a scratch copy with #print axioms for all 13 public declarations
   listed in the initial node (11 remain after removing the unused additions). All use only propext, Classical.choice and Quot.sound,
   except schemeGlobalHomAdjunctionMap, schemeGlobalHomAdjunctionMap_isIso and
   schemeGlobalHomAdjunctionIso, which also use sorryAx from existing dependencies.
   The chosen Leray comparison is pinned by the identity underived comparison and
   its derived-unit equation; the tensor comparison satisfies its canonical predicate by the existence
   theorem; the predicate itself includes the existing uniqueness principle. The adjunction existence theorem and the selected
   pullback composition data themselves have no sorryAx in these axiom checks.
   No data is newly chosen from an unproved mere-existence statement.
3. No statements were split off or added, so new-statement truth, edge-case,
   duplication and source-proof checks are vacuous. No new holes or nodes exist.
4. Read the evaluation-mate calculation, the universal derived Leray comparison,
   monoidal-realization reduction and the final coherator/global-sections argument.
   The proof uses the recorded dependency declarations and does not weaken them.
   Library search found related generic helpers in DerivedDirectImageInternalHom;
   these do not replace the fixed-data public construction without further changes.
   The retained public imports occur in public signatures or exposed definitions;
   the six plain imports support proofs. No old proof dependency was removed.
   The unit sk-thm-picard-duality has empty realized statement/step lists; these and
   the unit route are unchanged, with no new bypass introduced.
5. Read lem-pc-global-hom-adjunction.json and the relevant dependency statements.
   Its four proof steps, proof_deps and proof_origin match the canonical tensor,
   evaluation mate, sheaf comparison and Leray/coherator route in the Lean module.
   No node edits are needed. The existing hollow-definitions repair list raises
   an upstream normalization issue for the shared counit; relative tensor
   uniqueness does not resolve that issue, and this delivery does
   not claim to repair it or independently certify the upstream definitions.

Changes by this reading: removed two unused public theorem additions relative to
the refreshed base, corrected the report's progress and axiom claims, and recorded
the existing upstream normalization caveat. The remaining tensor-existence proof
adjustment is the supplied proof, not new proof work by this reading.
