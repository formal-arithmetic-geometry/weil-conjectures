## What changed

Proved `WeilConjectures.AdicQbarRealization.normalized_reindexing_hom` in
`Sheaf.Paper.AdicReindexingHom`, retaining its exact statement and public import.
Added four proved private helpers for the closed counit formula, evaluation
naturality in both inputs, transported uncurrying, and the abstract tensor/evaluation
square. The final proof applies that square to the original FamilyCore data.

For a permitted pair P, the source uncurrying equation is SpaceData.hom.evaluation.
On the other side, tensorator naturality moves realized podCommonHomComparison
through the tensorator; the target HomLaws evaluation and
podCommonHomComparison_laws.evaluation identify its uncurrying with pulled-back
source evaluation. Canceling the common tensor comparison in the given tensor
compatibility, and using comparison naturality at evaluation, supplies the two
squares for the private categorical calculation. Injectivity of uncurrying gives
exactly the original Hom equation. No perfection assumption or integral
normalization is used.

Updated only this module's node proof, proof_deps and proof_origin. No shared
interface, target, definition, public import, or other existing module changed.

Validation: the complete proof compiled through lcompile.py in 28.0 seconds,
below the 60-second limit. The sole warning requested an explanation for the
local heartbeat budget; that explanation is now present. The statement was also
checked byte-for-byte against the live item source. The delivery tool rechecks
the final source with its declaration/axiom probe.

## Proved and sorry left

Closed one hole:
`WeilConjectures.AdicQbarRealization.normalized_reindexing_hom`
(node `lem-sf-adic-reindexing-hom`).

One of one original holes closed; zero holes added; zero holes left in the item.
No split-off statements. The existing dependency
`WeilConjectures.podCommonHomComparison_laws` remains a named theorem used by this
proof; its proof is outside this delivery. The private helpers are fully proved.

## No longer needed

No imports removed and no modules withdrawn. The sole original public import,
`Sheaf.Paper.AdicRealizationFamilyData`, supplies all the statement and proof APIs.

Removed the following planned proof-dependency edges from the item's node:

- `lem-pur-isomorphism-inverse-image-tensor-hom`: the sheaf-level inverse-image
  tensor/Hom existence theorem is unnecessary once ReindexTensor is supplied.
- `lem-sf-ringed-derived-closed-symmetric-monoidal`: existence of ambient closed
  tensor data is unnecessary once each SpaceData supplies its At.closed.

These modules may still occur transitively in definition imports; this delivery
does not claim to remove them from the whole target closure. Instead the proof
records `def-sf-native-adic-realization-data` and
`def-sf-native-adic-tensor-reindexing`, whose evaluation and transpose data it uses,
and retains `lem-pod-derived-automorphism-hom-evaluation`.

## Where the brief, the DAG or earlier work was wrong

The preserved source contained one hole and a sufficient natural-language proof.
No mathematical statement error was found. The rework archive named a transitive
quarantine at CommonStagePullbackRepresentativeLinearity; the current server
queue lists the item as a one-hole proof task, and the live shared source was
restored during this session. The item was preserved, not withdrawn. The proof
works from the supplied structures and does not require repairing that unrelated
dependency or constructing a fresh inverse-image comparison.

The source argument is the existing agent-written categorical enhancement of
BS Remark 6.8.15 and Stacks 0GMX, as the old node explicitly records. The unit
route is retained, with no unit nodes or steps bypassed. The private categorical
argument applies without geometric hypotheses, including zero objects and
identity isomorphisms; in the native application it only forms the recorded
permitted pair and its pullback.

Searches run: LeanFinder for tensor-compatible natural isomorphisms preserving
internal-Hom comparisons (eight hits, generic cartesian closed-functor results),
Loogle for Adjunction.homEquiv_naturality_left_symm (exact lemma found), Mathlib
grep for evaluation and adjunction naturality (25 hits), and project searches
through NativeAdicRealizationData, NativeAdicTensorReindexing,
DerivedAutomorphismHomEvaluation and existing closed-evaluation proofs. No exact
native reindexing theorem was found; the existing adjunction API proves the glue.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
