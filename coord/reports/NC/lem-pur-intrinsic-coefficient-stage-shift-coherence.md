# Stage-1 report: lem-pur-intrinsic-coefficient-stage-shift-coherence

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-intrinsic-coefficient-stage-shift-coherence.json` — item, split; Mathlib searches found only generic shift/associator APIs.
- `dag/nodes/sec-smooth-purity/lem-pur-intrinsic-integral-associator-shift.json` — statement-only unsplit intermediate; Mathlib searches found no exact match.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.
- `report.md` — this report.

## Attachments

The proposed `WeilConjectures.SfAlgebraicallyClosedCoefficients.associator_commShift` attachment was rejected by the server's slopmaster2 check, so no Lean attachment is claimed.

## WANTED

None.

## Not duplicates

- `lem-pur-intrinsic-integral-associator-shift` vs `lem-pur-intrinsic-associator-shift-square`: the new node is the corrected *integral* compositor square for the finite-field scalar system; the existing node states the rational intrinsic square and has no finite-field datum.
- `lem-pur-intrinsic-integral-associator-shift` vs `lem-weil-scalar-associator-shifts`: the new node concerns the finite-field integral compositor and its normalization; the existing node concerns a rational scalar compositor and a different exact-triangulated input.
- `lem-pur-intrinsic-integral-associator-shift` vs `lem-pur-coefficient-associator-shifts`: the new node is for intrinsic completed coefficient categories and a finite-field scalar tower; the existing node is the balanced derived comparison for sheaves of commutative rings.

## What I checked and corrected

The live item was read together with `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-def-sf-operations.json`, the current blueprint proof `det-def-sfb-filtered-two-colimit-model.proof.md`, and the source module `lean/Sheaf/Paper/SfCoefficientStageCore.lean` (including the definitions of `Stage`, `transition`, `associator`, the normalization theorems, and `associator_commShift`). The source theorem's proof first constructs the corrected integral compositor square, then invokes the rational localization compatibility theorem, and finally transports through the coefficient-inclusion equality; the item proof now has those stages explicitly.

Step 1 cites `lem-route-coefficient-inclusion-laws`; I read its statement and verified that it supplies exactly the identity and composition equalities for the canonical small coefficient models used by `associator`, including reflexive maps. Step 2 cites `lem-route-integral-transition-comm-shift-exists-unique`; its statement gives the unique coherent integral transition shift normalized by the ordinary-to-completed comparison, which is the hypothesis used for each of the three integral transitions. Step 3 cites `lem-route-transition-comm-shift-exists-unique`; its statement gives the unique rational transition shift whose degree-one component is the localized integral component, matching the finite-stage normalization.

Step 4 uses the new statement-only node `lem-pur-intrinsic-integral-associator-shift`. I checked that its hypotheses introduce the finite-field datum, arbitrary scheme, three coefficient maps, equality transport, intrinsic integral categories, and the normalized integral shifts, and that its conclusion is exactly the integral compositor CommShift assertion rather than the item's rational conclusion. Step 5 uses `lem-pur-intrinsic-rational-associator-shift-compat`; I read its full statement and verified that it takes the corrected integral compositor CommShift, the degree-one localization equalities, and the integral/rational comparison normalizations, and concludes the all-integer rational CommShift equation. Step 6 uses the coefficient inclusion laws and `lem-weil-scalar-extension-composition`; I checked that the former supplies the equality transport used in the prescribed associator and the latter supplies natural scalar-extension composition with identity compatibility.

I also checked the edge cases explicitly: `E=L`, `L=M`, and `E=L=M` are allowed by the non-strict order and the identity inclusion law; the arbitrary scheme `Y` has no extra finite-type or separatedness hypothesis; and the rational category is the raw localization, with no Karoubi completion. The prior attachment was removed from consideration because the server explicitly reported that declaration as absent from the slopmaster2 project; the live source was retained as construction evidence only.

## Review by NC

I reread every cited node statement against each proof step and recorded verbatim quotes in `citations.json`. The integral intermediate is smaller than the item's rational associator claim and is not a restatement of an existing node: its conclusion is specifically the corrected integral compositor square. I checked that every non-elementary fact in Steps 1–6 is named by a cited node, that every cited node says the fact taken from it, and that the union of all `uses` is exactly `proof_deps`. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches for both the item and the new node; generic categorical hits were recorded as no exact match, and Loogle's unknown identifier was recorded as unavailable. No repository or Lean source file was modified, and no compiler or Lake command was run.

The server review also caught that the inherited `blueprint.from.node` named an intermediate DAG node rather than a blueprint node. I corrected both node records to use the actual blueprint ancestor `def-weil-algebraically-closed-coefficients`, preserving the same proof place and route.
