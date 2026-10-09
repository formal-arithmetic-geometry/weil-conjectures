# Stage 1 delivery: `lemma-weil-pbc-chow-factorization`

## Files written

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-chow-factorization.json` — existing statement node, now `status: split`; no new nodes.
- `coord/reports/C1/lemma-weil-pbc-chow-factorization.md` — this delivery report.

## Attachments

None. The item has no Lean declaration on either branch. Existing closed declarations used by cited nodes remain attached to those nodes; no private proof lemma was introduced here.

## WANTED

None. The imported blueprint proof and the cited Stacks sources are available in the repository records.

## What was checked or corrected

The imported statement was retained: it is the no-finite-presentation Chow factorization for a proper morphism over an affine base, including arbitrary base-change stability. The projective-space definition was added as a statement dependency. The imported proof's hidden Steps 4, 5, and 7 were expanded with explicit fibre-product, projective-space pullback, proper/closed-immersion/surjective base-change, and cartesian-pasting dependencies. The generic cross-unit foundation results `lemma-nagata-final-descended-model`, `lem-weil-pbc-proper-base-change`, `lem-weil-pbc-proper-composition`, and `lem-weil-pbc-proper-to-separated` are recorded as `tool_uses` as required by the route contract. The trailing explanatory remark was removed from the proof-step list because it is not a proof step. LeanSearch, Loogle, LeanFinder, and Mathlib source grep found no Mathlib Chow-factorization theorem.

## What could not be finished

Nothing remains for this one-level Stage 1 split. No Lean was written or compiled.

## Review by C1

I independently checked the statement against the imported node and the `sk-thm-chow` unit. The approximation route is coherent: properness supplies the separated finite-type envelope, separated finite-presentation descent supplies the noetherian model, the noetherian Chow node supplies the proper surjection and immersion, and base change plus restriction to the original closed subscheme recover the claimed object. The final properness argument correctly uses properness over the affine base, separatedness of relative projective space, and the proper-immersion-to-closed-immersion result. Steps 4, 5, and 7 are not elementary identities and now cite the relevant reusable nodes. The recorded `proof_deps` is exactly the union of step uses, every cited id exists and is unmerged, and the only out-of-unit unsplit statements are explicitly marked as accepted tool uses. `python3 tools/check_dag.py`, `python3 tools/review_split.py lemma-weil-pbc-chow-factorization`, and JSON validation all pass; the six reachability messages from `check_dag.py` are pre-existing unrelated repository warnings.
