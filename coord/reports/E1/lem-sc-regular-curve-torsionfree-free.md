Files written:

- `dag/nodes/sec-picard-framework/lem-sc-regular-curve-torsionfree-free.json` (statement, split; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-sc-dvr-fg-torsionfree-free.json` (statement, unsplit; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-sc-coherent-free-stalks-locally-free.json` (statement, unsplit; no exact Mathlib match).

Attachments: none.

WANTED: `literature/stacks-project/divisors.tex`, Tag 0CC4, for the item and the DVR module step.
WANTED: `literature/stacks-project/modules.tex`, Tag 0GWM, for the coherent free-stalk criterion.

The item was unsplit and has no exact sorry-free declaration in `weil-src-slopmaster2`; the blueprint search also found no duplicate. I retained its statement and added the regular-scheme definition dependency. The two new nodes are strictly smaller supporting facts and carry statements only, as required. I searched the whole DAG and blueprint by phrases, notions, and tags before creating them. The split follows the source's torsion-free quotient paragraph: local rings are fields or DVRs, finite torsion-free stalks are free, and coherent free stalks spread to local freeness; the converse is the one-line domain argument, and rank constancy follows from local constancy on the connected integral scheme.

## Review by E1

I read the item's imported blueprint paragraph in `lem-sc-riemann-roch` and the item source label `divisors.tex`, Tag 0CC4. I also read the pinned local Stacks checkout's 0CC4 label and the 0GWM module-localization label used for the second supporting statement. The item statement agrees with 0CC4: integral, regular, topological dimension at most one, coherent module, torsion-free exactly finite locally free, and generic rank equal to the constant rank. The first proof step uses the regular-scheme definition, the existing one-dimensional regular-local-ring-to-DVR node, and coherence to identify finite stalks; the field/DVR dichotomy is the dimension-at-most-one case split. The second step uses the new DVR module statement and the new coherent free-stalk statement, exactly matching the two non-elementary assertions in 0CC4. The converse step uses only that local rings of an integral scheme are domains and that a finite free module over a domain is torsion-free. The last step uses the definition of the function field and the elementary local constancy of rank on a connected integral scheme.

For the new nodes I checked that each statement introduces its own ring/module or scheme/sheaf hypotheses, contains no proof sketch, uses the exact Stacks labels, and records LeanSearch, semantic search, Loogle, and Mathlib-source searches. I tested the statements on a field (every finite module is free), on a DVR module `R/(t)` (not torsion-free, so excluded), on `R` and `R^2`, and on a free sheaf of rank zero and rank one. No source statement or hypothesis was silently weakened. The only limitation is that the project repository does not include the Stacks `.tex` sources, so both source locations are reported as WANTED.

What I could not finish: no Lean compilation is permitted at stage 1, and the remote delivery script is the required final verification.
