# Stage-1 report: lem-trf-regular-ring-universally-catenary

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-regular-ring-universally-catenary.json` — statement, split proof, blueprint metadata, searches.
- `dag/nodes/sec-trace-formula/lem-trf-regular-local-cm.json` — statement-only helper; Mathlib searches found no matching Cohen–Macaulay/depth theorem.
- `dag/nodes/sec-trace-formula/lem-trf-cm-ring-universally-catenary.json` — statement-only helper; Mathlib searches found no catenarity theorem.
- `citations.json` — seven step/node quotes, all copied verbatim from the cited statements.

Attachments: none. No exact sorry-free declaration with the item statement exists in either read-only source tree.

WANTED: none.

The imported item had the correct hypotheses and conclusion but no proof split. The Mathlib searches returned only Noetherianity, finite-height, regular-sequence dimension identities, and unrelated local-ring facts; no catenarity or Cohen–Macaulay theorem. The two new nodes are therefore unsplit Stacks leaves at Tags 00NQ and 00NM. I searched the whole DAG and blueprint for those tags and for the relevant phrases; the existing 00NQ node `lem-weil-pbc-regular-local-generators-regular-sequence` states the regular-sequence part but does not state the depth/Cohen–Macaulay conclusion, and no 00NM node exists. Neither new node is a restatement of an existing node or a clause with the item's regular-ring hypotheses.

## Review by Q104

I read the item, its `sec-trace-formula` chapter and `sk-i-curve-zero` unit, the ancestor blueprint reference, and the Stacks source around Tags 00NQ (lines 25732–25743) and 00NM (lines 25607–25645), with labels checked in `literature/stacks-project/tags/tags`. The item hypotheses are used exactly: Step 1 applies the regular-local statement at every prime localization, including the dimension-zero empty-sequence case. The local-CM helper states depth equal to Krull dimension and its regular-sequence interpretation, so it supplies precisely the premise required by Step 2. Step 2 checks Noetherianity and applies the 00NM helper; unfolding the existing excellent/universal-catenarity definition gives the finite chain bound and equal saturated-chain lengths in every finite-type algebra. Every non-elementary fact is named by a node, and each cited node's statement was opened and matched to the quoted text in `citations.json`. I checked edge cases (a field, the zero-dimensional local case, and the zero ring's vacuous prime condition) and made no Lean or compiler changes.

What I could not finish: no Lean proof was attempted because this is the stage-1 natural-language DAG only.

## Not duplicates

lem-trf-cm-ring-universally-catenary vs lem-trf-regular-ring-universally-catenary: the new node assumes every localization is Cohen–Macaulay and states the general 00NM theorem; the existing item assumes regular localizations and is the target specialization.
lem-trf-regular-local-cm vs lem-trf-regular-ring-universally-catenary: the new node is a local depth-equals-dimension statement, while the existing item is a global universal-catenarity conclusion.
lem-trf-regular-local-cm vs lem-weil-pbc-flat-polynomial-append-fibre-regular-sequence: the new node concludes depth equals dimension for an arbitrary regular local ring; the existing node concerns a regular sequence in a particular flat polynomial fibre setup.
lem-trf-regular-local-cm vs lem-weil-pbc-flat-polynomial-append-tensor-fibre: the new node concludes depth equals dimension for an arbitrary regular local ring; the existing node concerns tensor and fibre identifications in a polynomial append construction.
lem-trf-regular-local-cm vs lem-weil-pbc-flat-regular-fibre-parameter-selection: the new node concludes depth equals dimension for an arbitrary regular local ring; the existing node selects parameters for a flat regular-fibre lifting problem.
lem-trf-regular-local-cm vs lem-weil-pbc-geometrically-regular-over-field-flat: the new node concludes depth equals dimension for an arbitrary regular local ring; the existing node proves flatness and geometric regularity over a field.
lem-trf-regular-local-cm vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: the new node is the local Cohen–Macaulay consequence of regularity; the existing node constructs a global complete-intersection regular sequence.
lem-trf-regular-local-cm vs lem-weil-pbc-hypersurface-derivation-regular: the new node treats a full regular system of parameters; the existing node treats one hypersurface equation detected by a derivation.
lem-trf-regular-local-cm vs lem-weil-pbc-popescu-find-sequence: the new node concludes depth equals dimension; the existing node supplies a sequence in the Popescu smoothing construction.
lem-trf-regular-local-cm vs lem-weil-pbc-regular-local-generators-regular-sequence: the new node adds the depth/Cohen–Macaulay conclusion, whereas the existing node states regularity of parameter sequences and their regular quotients.
lem-trf-regular-local-cm vs lem-weil-pbc-regular-local-hypersurface-criterion: the new node concerns all parameters and depth; the existing node characterizes regularity after quotienting by one element.
lem-trf-regular-local-cm vs lem-weil-pbc-regular-ring-normal: the new node proves Cohen–Macaulayness of regular local rings; the existing node proves normality of a global regular ring.
