# Stage-1 delivery: def-pc-upper-shriek-right-adjoint

## Files written

- `dag/nodes/sec-picard-framework/def-pc-upper-shriek-right-adjoint.json`: definition split; no new nodes and no Mathlib leaves.
- `citations.json`: empty because a definition has no proof steps.

## Attachments

None. The Lean source has upper shriek declarations for etale and pro-etale sheaves, but no declaration for this coherent quasi-coherent derived functor.

## WANTED

- `literature/stacks-project/duality.tex`, Tags 0A9E and 0A9Y, for `def-pc-upper-shriek-right-adjoint`. The literature source tree is absent from this read-only checkout; I read the Stacks Project pages for those tags online.

## Source correction

The imported source place said Tag 0ATX, Lemma 48.16.3, but that lemma concerns composition of upper shriek functors. The right adjoint used in this definition is established by Tag 0A9E, Lemma 48.3.1. Situation 48.16.1 (Tag 0A9Y) names the resulting construction upper shriek. I corrected only the source place; the statement itself is accurate.

## Review by E1

I read Stacks Tag 0A9E, Lemma 48.3.1: for morphisms of quasi-compact, quasi-separated schemes it gives a right adjoint to derived direct image on $D_{\mathrm{QCoh}}$. I also read Tag 0A9Y, Situation 48.16.1, where the right adjoint of a proper compactification defines upper shriek, and Tag 0ATX to verify the source mismatch. The item's Noetherian and proper hypotheses specialize 0A9E: Noetherian schemes are quasi-compact and quasi-separated, and a proper morphism is a morphism between them. The separate node `lem-pc-noetherian-derived-direct-image-right-adjoint` explicitly states the existence and the preservation of quasi-coherent complexes under exactly these hypotheses. `def-pc-derived-direct-image` defines $Rh_*$, `def-pc-derived-category` defines $D_{\mathrm{QCoh}}$, and `def-weil-proper-morphism` defines proper; I opened each statement and checked the four citations name what the definition uses. The right adjoint is chosen from the existence assertion, with no additional proof step. For the small case $h=\operatorname{id}_X$, $Rh_*$ is the identity up to canonical isomorphism and its right adjoint can be chosen as the identity; this is consistent with the definition. I searched the blueprint by “upper shriek” and “right adjoint,” the DAG, and Lean source before concluding no new node or attachment is needed. The Mathlib searches already recorded on the item cover LeanSearch, Loogle, and source grep. The only correction was the Stacks place.

## Unfinished

Nothing in this one-level definition split. Its statement dependencies remain independent DAG items.
