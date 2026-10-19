# Stage 1 report: lem-weil-pbc-restriction-local-completeness

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-restriction-local-completeness.json`: statement split into two proof steps; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-local-hom-tower-criterion.json`: statement-only prerequisite; no Mathlib match.
- `citations.json`: verbatim citations for every step/node use.

## Attachments

No attachments. I searched the slopmaster2 project for the item id, the Stacks tag 099C, and restriction/derived-completeness declarations; no sorry-free project declaration states this item exactly.

## WANTED

None. `literature/stacks-project/algebraization.tex` contains Tags 0997 and 099C used here.

## What was wrong or incomplete

The imported item had no proof and its Mathlib searches were already negative. Its statement uses the internal-Hom formulation of local completeness, while Tag 099C proves the restriction result through the multiplication tower T(K,f); therefore I added the smaller Tag 0997 criterion as a statement-only node rather than silently treating the two formulations as identical. No statement was changed and no hypothesis was added.

## What could not be finished

No Lean was written or compiled, as required for this stage. The new prerequisite remains `unsplit` for later workers.

## Review by NE

I read the imported item, the completed-pullback ancestor, the unit and chapter records, and `literature/stacks-project/algebraization.tex` at Tags 0997 and 099C. Tag 0997 supplies exactly the new criterion used in step 1: vanishing of derived internal Hom from localization is equivalent to vanishing of the derived multiplication tower on the slice. Step 1 applies this criterion once over O and once over B to the image of each ideal section. Step 2 uses the restriction-of-scalars definition, which explicitly keeps the underlying abelian sheaf, together with the module-sheaf statement that kernels are sectionwise and cokernels are sheafifications of sectionwise cokernels; hence the tower's multiplication maps and cohomology are unchanged after forgetting scalars. The abstract derived-category definition supplies cohomology as kernel modulo image, and the derived-limit definition identifies the tower object. I checked that all hypotheses (small site, ring sheaf morphism, arbitrary ideal, every slice section) are present and that no flatness or finite-generation assumption slipped into either step. I also checked every citation quote against the cited node text and recorded the Mathlib searches actually run for both the item and the new criterion; LeanSearch was unavailable and recorded as such.

## Not duplicates

lem-weil-pbc-local-hom-tower-criterion vs lem-weil-pbc-restriction-local-completeness: the new node is the single-ringed-site equivalence between localization internal-Hom vanishing and the multiplication-tower criterion; the item compares this criterion after restriction of scalars for two ring sheaves and an ideal sheaf.
lem-weil-pbc-local-hom-tower-criterion vs lem-weil-pbc-ringed-derived-complete-elements-ideal: the new node compares localization RHom with the derived multiplication tower for one section, while the existing node proves that the set of sections satisfying the tower vanishing forms a sheaf of ideals; neither statement implies the other.

## Second reading by NE

- Item statement: checked against `algebraization.tex`, Tag 099C (`lemma-restriction-derived-complete`), with Tag 0997 for the internal-Hom formulation; verdict: all hypotheses (site, ring-map, ideal, generated extension ideal, slice sections, and arbitrary derived object) and both implications are present, including the zero and field cases and no flatness assumption.
- Step 1: checked against Tags 099C and 0997 and the complete statement of `lem-weil-pbc-local-hom-tower-criterion`; verdict: the criterion is applied on every slice and to the image section in the coefficient ring, with the required derived-category and derived-limit notions cited.
- Step 2: checked against the restriction-of-scalars, module-sheaf, abstract-derived-category, and derived-limit definitions and the final paragraph of Tag 099C; verdict: the underlying abelian sheaf, multiplication maps, kernels, cokernels, cohomology, and zero-object detection are identified explicitly, so preservation and reflection are both justified.
- New node `lem-weil-pbc-local-hom-tower-criterion`: checked against Tag 0997 clause-by-clause and searched for duplicate DAG and Mathlib declarations; verdict: strictly smaller, self-contained, statement-only, with all definition dependencies, source label, blueprint fields, and recorded searches.
- Small cases: tested the criterion and item on the zero object, a field with (f=0) and (f=1), and the empty slice; no hypothesis or conclusion changes.
- Changes made: none to statements, proof steps, citations, or searches; added this second-reading audit only. The item’s existing `split_report` and first review remain unchanged.
