1. Files written

- Item: `dag/nodes/sec-picard-framework/lem-sc-affine-perfect-derived-tensor-hom.json` (statement, split; no new nodes).
- `citations.json` (verbatim citations for all proof-step uses).

2. Attachments

None. No sorry-free declaration tagged `lem-sc-affine-perfect-derived-tensor-hom` or stating the item exactly was found under `WeilConjectures/`.

3. Source read

Read `/home/ubuntu/c1-stacks-review/cohomology.tex`, Cohomology Lemma `cohomology-lemma-internal-hom` (Tag `08DJ`), including equation (1) and its proof.

4. What was checked and corrected

The imported statement was retained: it is the derived tensor-Hom correspondence for a perfect complex, with the ambient category explicitly `D(O_X)`. The source file named in the node is not present in this checkout, so the proof is marked agent-written and the missing source is reported above. The whole DAG and blueprint were searched for the tensor-Hom statement; the closest existing nodes are the underived sheaf-module closed structure and the generic derived-adjunction theorem, not duplicates of this item. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; only ordinary module-level closed structure appeared, while LeanSearch was unavailable.

## Review by H1

I read the item node, its `sk-thm-picard-duality` unit, the `sec-picard-framework` chapter record, and the existing statements used by every step. Step 1 cites `lem-pc-sheaf-modules-tensor-closed` for the exact natural Hom bijection between tensoring by A and underived sheaf internal Hom, and `def-pur-derived-internal-hom` for the derived internal-Hom construction; I checked that the cited sentence contains the closed adjunction it uses. Step 2 cites `lem-pc-kflat-resolution` for K-flat replacements and `prop-pur-kinjective-resolutions-exist` for functorial K-injective replacements, and uses the derived internal-Hom definition to identify the right derived functor. Step 3 cites `lem-pc-derived-adjoint-functors`, whose statement explicitly gives the canonical bifunctorial Hom bijection when the left and right derived functors exist. The perfectness hypotheses are retained even though the general closed adjunction does not need them. I corrected the proof origin to agent-written after verifying that `literature/stacks-project/perfect.tex` is absent, added the required WANTED entry, and checked every citation quote against the source node text.

## Second reading by H1

- Item statement: checked against Cohomology Tag 08DJ equation (1); the scheme and perfect-object hypotheses are specializations, and the Hom correspondence has the correct tensor order after symmetry.
- Step 1: replaced the unsupported underived/K-flat/K-injective reconstruction with a direct application of the broader Tag 08DJ statement; the cited child states exactly the bifunctorial Hom bijection.
- Step 2: checked as elementary evaluation of the displayed bijection at a morphism; no uncited theorem is used.
- New node `lem-sc-derived-internal-hom-adjunction`: statement-only, self-contained, TeX formatted, definitions cited, source Tag 08DJ, and Mathlib searches recorded.
- Small cases checked: zero complexes give the singleton bijection; over a field this is ordinary tensor-Hom; on the empty scheme both Hom sets are trivial.

Changes: corrected the source to `cohomology.tex` Tag 08DJ, added the broader statement-only child, removed unsupported proof steps, and synchronized `citations.json` and search records.

## Not duplicates

`lem-sc-derived-internal-hom-adjunction` vs `lem-pc-derived-internal-hom-pullback-adjunction`: the existing node concerns a specific pullback/direct-image comparison and its counit; the new node is the unconstrained tensor-internal-Hom adjunction on one scheme.
`lem-sc-derived-internal-hom-adjunction` vs `lem-sc-ext-stalk-localization`: the existing node identifies stalks of coherent Ext sheaves under Noetherian hypotheses; the new node gives the global derived Hom bijection for arbitrary complexes.
