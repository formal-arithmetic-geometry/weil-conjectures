1. Files written:

   - `dag/nodes/sec-picard-framework/lem-sc-finite-pushforward-derived-hom-qcoherent.json`: split item.
   - `dag/nodes/sec-picard-framework/lem-sc-coherent-pseudo-coherent.json`: statement-only unsplit node; Mathlib no match.
   - `dag/nodes/sec-picard-framework/lem-sc-pseudo-coherent-rhom-qcoherent.json`: statement-only unsplit node; Mathlib no match.

2. Attachments: none.

3. WANTED: none.

4. The item had no Lean declaration. I read Stacks Tags 01Y6, 08E8, 0AUC and 0AUP. Existing node `lem-weil-pbc-finite-pushforward-coherent` supplies coherence of the finite pushforward, so I did not duplicate that result. The two new nodes isolate the non-elementary implications: coherent implies pseudo-coherent on a Noetherian scheme, and derived internal Hom from a pseudo-coherent first argument preserves bounded-below quasi-coherence. The proof then applies those statements and observes that restriction of scalars preserves the underlying quasi-coherent cohomology. I checked the hypotheses: finiteness and Noetherianity give the coherence node's assumptions, and the given K is exactly bounded below with quasi-coherent cohomology. Small cases include f the identity and K concentrated in degree zero.

## Review by G1

I checked the target statement against `duality.tex` Tag 0AX2 and its cited Tags 0AUC/0AUP. Step 1 cites the existing finite-pushforward coherence statement and the new coherent-to-pseudo-coherent statement; their quoted clauses say exactly what Step 1 uses. Step 2 cites the new pseudo-coherent RHom statement, including its A-module conclusion. Step 3 uses its explicitly stated restriction-of-scalars conclusion and is elementary. Both new statements are self-contained, statement-only, and were searched in the whole DAG and blueprint before creation; no existing node stated either theorem. Lean source grep found no declaration for the item or either new statement. Mathlib searches were run with LeanSearch, LeanFinder and grep for both new nodes (LeanSearch unavailable; the other searches found no exact theorem).

5. Nothing remains unfinished.

## Not duplicates

lem-sc-coherent-pseudo-coherent vs lem-sc-derived-internal-hom-stalk-localization: the existing node localizes derived internal Hom at stalks for a coherent source, while the new node states the distinct global implication that a coherent module on a Noetherian scheme is pseudo-coherent.

lem-sc-coherent-pseudo-coherent vs lem-sc-ext-stalk-localization: the existing node concerns stalk localization of Ext, whereas the new node concerns pseudo-coherence of a coherent complex.

lem-sc-pseudo-coherent-rhom-qcoherent vs lem-sc-finite-pushforward-derived-hom-qcoherent: the item specializes the general RHom preservation theorem to the finite pushforward algebra and also proves that algebra pseudo-coherent; the new node is the general theorem with an arbitrary pseudo-coherent module.

## Second reading by G1

- Item statement: checked against duality.tex Tag 0AX2 (`lemma-finite-twisted`), including finite Noetherian hypotheses and both quasi-coherence conclusions; verdict correct.
- Step 1: checked against coherent.tex Tag 01Y6 and perfect.tex Tag 08E8; verdict correct.
- Step 2: checked against duality.tex Tag 0AX2 and perfect.tex Tag 0A6H clause (1); verdict correct after source-label repair.
- Step 3: checked against duality.tex Tag 0AX2; the underlying complex, cohomology, and quasi-coherence condition are unchanged under restriction of scalars by the derived-category definition; verdict elementary and correct.
- `lem-sc-coherent-pseudo-coherent`: checked against perfect.tex Tag 08E8; self-contained and non-duplicate; verdict correct.
- `lem-sc-pseudo-coherent-rhom-qcoherent`: checked against perfect.tex Tag 0A6H clause (1); verdict correct after correcting unrelated Tags 0AUC/0AUP.

Changes: corrected the internal-Hom source to Tag 0A6H; expanded Step 3 with the restriction-of-scalars definition argument; kept the proof on the unit route; updated citations and the review record.

Second-reading repair: corrected `lem-sc-coherent-pseudo-coherent` to cite `def-pur-pseudo-coherent-complex` (rather than the unrelated derived-internal-Hom definition); the item source is the single Tag 0AX2 lemma.

## Not duplicates

def-pc-derived-category-qcoh-algebra vs lem-sc-derived-internal-hom-restrict-open: the existing node concerns restriction of derived internal Hom to open subschemes, while this definition introduces the derived category and bounded-below quasi-coherent subcategory for an arbitrary quasi-coherent algebra.

def-pc-derived-category-qcoh-algebra vs lem-sc-affine-rhom-qcoherent: the existing node proves an affine RHom quasi-coherence theorem, while this definition only defines D(B) and D^+_{QCoh}(B) for a sheaf algebra.
