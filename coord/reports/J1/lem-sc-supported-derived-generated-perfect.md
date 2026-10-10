1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-supported-derived-generated-perfect.json` (split item; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-pc-supported-perfect-generator.json` (statement-only child; Mathlib searches found no match).

2. Attachments: none.

3. WANTED: none.

4. What was checked or corrected:

- The item source `literature/stacks-project/duality.tex`, Tag 0E4G, was read at the proof of Lemma 48.4.3(3). The cited inputs were checked in `/home/ubuntu/c1-stacks-review/perfect.tex` (Tag 0A9A, `lemma-generator-with-support`) and `/home/ubuntu/c1-stacks-review/derived.tex` (Tag 09SN, `lemma-write-as-colimit`). The existing DAG statement `lem-pc-compact-generators-build-objects` was read in full and is the needed 09SN generalization, so no duplicate child for 09SN was created.
- Step 1 uses the new supported-generator statement. Its hypotheses match the item after setting `X=Y` and `T=Y\\setminus V`; the resulting generator is explicitly perfect and supported.
- Step 2 checks the remaining hypotheses for the 09SN specialization. Direct sums preserve support because cohomology of a direct sum is the direct sum of cohomology sheaves, and the existing `lem-pc-perfect-object-compact` statement gives compactness of E in the ambient derived category, hence in the full supported subcategory. The singleton coproduct is therefore a generator by Step 1.
- Step 3 applies the exact statement of `lem-pc-compact-generators-build-objects`. Since that statement starts at `X_1`, I explicitly prepend `Q_0=0`; the cone of `0\\to X_1` is `X_1`, already a coproduct of shifts of E, and the telescope is unchanged.
- Mathlib searches were run for the item and new child with LeanFinder, Loogle, grep, and LeanSearch. LeanSearch was unavailable; all recorded queries and verdicts are retained in the node files. No existing DAG node states the support-specific generator theorem. `lem-pc-derived-qcoh-perfect-generation` is not a duplicate: it concerns all of D_QCoh(Y), while the new child concerns the supported subcategory and requires E itself to be supported.

## Not duplicates

`lem-pc-supported-perfect-generator` vs `lem-pc-derived-qcoh-perfect-generation`: the latter generates the entire quasi-coherent derived category by all perfect complexes, while the new statement gives one perfect complex supported on a specified closed subset that generates only the supported subcategory.

## Review by J1

I checked the item proof against Tag 0E4G and read the complete statements of every cited node. The new child follows Tag 0A9A for a quasi-compact, quasi-separated scheme and a closed T with quasi-compact complement. The compactness hypothesis in Step 2 is exactly the existing perfect-object compactness statement, and the support and coproduct assertions are the direct closure facts used in the Tag 0E4G proof. Step 3 uses the existing 09SN split, whose statement supplies the telescope, initial coproduct of shifts, and transition cones; I verified that adjoining the zero object preserves the required cone condition. I also checked the edge case of an empty supported subcategory: the generator may be zero, and the singleton construction still yields the zero sequence. The only correction needed during review was removing an accidental duplicate `blueprint` JSON key before the dry run.

5. What could not be finished: nothing.

## Second reading by J1

- Item statement: checked against Stacks Tag 0E4G (Lemma 48.4.3(3)) and its use of Tags 0A9A and 09SN; the quasi-compactness, quasi-separatedness, quasi-compact open complement, supported cohomology, and telescope clauses agree.
- Step 1: checked against the complete statement of `lem-pc-supported-perfect-generator` and source Tag 0A9A; all hypotheses match under X=Y and T=Y\\setminus V, and the supported perfect generator is exactly supplied.
- Step 2: checked against `lem-pc-derived-qcoh-direct-sums` and `lem-pc-perfect-object-compact`; the direct-sum cohomology statement supplies closure of the supported subcategory, while ambient compactness restricts because coproducts agree.
- Step 3: checked against the complete statement of `lem-pc-compact-generators-build-objects` and source Tag 09SN; adjoining Q_0=0 preserves the first cone condition and the telescope.
- New node `lem-pc-supported-perfect-generator`: checked B1-B7 against Tag 0A9A; it is statement-only, self-contained, uses definition nodes, has a tag and label, and has recorded LeanFinder/Loogle/grep/LeanSearch searches with the unavailable service marked unavailable. Empty and field-supported cases are consistent.
- Changes: corrected the item node's `created.item` to this item; cited `lem-pc-derived-qcoh-direct-sums` in Step 2 and `proof_deps` to support coproduct closure; retained the existing child and all prior review sections unchanged.
