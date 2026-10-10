1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-finite-sections-cover-qc.json`: item, statement split, no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-global-generation-nonvanishing-cover.json`: new statement-only dependency, no Mathlib match.
- `citations.json`: direct step citations with verbatim statement excerpts.

2. Attachments

None.

3. WANTED:

None.

4. What was wrong or incomplete

The imported item had an empty proof despite its source giving the compactness step. The source sentence also relies on the unstated intermediate fact that a globally generated invertible module has a nonvanishing section at every point when the generating family is not assumed finite. I supplied that fact as the strictly smaller helper node and then applied quasi-compactness. No statement was changed.

5. What could not be finished

Nothing.

## Review by C1

I read the item against Varieties Lemma 09NC in `literature/stacks-project/varieties.tex`, specifically the sentence beginning “Again because X is quasi-compact”. I also read the existing statements of `def-weil-pbc-quasi-compact-scheme`, `def-weil-pbc-generating-sections`, `def-sc-invertible-module`, `def-weil-pbc-ample-invertible-module`, `lem-weil-pbc-locally-surjective-iff-stalks`, and `lem-weil-pbc-nakayama-local-generators`. The item's sole step uses exactly the helper's union statement and the quasi-compact definition; the finite-subcover extraction is the elementary topological consequence of those statements.

The new helper is self-contained: its scheme, invertible module, generating family, and nonvanishing loci are all introduced and cited to definitions. Step 1 uses the generating-sections definition and the existing stalk-surjectivity statement. Step 2 uses the rank-one stalk property of an invertible module and the existing general submodule form of Nakayama; I explicitly use the general form so an arbitrary generating family is allowed. Step 3 is the defining equivalence between a nonzero residue class and membership in the nonvanishing locus. I tested the argument on an affine scheme with the trivial line bundle, on a one-point scheme, and on the empty scheme; the union and finite-subcover conclusions behave as stated. I searched the DAG and blueprint for an equivalent nonvanishing-cover lemma before creating the helper, and searched Mathlib with LeanSearch, LeanFinder, and source grep; no exact declaration was found.
