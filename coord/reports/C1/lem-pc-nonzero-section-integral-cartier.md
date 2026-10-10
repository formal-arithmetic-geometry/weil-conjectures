Files written:

- `dag/nodes/sec-picard-framework/lem-pc-nonzero-section-integral-cartier.json`: statement node, split; no new nodes and no Mathlib leaves.

Attachments:

- None. A search of `WeilConjectures/` and `Comparator/` by the item id, zero-scheme terminology, and Cartier terminology found no exact sorry-free declaration.

WANTED:

- None. The Stacks pages for Tags `02OR`, `01WY`, `01WZ`, and `01OK` were available and read.

What was checked and corrected:

- The item statement was left unchanged. Its hypotheses introduce an integral scheme, an invertible module, a nonzero global section, and the zero scheme, and its conclusion spells out both the affine local equation and the effective Cartier ideal.
- No existing DAG node or blueprint node states this exact implication. The existing node `lem-sc-invertible-module-generic-stalk` supplies the needed restriction-injectivity fact; it is cited as a generic tool rather than duplicated.

## Review by C1

I read Stacks Divisors Lemma `02OR` (label `lemma-zero-scheme`), Definition `01WY` (label `definition-regular-section`), Lemma `01WZ` (label `lemma-regular-section-structure-sheaf`), and Properties Definition `01OK` (label `definition-integral`). I also read the existing DAG statements for `def-pc-integral-scheme`, `def-pc-zero-scheme`, `def-sc-invertible-module`, `def-nagata-effective-cartier-ideal`, `def-pc-divisor-line-bundle`, and `lem-sc-invertible-module-generic-stalk`.

Step 1 uses clause 3 of `lem-sc-invertible-module-generic-stalk`: sections on a nonempty open inject into the generic stalk. Therefore the nonzero global section remains nonzero on each nonempty affine trivializing open, and its coefficient in a basis is nonzero. This is the omitted regularity argument behind `02OR` in the integral case; the cited node's statement says exactly the injectivity used.

Step 2 uses `def-pc-integral-scheme` for the domain property of the affine ring and `def-pc-zero-scheme` for the local ideal equation `I_Z|_U = (a)`. In a domain, a nonzero element is a nonzerodivisor, so the local generator has the required property. Both cited statements introduce the objects used here and say these facts directly.

Step 3 uses `def-sc-invertible-module` for the affine trivializing cover, `def-nagata-effective-cartier-ideal` for the local nonzerodivisor criterion, and `def-pc-divisor-line-bundle` for the divisor terminology. The step is elementary once the preceding local facts are established.

I checked edge cases while reviewing the statement: the zero section is excluded by `s != 0`; the empty affine open is excluded explicitly; and disconnected or reducible schemes are excluded by integrality, since otherwise a nonzero global section could restrict to zero on a component. A search of all DAG nodes and the imported blueprint for “nonzero section”, “zero scheme”, and “Cartier divisor” found no duplicate statement. The Mathlib searches already recorded on the item (LeanSearch unavailable, LeanFinder/Loogle/grep finding only structure-sheaf results and no invertible-module zero-scheme theorem) were retained.
