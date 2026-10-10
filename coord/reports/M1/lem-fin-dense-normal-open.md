Files written:

- `dag/nodes/sec-smooth-purity/lem-fin-dense-normal-open.json`: item split into four proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited dependency.

Attachments:

- `AlgebraicGeometry.Scheme.exists_isIso_fromNormalization_restrict` belongs to existing node `lem-sc-normalization-exists` (source `WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean:483`); it does not state normality of the open and therefore is not an attachment for this item.

WANTED:

- None.

What was checked and corrected:

- The imported proof used the finite normalization lemma and a common-denominator argument, but did not make the affine chart, fraction field, or nonzero principal element explicit. Those are now stated in the steps. The existing nodes `lem-weil-pbc-integral-closure-finite-extension-normal` and `lem-weil-pbc-localization-normal-domain` were found by searching the whole DAG and are cited instead of creating duplicates.

## Review by M1

I read the item source in `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/lem-fin-dense-normal-open.md`, the imported item, and the source declarations in `WeilConjectures/Mathlib/AlgebraicGeometry/Normalization.lean`. The latter has a sorry-free theorem giving a nonempty open where normalization is an isomorphism, but its conclusion does not assert that the open is normal, so it is not an exact attachment.

Step 1 uses the definition node for normalization and the existing finiteness lemma; their statements introduce the integral closure and say the normalization map is finite under the stated finite-type hypotheses. Step 2 is elementary finite-module denominator clearing. Step 3 uses the existing integral-closure normal-domain leaf, which supplies both normality and the fraction field, and the existing localization-normal-domain leaf, whose hypotheses are met because the chosen denominator is nonzero. The conventions node supplies the meaning of integral and normal scheme. Step 4 is the elementary fact that a nonempty principal open in an integral scheme is dense, again using the conventions statement for integrality.

I checked the small edge cases in the denominator argument: the affine chart is nonempty, hence its domain ring is nonzero; a finite product of nonzero denominators remains nonzero; and localization at that element is nonempty. The Mathlib searches for the item were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as such. No new node was created, so there are no new-node search or duplicate obligations.
## Second reading by M1

- Item statement: checked against the blueprint node and its integral finite-type hypotheses; verdict correct, including the nonempty normal open conclusion.
- Step 1: checked the normalization definition, finite-normalization statement, and scheme conventions (finite affine maps are finite module maps); verdict correct after adding the missing conventions citation.
- Step 2: checked finite module generators and common-denominator localization; verdict elementary and correct, with the finite-module input cited by Step 1.
- Step 3: checked the integral-closure normal-domain and localization-normal-domain statements, then the normal-scheme definition; verdict correct for the nonzero denominator and affine normality.
- Step 4: checked nonemptiness of a principal open in a domain and density in an integral scheme; verdict elementary and correct.
- New nodes: none; duplicate and Mathlib-leaf searches are therefore inapplicable.
- Changed Step 1 to cite `def-weil-pbc-scheme-conventions` and added its verbatim citation quote; this closes the metadata's previously uncited use.
- Tested the denominator argument on a field, a nonzero domain, and the zero-dimensional case; no edge-case failure found.
