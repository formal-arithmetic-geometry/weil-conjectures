# Delivery report

Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-semilocal-dedekind-dvr-reduction.json` — item, split; two proof dependencies.
- `dag/nodes/sec-curve-estimates/lem-sc-dedekind-localization-dvr.json` — statement, Mathlib leaf; `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` at `Mathlib/RingTheory/DedekindDomain/Dvr.lean:128`.
- `dag/nodes/sec-curve-estimates/lem-sc-dedekind-intersection-localizations.json` — statement-only unsplit node; no Mathlib match.
- `citations.json` — verbatim quotes for every cited node in every item step.

Attachments: none.

WANTED: `literature/stacks-project/algebra.tex`, Algebra Definition 034W and Lemma 034X, for the Dedekind localization and intersection facts; the source text is not present in this checkout, so the proof origin records the agent reconstruction from those tags.

No source error was found. The original item was unsplit and had no matching declaration in `WeilConjectures/` or `Comparator/`. Existing DAG searches found no node stating the localization/intersection interfaces; the existing `lem-sc-normal-dim1-dvr` was not used because the localization clause has a direct Mathlib leaf.

## Review by J1

I read the item source reference (Algebra Definition 034W and Lemma 034X, with the reduction paragraph in Varieties Lemma 09N5) and checked the item statement against its hypotheses: B is semilocal Dedekind, K is its fraction field, the maximal ideals are finite, and the conclusion concerns all maximal localizations and the Jacobson radical. I searched the whole DAG and blueprint for each proposed interface before creating it. The localization node states exactly the local DVR fact needed in step 2 and was checked against the Mathlib declaration and source line 128; its Mathlib searches were run with LeanFinder, Loogle, and grep. The intersection node is self-contained, states both the intersection and contraction facts used in step 3, and records all three required searches with no match.

Step 1 uses only the definition of semilocality and the elementary fact that a maximal ideal in a one-dimensional domain is nonzero prime. Step 2 cites the localization node for the DVR conclusion; the identification of the localized fraction field with K is the direct quotient argument written in the step. Step 3 cites the two verbatim intersection/contraction statements. I checked both directions separately: Jacobson membership maps into every localized maximal ideal, while membership in all localized maximal ideals first puts x in the intersection B and then in every contracted maximal ideal. Small cases checked were a local DVR (one maximal ideal), where the criterion reduces to membership in its maximal ideal, and a semilocal localization of a Dedekind domain with two maximal ideals, where the intersection/contraction argument applies componentwise.

The item and both new nodes carry blueprint references. `citations.json` quotes the exact statements used by steps 2 and 3. The delivery is confined to the item directory and sandbox.
