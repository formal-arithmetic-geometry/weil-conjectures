Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-affine-standard-cover-finite-presentation-flat.json`: statement split into three steps.
- `dag/nodes/sec-curve-estimates/lem-sc-affine-standard-cover-finite-free-local-fp-flat.json`: new unsplit statement; Mathlib component matches only.
- `dag/nodes/sec-curve-estimates/lem-sc-affine-standard-cover-finite-presentation-localization-span.json`: new Mathlib leaf, `Module.FinitePresentation.of_localizationSpan`.
- `dag/nodes/sec-curve-estimates/lem-sc-affine-standard-cover-flat-localization-span.json`: new Mathlib leaf, `Module.flat_of_localized_span`.

Attachments: none.

WANTED: `literature/stacks-project/algebra.tex`, Tag 00NX and the cited Tags 00EO and 00HT, is absent from this checkout; the proof route was checked against the current Stacks web statements and the existing node source metadata.

## Review by E1

I checked the item against the Stacks Tag 00NX statement and its proof chain (7) => (4) => (5) => (1). The local bridge node states exactly that a finite free localization is finitely presented and flat. Step 1 uses only that bridge and verifies the same finite family generates the unit ideal as the span condition required by the two descent lemmas. Step 2 cites the new Mathlib leaf whose statement is precisely finite presentation from finitely presented localizations over a unit-ideal span, and cites the existing definition node for the conclusion. Step 3 cites the new Mathlib leaf whose statement is precisely flatness from flat localizations over the same span, and cites the existing flatness definition. I read the Mathlib source at `LocalProperties/FinitePresentation.lean:48-52` and `Flat/Localization.lean:100-107`; both declarations specialize directly to the standard-open localizations. I searched the DAG and blueprint for duplicate nodes and found no existing nodes for either descent declaration. Small cases checked include a one-element cover with $f_1=1$ and the product ring $R=k\\times k$ with the two idempotent standard opens. I corrected the imported unsplit item by supplying all proof steps, dependencies, blueprint references, and verbatim citation quotes.
