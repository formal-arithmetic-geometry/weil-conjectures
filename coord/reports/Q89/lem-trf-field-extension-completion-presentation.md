## Files written

- `dag/nodes/sec-trace-formula/lem-trf-field-extension-completion-presentation.json` — item, statement split into six proof steps, no new nodes, Mathlib search verdict: no direct match.
- `citations.json` — 17 verbatim citations for the non-elementary step uses.

## Attachments

None. I searched the slopmaster2 WeilConjectures source for the item id and for completion/base-change/power-series terminology; no sorry-free project declaration states this item.

## WANTED

None. The cited Stacks source is present locally at `literature/stacks-project/varieties.tex`.

## What was checked and corrected

The imported item was unsplit and its four existing Mathlib searches were retained after reading their results. I searched the whole DAG and blueprint for the Tag 0C54 completion/base-change statement and for its component lemmas. The needed facts already exist as DAG nodes, so I created no duplicate auxiliary node. In particular, the finite-type Noetherian, field-extension flatness, flat-localization, finite-separable tensor reducedness, pointwise dimension preservation, completion locality/completeness, flatness of completion, power-series universal property, complete-source surjectivity, power-series Noetherianity/completeness, and flat-mod-injective nodes are all existing nodes cited by the proof.

The source is Stacks Project `varieties.tex`, Tag 0C54, whose proof uses Tags 0C4Y and 0C50. Step 1 verifies the finite-type local rings, the flat local map, equality of maximal ideals using reducedness of the finite separable tensor fibre, and equality of local dimensions using the existing pointwise field-extension dimension node. Step 2 checks that both completions are Noetherian local and complete, and that the induced completion map is flat. Step 3 applies the existing complete-target power-series universal property to the images of the chosen variables. Step 4 checks that the transported kernel relations vanish and proves surjectivity via the complete-source surjectivity lemma; its hypotheses are supplied by the field power-series completion node and the completion quotient node. Step 5 applies the existing flat-mod-injective criterion to the map from the coefficient-extended quotient, with the residue map K to K equal to the identity, proving injectivity. Step 6 records the resulting K-algebra isomorphism and the variable-image compatibility.

I checked every citation against the exact statement of its node and recorded the relevant sentence verbatim in `citations.json`; `proof_deps` is exactly the union of step uses. The proof has no step longer than 2000 characters. I tested the construction on the basic cases S=k[x] at (x), K=k, and a separable quadratic residue extension embedded in an algebraically closed K; the map reduces to the evident identity/base-change presentation. The inseparable residue-field example from the Tag 0C52 discussion is excluded by the finite-separability hypothesis, as required.

## Review by Q89

I read the item node, the unit `sk-i-curve-zero`, the ancestor blueprint reference, and the complete Tag 0C54 proof in `literature/stacks-project/varieties.tex` (including its uses of Tags 0C4Y and 0C50). I also opened the statement of every cited DAG node. Step 1 uses exactly the finite-type Noetherian, field-extension faithfully-flat, flat-localization, finite-separable tensor reducedness, and pointwise dimension statements; their hypotheses match S, k, K, p, and q. Step 2 uses the completion Noetherian/local/residue/complete statements and the flatness-of-completion statement, with A and B Noetherian local and m_A B=m_B checked in Step 1. Step 3 uses only the universal property for a complete target and the completion quotient statement, with the variable images generating the completed maximal ideal. Step 4 uses the field power-series Noetherian/local/complete statement, the completion quotient statement, and the complete-source surjectivity criterion; the reduction map is K to K. Step 5 uses the field power-series Noetherian/local statement, completion flatness, and flat-mod-injective; the source quotient is finite over itself and the residue map is injective. Step 6 is elementary transport of the isomorphism and variable images.

No statement was changed. No new node was needed, no duplicate was introduced, and no SGA source was used. I checked the edge cases K=k and S=k[x] at (x), and confirmed that inseparable residue extensions are precisely where the separable tensor/reducedness input can fail.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## What could not be finished

Nothing remains for this stage-1 split.
