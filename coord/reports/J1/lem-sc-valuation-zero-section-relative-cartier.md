Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-zero-section-relative-cartier.json` — split proof; no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-pc-recd-fibre-cartier-local.json` — statement-only Tag 062Y(3) child; no Mathlib match.
- `citations.json` — verbatim citations for both proof steps.

Attachments: none.

WANTED: none.

What was wrong: the imported item was statement-only even though it is a real input to the Tag 0EX8 proof. Its source uses the local part (3) of Divisors Lemma 31.19.9, which was not stated by the existing all-fibres criterion node, so I added that precise local criterion rather than citing a statement that did not supply the step.

What could not be finished: no sorry-free Lean declaration states this valuation-ring Cartier lemma; stage 1 therefore records the natural-language proof only.

## Not duplicates

`lem-pc-recd-fibre-cartier-local` vs `lem-pc-recd-locally-principal`: the existing node assumes every fibre is an effective Cartier divisor and concludes globally; the new node is the local Tag 062Y(3) criterion from one fibre germ and local principality.

## Review by J1

I checked the target against More on Morphisms, Lemma 37.33.3 (Tag 0EX8), especially its final paragraph, and checked the auxiliary criterion against Divisors, Lemma 31.19.9 (Tag 062Y), part (3). Step 1 uses `lem-pc-zero-scheme-properties` for local principality, `lem-pc-nonzero-section-integral-cartier` for the nonzero section on the integral closed fibre, and the new local criterion exactly for the resulting fibre-Cartier germ. Properness over the local base supplies the specialization of every point of the zero scheme to the closed fibre; this is the specialization assertion used in the source paragraph. Step 2 is the definition of relative effective Cartier divisor, so flatness is immediate. I read each cited node's statement and verified the hypotheses: flat finite presentation for the criterion, invertibility and nonzero closed-fibre restriction for the integral Cartier lemma, and properness/locality for specialization. I tested the affine-domain case with a nonzero coefficient and checked the zero-section and flatness conclusions on the empty-zero-locus edge case. The required LeanFinder, Loogle, grep, and LeanSearch searches were run for both the item and the new child; LeanSearch was unavailable and recorded as such.

## Second reading by J1

- Item statement: checked against More on Morphisms, Lemma 37.33.3 (Tag 0EX8), final paragraph; hypotheses proper, flat, finite presentation, valuation base, integral closed fibre, invertible module, and nonzero restriction are preserved, and the relative-Cartier conclusion agrees.
- `lem-pc-recd-fibre-cartier-local`: checked against Divisors, Lemma 31.19.9 (Tag 062Y), part (3); the local fibre-Cartier and locally-principal hypotheses and neighbourhood conclusion agree exactly.
- Step 1: `lem-pc-zero-scheme-properties`, `lem-weil-pbc-proper-closed-image`, `lem-pc-nonzero-section-integral-cartier`, and `lem-pc-recd-fibre-cartier-local` were opened; each cited statement supplies the fact used. The specialization argument is now explicit: the closure image is closed, contains the generic point, hence contains the closed point of the local spectrum.
- Step 2: checked against `def-pc-relative-effective-cartier`; its flatness clause gives the conclusion directly and is elementary.
- New-node form: the auxiliary node is statement-only, self-contained, has definition dependencies, a Tag 062Y source, blueprint fields, and recorded searches; no Mathlib declaration matches.
- Edge cases checked: empty zero locus (unit section), affine integral domain with a nonzero coefficient, and the zero section excluded by the nonzero closed-fibre hypothesis.

Changes made: added the existing proper-closed-image node to step 1 and `proof_deps`, copied its verbatim statement into `citations.json`, and expanded the report. This repairs the previously uncited properness-to-specialization fact; no node statements were changed.
