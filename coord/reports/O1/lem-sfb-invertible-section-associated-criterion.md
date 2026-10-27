## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-invertible-section-associated-criterion.json`: statement, split; the complete scheme/line-bundle criterion is not a Mathlib leaf. Six proof steps reuse existing nodes. No new nodes and no new Mathlib leaves.
- `citations.json`: 17 entries, one for every step/node citation, quoting each cited statement verbatim.
- `report.md`: this worker report and self-review.
- `searches.jsonl`: the prescribed search command's own log, retained across the interruption. No delivery was started before the interruption.

## Attachments

None. Searched `lean/WeilConjectures/` for the item's blueprint tag, regular-section names, and associated-point/associated-prime section terminology. No declaration supplies all the clauses. Existing associated-stalk detection declarations are different statements; their presence does not close this criterion.

## WANTED

None. All the sources used are present locally.

## What was wrong or changed

The imported item's statement is correct and unchanged. Its proof was empty. Stacks Tag 0AYL, `divisors.tex`, `lemma-regular-section-associated-points`, itself omits the proof but gives the affine-trivialization hint. I expanded that hint rather than merely repeating it. The resulting proof uses exact element-annihilator associated primes, not a tacit identification with radical annihilators in arbitrary rings. The Noetherian hypothesis is used explicitly before descending association from the stalk.

The item's inherited `blueprint.from.node` is null: the ancestry tool returns `None` because the upstream created-item chain ends at `lem-sfb-admissible-direct-image` without a blueprint ancestor. I preserved that result and its detailed place/via, and explained the supporting-input link in `split_report.blueprint`. I read the latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, paragraph (3), as well as the repository chapter/unit records. This supporting regular-section argument changes no chapter or unit route and is not the unit's key node, so no unit realization record is delivered.

The generic tool `lem-sc-associated-localization-fg` is declared in `split_report.tool_uses`: its ring/module statement is used with R = M = A. The other theorem tools are existing Mathlib leaves. No new nodes were needed; the weakly-associated-prime nodes found during the search were deliberately not duplicated.

## What remains unfinished

No mathematical part of the split remains unfinished. Stage 1 only: no Lean was written, no compiler or Lake was run, no project or launcher file was modified, and no agent was started.

## Not duplicates

No new nodes. Searches of the DAG by tags 0AYL, 01WZ, 02OK, 056M, 00LD and by associated-point, affine-localization, nonzerodivisor, affine-basis and locally-Noetherian terminology found the inputs reused here. Blueprint searches for associated points/primes, regular sections and nonzerodivisors found no blueprint statement replacing this item. The ring zero-divisor criterion is already `lem-weil-pbc-noetherian-zerodivisors-union-associated-primes`, so it is cited as an existing Mathlib leaf.

## Review by O1

I read Stacks `divisors.tex` Tag 0AYL and its preceding regular-section definition/Tag 01WZ, and Tag 02OK (`lemma-associated-affine-open`). I also read `algebra.tex` Tag 0310 (`lemma-associated-primes-localize`) and Tag 00LD (`lemma-ass-zero-divisors`), `schemes.tex` Tag 01IT (`lemma-basis-affine-opens`), and `properties.tex` (`lemma-locally-Noetherian`, the affine-ring criterion). There are no new nodes requiring a separate source review. I opened the statement of each cited node and checked the following applications.

1. Step 1 uses `pqf-lem-affine-open-locnoeth` for the Noetherianity of every affine ring, not just a chosen atlas. `lem-weil-pbc-affine-open-stalk-localization` really gives the ambient stalk and its germ map as the prime localization; it is not merely a theorem about an abstract spectrum. `def-weil-pbc-localization-at-prime` explicitly specifies the maximal ideal. Thus the ring used later is exactly the ring in condition (ii).
2. Step 2 uses the definition `def-sc-associated-points` for the maximal ideal being an exact annihilator. `def-weil-pbc-noetherian-ring` supplies finite generation of the prime. The full statement of `lem-sc-associated-localization-fg` gives precisely the converse from the localized maximal annihilator, with no finite-generation assumption on the module. Its hypotheses hold with R = M = A. For the other direction I wrote the fraction calculation: r/t kills z/1 exactly when some u outside p has ur in p, and primality makes this equivalent to r in p. This avoids claiming that the cited descent lemma also proves ascent. It also proves z/1 is nonzero. The short calculation is part of the argument, not a new auxiliary node.
3. Step 3 takes a local frame from `def-sc-invertible-module`, and uses the actual residue-field quotient in `def-weil-residue-field`. The localization definition gives inverses to a/1 when a is outside p, so its residue is nonzero. If a is in p, its residue is zero. The residue-field basis vector is the class of the frame e_x. Thus this is fibre nonvanishing, not merely a nonzero germ; these are different conditions. Frame independence follows because each frame gives an isomorphism of that same fibre.
4. Step 4 applies `lem-weil-pbc-noetherian-zerodivisors-union-associated-primes` only after step 1 established its Noetherian hypothesis. Its statement is the full union equality for exact associated primes. Steps 2 and 3 therefore show that (i) avoids every prime in that union. The remaining injectivity argument is the explicit subtraction calculation a(b-c) = 0.
5. Step 5 uses local rank-one freeness and the full neighbourhood formulation of `lem-weil-pbc-affine-opens-basis`, so even a nontrivial line bundle has a suitable affine frame around the chosen associated point. The same union equality says that injective multiplication avoids every associated prime. Step 2 identifies the particular prime, and step 3 identifies its fibre. This does not assume every affine open trivializes L, global triviality, reducedness or quasi-compactness.
6. Step 6 proves the extra assertion that condition (ii) is the usual regular-section condition. `def-weil-sheaf-of-modules-category` says kernels are sectionwise, and the two frame/basis inputs give a cover of any open by affine frames. The kernel vanishes on each such open by (ii), then vanishes by the sheaf uniqueness axiom. Conversely sectionwise injectivity on an affine frame is multiplication by its coefficient. This is an elementary local sheaf argument; no uncited exactness or global-sections theorem is being used.

I checked the empty scheme and zero ring explicitly: both conditions hold and the zero ring's endomorphism is injective. On Spec of a field a zero section fails both conditions and a nonzero section satisfies both. On Spec(k[epsilon]/(epsilon^2)), epsilon has zero fibre at its associated point and kills epsilon, while a unit passes both tests. Embedded associated points are needed: in k[x,y]/(x^2,xy), the section y is nonzero at the minimal associated prime (x), but it vanishes at the embedded associated prime (x,y) = Ann(x) and yx = 0, so it correctly fails both conditions. No reduction to generic points was made. The argument also permits disconnected and non-quasi-compact locally Noetherian schemes because all choices are local and all covers may be infinite.

I checked delivery-errors B through E: no new self-contained statements to audit, no added or weakened hypothesis, no proof moved into a restatement node, no dependency on the proof rather than the statement of a cited node, and no assumption that two affine opens have affine intersection. All non-elementary facts are cited. Every step is below 2000 characters; none hides an additional lemma requiring a new node. `citations.json` is generated from the exact current statement strings, one entry for each use. The recorded searches include both natural-language phrasings, LeanSearch, Loogle and Mathlib grep; the ring hit was read at `Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean:238`, and it supplies an existing leaf rather than an attachment of the whole item.
