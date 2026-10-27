## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-sections-avoid-regular-nodes.json`: item split in six steps, statement unchanged. No Mathlib match for the item.
- No new nodes and no new Mathlib leaves. Existing DAG inputs supply every non-elementary ingredient.
- `citations.json`: one verbatim statement quotation for each node used by each proof step.
- `searches.jsonl`: actual current-session searches, retained alongside the item's inherited search records.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag and the notions `nodal`, `semistable`, node avoidance and etale trait stalks. No project declaration gives this item. The existing proved `AlgebraicGeometry.Scheme.etale_trait_stalk` in `AlgebraicGeometry/Morphisms/EtaleTraitStalk.lean` supplies only the trait-stalk input, already recorded by `lem-sbc-etale-trait-stalk`.

## WANTED

None. The proof uses local Stacks sources already present.

## What needed repair

The item was statement-only; its statement is correct and is retained verbatim. The missing argument is now explicit: move to the nonzero-parameter etale nodal chart, locate its crossing, use regularity to force exponent one, lift the chosen multisection point by a fibre product, and contradict the principal maximal ideal in the resulting etale trait stalk. A lift of the entire multisection is unnecessary and was not assumed.

The item's inherited blueprint ancestor is null, even though its `from.place` and `via` chain specify the direct-image/marked-nodal-model route. `blueprint_refs.py ancestor` reports None as well. I retained this record and its precise place, searched the whole imported blueprint for `nodal`, `multisection`, `regular nodal`, `sections avoid`, and `smooth locus`, and found no imported statement of this lemma. The sole smooth-locus hit is a Frobenius fixed-point theorem and is unrelated. No chapter or unit route is changed.

The first new Loogle query used identifiers not recognized by that endpoint; it is recorded as invalid, with the diagnostic, and was replaced by `Algebra.Etale, IsDiscreteValuationRing` (zero hits). The semantic searches returned smooth/etale locus, formally unramified, ramification and elliptic good-reduction facts, none implying avoidance of nodes. Grep found no nodal/semistable theorem in Mathlib's algebraic geometry. Read the inherited search summaries before running the current differently phrased checks. No unrun searches are recorded.

## Unfinished work

None in this one-level split. The reused unsplit inputs remain their own items. No Lean was written and no compiler or build command was run.

## Not duplicates

No new nodes. In particular I reused `lem-sfb-trait-nodal-etale-dvr-model` instead of creating a second 0CDD local-chart node, and the narrower `lem-sfb-dvr-binomial-local-geometry` instead of restating the much broader `lem-sfb-dvr-nodal-chart-blowup-calculus`. The existing alternative `lem-sfb-dvr-nodal-etale-local-form` lacks the convenient smooth-generic refinement and fixed base uniformizer, which the cited trait-model node states explicitly. No cited node reaches this item through its dependencies.

## Review by Q21

I read `models.tex` Tag 0CDD (`lemma-etale-local-at-worst-nodal`) in full, including its two local equations, and the beginning of 0CDE (`lemma-blowup-at-worst-nodal`), where smooth generic fibre excludes the zero parameter. I read 0CDC (`example-blowup`), including the regularity distinction between exponent one and larger exponents. For the stalk argument I read `more-algebra.tex` 0AH0 (`lemma-regular-etale-extension`) and 0AP2 (`lemma-Dedekind-etale-extension`), and the project Lean proof of the canonical etale trait stalk. I also read `morphisms.tex` 01V9 (pointwise fibre criterion) and 02V4 (smooth locus), `descent.tex` 036U (source locality), and `spaces-properties.tex` 03H4 and its preceding scheme-point identification. There are no new nodes whose sources require a separate review.

For step 1, the fibre criterion states exactly the equivalence used to place the generic fibre in the smooth locus. Its local finite-presentation and flatness hypotheses are the item's hypotheses. The trait-model statement explicitly supplies etale DVRs, the unchanged base uniformizer, a common pointed neighbourhood, and a positive exponent when the generic fibre is smooth; no unstated nonzero-parameter assertion is taken from a proof. The expanded geometric-node hypotheses agree with those of the item.

For step 2, I checked that the binomial-fibres statement supplies smoothness away from the crossing over an arbitrary field, and that the local-geometry statement supplies flatness and finite presentation. The fibre criterion is applied over the DVR R', then etale smoothness and composition put the assertion over R. The cited source-locality node explicitly includes its pointwise equivalence: this is what carries smoothness through q and p. Thus we establish that the chart point is the origin before using its local ring.

For step 3, I opened both cited statements. Etale-stalk invariance supplies both directions of the regular-local equivalence, so regularity goes from W to U and then down to the chart. The binomial-local-geometry statement explicitly says regular at the origin exactly for exponent one, with no excellence/completeness/characteristic hypothesis. I use that narrow clause and no blowup result.

For step 4, the pointwise fibre-product node states existence of a point above the two specified points, including in the scheme special case. I checked this against 03H4 and its scheme-point identification. Base-change clause (1) and composition clause (2) give precisely that T is etale over R. The trait-stalk statement applies to an arbitrary point over the closed point and gives the actual stalk, its injective canonical map and the unchanged uniformizer; it does not require an affine chart, a section, a finite morphism, or a closed point of the entire source. This avoids the unwarranted assumption that a section lifts globally through an etale chart. Generic points and residue-field extensions cause no loss of the chosen point.

Step 5 is an explicit two-line principal-ideal calculation in that domain DVR: both pulled-back coordinates are in its maximal ideal because the stalk maps are local and their image point is the crossing; the model equation gives their product equal to the base uniformizer. Dividing once by that nonzero element would make a proper maximal ideal contain 1. The sole cited definition states domain, principality and nonfield, exactly what is used. This is elementary, not a hidden valuation-theoretic lemma. Step 6 writes the open-subscheme factorization through the original sheaf maps and their restrictions, using the actual definition of open immersion. Neither step hides a new statement.

I tested the empty B and empty W cases (vacuous), disconnected covers (argument pointwise), and arbitrary residue characteristic and imperfect residue fields (all local inputs allow these). On xy=pi a putative node section gives the written contradiction. On xy=pi^2 the map x=y=pi does pass through the node, but its total space is nonregular, so this tests the necessity of the regularity hypothesis. A ramified trait can also pass through xy=pi; it is excluded by etaleness, exactly where the uniformizer-preserving stalk theorem is applied. The argument actually works for any etale B, so finiteness imposes no missing requirement. All steps are under 2000 characters. Citations are verbatim statements and all off-unit generic tools are declared in `split_report.tool_uses`.
