# Stage-1 delivery: lem-per-algebraic-valuation-coarsening-correspondence

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-algebraic-valuation-coarsening-correspondence.json`: existing statement, split into six steps, with no new nodes and no new Mathlib leaves.
- `citations.json`: six literal statement excerpts, covering every use in every proof step.
- `report.md`: this signed review. `searches.jsonl` is the unmodified output log written by msearch.

## Attachments

None. Searching `lean/WeilConjectures/` for the exact blueprint tag and for coarsening/value-group torsion found no project declaration stating the whole interface. The related `lean/Sheaf/RingTheory/ValuationValueGroupTorsion.lean:35` declaration `WeilConjectures.algebraic_extension_value_group_torsion` has an explicit `sorry` and proves only the torsion input; it is not an attachment for this item.

## WANTED

WANTED: Bourbaki, Commutative Algebra, Chapter VI §§4 and 8, the convex-subgroup and algebraic-extension valuation background recorded in the item's source, for lem-per-algebraic-valuation-coarsening-correspondence. The text is unavailable in the local literature. No assertion is attributed to unread Bourbaki text: the correspondence is reconstructed explicitly from the admitted existing torsion interface and elementary fractions, and `proof_origin.by` is `agent`. This discharges the repair note's option to reconstruct missing-source input rather than assume it.

## Audit of the imported item and repair order

The released stage-1 note dated 2026-10-24 re-admits this exact interface and withdraws its historical proof and theorem attachment. The local live item was genuinely unsplit, and there was no earlier sandbox proof/report/search log to salvage. I preserved the statement, source, statement dependencies, provenance and all inherited Mathlib searches. I did not read or revive a historical git proof. No statement dispute or change was needed. The latest blueprint ancestor is `lem-per-artin-gabber-affine-curve`; the retained provenance places this input under Step 3, local-model purity, strict completion and the dense henselian valued-field comparison. I read the current chapter, unit and ancestor proof in `literature/blueprint/latest/`. This delivery does not change that route or use the excluded punctual-completion restatements.

ILO XX §4.4, printed pp.373–374 (PDF pp.379–380), gives the non-Noetherian abelian completion sketch, reduces the valued case to a dense embedding of henselian fields, and refers to Krasner forms in Bourbaki VI §8 exercises 12 and 14(a). It does not itself prove the present coarsening correspondence. Stacks `algebra.tex`, Tag 00ID (`lemma-valuation-group`), gives the quotient ordered-group convention; Tag 0AAV (`lemma-valuation-ring-cap-field-finite`) gives only nontrivial restriction; neither is misrepresented as the full correspondence. I read the adjacent fraction-field inverse-alternative and restriction/localization discussion as well. The missing argument is supplied by explicit fractions in Steps 3–5.

For the non-elementary input I read the entire existing statement and proof of `lem-trf-valuation-value-group-torsion`. Its source is Stacks `more-algebra.tex`, Tag 0ASJ (`lemma-etale-extension-valuation-ring`), first proof paragraph, which uses finite index of value groups. The existing node isolates the stronger general algebraic element form and supplies a polynomial proof. I read that paragraph in the Stacks source. Its statement applies to arbitrary algebraic extensions, so it certainly applies to the finite algebraic extension here. No henselianity, separability, excellence, finite rank, discrete value group, or residue-field hypothesis is introduced.

## Searches and reuse

Whole-DAG statement/title searches found the existing torsion input, the valuation prime/convex correspondence, the ordered positive-cone correspondence, and height/coarsening results. I read those statements. The torsion node says exactly what is needed; the convex and height results are unnecessary for the fraction argument. The two blueprint searches `coarsening correspondence` and `algebraic valuation` each returned zero, and the broader convex/valuation searches supplied no exact imported equivalent. The item retains `same_as: []`. The ancestor command confirmed `lem-per-artin-gabber-affine-curve`.

Actual fresh msearch runs used LeanFinder twice, LeanSearch, Loogle, and two source greps. The hits were read, including `Valuation.HasExtension` in `Extension.lean:57–85`, the coarsening/prime equivalence in `ValuationSubring.lean:264–395`, `LocalSubring.lean:36–115`, and `Minpoly.lean:39–58`. HasExtension identifies a restricted valuation with a chosen base valuation; it does not classify coarsenings across an algebraic extension. The prime equivalence is for overrings of one valuation subring in one field. Minimal-polynomial constant-coefficient results and discrete uniformizer results do not assert the arbitrary algebraic torsion property. The second LeanFinder phrasing returned integer/fraction-field characterizations and tilt definitions, not the item. Thus no exact or one-line Mathlib attachment was found. Every fresh record in the item is copied from the actual search log, with its exact tool and query; inherited searches are retained as instructed.

## Not duplicates

No new nodes are created. In particular the torsion clause is cited from `lem-trf-valuation-value-group-torsion`, not restated in a new node. The fraction-ring closure and membership computations are proof steps, not new nodes. The existing torsion node is declared as a generic tool use from another unit; the current unit supplies no such algebraic valuation lemma.

## Review by Q96

I checked B–E of `coord/delivery-errors.md` against the node files and open source text. The only non-elementary input is the existing torsion lemma; no assertion in this proof is taken from its internal construction instead of its statement. There are no new statement-only node, source-tag, definition-dependency or duplicate obligations. The six proof steps have the following precise support.

1. I read the statement of `def-trf-valuation-ring`. It gives exactly the fraction-field alternative used for restriction and for representing a field element as a fraction. Intersecting with a subfield preserves it. Units are elements with their inverse in the ring, so the kernel equality and preservation of the quotient order follow directly; no convex-subgroup classification is used.
2. I read `lem-trf-valuation-value-group-torsion`, which explicitly gives (x^n=au) with (n\ge1), (a\in K^\times), and (u,u^{-1}\in W). Algebraicity and the inverse alternative are present here. Taking quotient classes proves (nw(x)=w(a)), and every class has a representative. This step is marked non-elementary because it uses that theorem.
3. Only `def-trf-valuation-ring` is cited. Every proposed denominator is nonzero and in (V\subseteq W), denominator products remain eligible, and the displayed addition, product and negation formulas show the set is a subring. It contains (W), hence has the inverse alternative and fraction field (L). Thus this is an elementary construction, with no localization existence theorem hidden in it.
4. Only the same valuation definition is needed. If (y/s\in K), then (y=s(y/s)\in K\cap W=V); the denominator inverse is in (V') by construction. In the reverse direction an element of (V'\setminus V) has inverse in (V), so its own inverse supplies an allowed denominator. The zero case is explicitly separated.
5. Both cited statements were reread. For (x\in U\setminus W), the inverse alternative gives (x^{-1}\in W), and the existing torsion statement applies to this nonzero (x). The factor (u) and (x) are units of (U), so (a=x^n/u\in R^\times). Crucially the denominator (s=a^{-1}=u(x^{-1})^n) lies in (W\cap K=V), not merely in (R); its inverse is in (R). The numerator (u(x^{-1})^{n-1}) belongs to (W) even when (n=1). This explicitly proves uniqueness instead of invoking an unstated coarsening theorem. The step is marked non-elementary because it uses the torsion lemma.
6. This step uses only the two already established inverse identities and set inclusions. It checks both inclusion directions through the denominator sets. The overring (L) restricts to (K); uniqueness forces it to be the only one. Hence properness in the non-field sense follows, and strictness over the initial rings is preserved as well.

I tested (K=L) (the correspondence becomes the identity), (W=L) (both overring posets are singletons and both value groups are zero), and (V=K) (the torsion lemma plus the fraction formula forces (W=L)). Rank-one and higher-rank valuations are both allowed; no finite chain or Archimedean argument enters. Purely inseparable finite extensions cause no change because the input is algebraicity alone. The exponent-one and zero-element cases are handled explicitly. Dropping algebraicity would be wrong: (K=k\subset k(t)=L), (W=k[t]_{(t)}) has (V=k), but (W\ne L) and both restrict to (k); its quotient value group is \(\mathbf Z\), not torsion. This confirms the essential hypothesis is retained.

All six citation excerpts were checked as verbatim substrings of their current node statements. No proof step exceeds 2000 characters; the whole proof has 2848 characters. No long step conceals a separate comparison or classification lemma. No SGA source, completion regularity assertion, or excellence assumption is used.

## Unfinished work

None for this one-level split. The reused torsion interface remains an existing downstream item with a sorry declaration; stage 1 permits this dependency. The required dry run passed; the push result is printed by deliver.py after this report is finalized.

## Validation

The first required `deliver.py Q96 lem-per-algebraic-valuation-coarsening-correspondence --no-push` exited successfully with `OK (not pushed)` at `e0aed7dcd88`, reporting that server preflight passed. Local read-only comparisons also confirmed that statement, source, statement dependencies, blueprint provenance, creation/audit fields and inherited searches are preserved, the proof dependencies equal the union of the step citations, and every citation excerpt is literal. This report update is followed by a final dry run and then the authorized direct push.
