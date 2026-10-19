# Worker report: lem-sf-normalized-derived-comparison-common-resolution

## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-normalized-derived-comparison-common-resolution.json`: statement; split with four explicit steps, using existing nodes only. Mathlib verdict: no exact match or one-line specialization found.
- `citations.json`: three entries, covering every citation of the proof steps, copied verbatim from the cited statements.
- `report.md`: this report. The search command generated `searches.jsonl`; `write_split.py` is a sandbox-only helper, not a DAG delivery file.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched the read-only slopmaster2 project under `WeilConjectures/` (and `Comparator/`) for the exact blueprint id, normalized/derived comparison, common resolution, and the derived-functor resolution/comparison APIs. No project declaration supplies all the hypotheses and conclusions of this item. The existing objectwise and composition results do not state this arbitrary normalized comparison theorem.

## Wanted sources

None. The source needed here is present: `literature/stacks-project/derived.tex`, Tag 070Y, label `lemma-K-injective-defined`. The item's comparison formula is an agent consequence, as its source field already says; I do not attribute this full formula to Stacks.

## Problems and changes

The imported item had a complete statement but no proof. I kept its statement and statement dependencies unchanged and wrote the missing argument, rather than introducing another node for its own conclusion. In particular, invertibility of Q(Fv) is a hypothesis in the normalization, not a consequence of exactness of r or preservation of K-injectives. The proof never assumes that rJ is K-injective.

The step-1 argument uses the exact-functor factorization leaf for preservation of quasi-isomorphisms. It uses the existing K-injective computation node for c_a = eta_I^{-1} RF(Qa), not merely the title of that node or an unnamed construction in its proof. Step 2 writes the full naturality square and cancels RF(a). Step 3 uses the supplied normalization. Step 4 writes the canonical transition equation for two arbitrary choices, so the final compatibility clause is not hidden in the word 'transport'.

The unit and chapter records were read. This item is a generic tool within `sk-def-sf-operations`, carrying the finite-level comparison required to form the inverse-system transition maps of its historical blueprint ancestor. That ancestor is a definition with no separate proof file; the current DAG statement explicitly cites `lem-sf-compact-support-restriction-of-scalars` for its transitions. I retained the existing precise `blueprint.from.place` and historical ancestry. The current snapshot contains no replacement node stating this exact abstract consequence. Searches of the whole imported blueprint by normalized, successive, K-injective and comparison, and the full DAG searches by Tag 070Y and the item concepts, found no duplicate statement. The K-injective computation sibling is a strictly more basic computation theorem and does not assert this beta comparison.

I retained the item's historical Mathlib search records and added only searches actually run by msearch for Q112. LeanFinder, Loogle, LeanSearch, and grep all returned results; none was marked unavailable. Read the principal hits in Mathlib: `CategoryTheory/Localization/DerivabilityStructure/PointwiseRightDerived.lean` lines 46–83 constructs a particular universal comparison and its unit equation; `CategoryTheory/Abelian/RightDerived.lean` lines 110–153 concerns right-derived cohomology functors on objects via nonnegative injective resolutions. Neither is a one-line specialization to the supplied beta normalized through two arbitrary unbounded resolutions. A second LeanFinder phrasing returned the same objectwise naturality family and exact-functor localization APIs.

## Unfinished work

None for this one-level split. The existing `lem-sf-kinjective-derived-map-computation` remains an independently queued node; I use its stated theorem, without editing or splitting it.

## Review by Q112

I read the standing brief, stage-1 contract, the three blueprint levels in SETUP, GOAL, dag-sync, worker role, and delivery-errors B–E in full. I read the item, its chapter and unit, the historical ancestor's blueprint text and current DAG statement, its parent's resolution argument, and Stacks `derived.tex` at `lemma-K-injective-defined` (Tag 070Y, checked against the tags mapping). That source says every K-injective complex computes the right derived functor. It does not itself state the normalized-comparison theorem, so `proof_origin.by` is agent and the actual naturality argument is included.

For step 1 I opened both cited node statements. `lem-weil-pbc-exact-functor-derived-factorization` explicitly states that the termwise exact functor preserves quasi-isomorphisms and supplies the natural localization factorization; r is exact additive, so its hypothesis is met. Composition of the two quasi-isomorphisms is elementary, and T is K-injective by the chosen v. `lem-sf-kinjective-derived-map-computation` explicitly defines c_a by eta_I inverse followed by RF(Qa), under the existence of K-injective resolutions for every complex. Those hypotheses are assumed for A and A', and F and G are additive. Applying the formula to v, w and u gives exactly the displayed identities; applying functoriality gives c_w = c_v RF(a). The cited node is in the item's own unit; the exact-functor node is a Mathlib leaf. There is no off-route non-leaf tool use.

For step 2 the only new input is naturality of the supplied beta. I checked domains: RF(a) goes from RF(rN) to RF(rJ), and s(RG(q)) from s(RG(N)) to s(RG(J)). After multiplication by RF(a) inverse, both sides run from Q(FT) to Q(sGJ). This is formal naturality and cancellation, so it is marked elementary and needs no new lemma node. For step 3 the normalization is applied at J and v, precisely the case assumed; it gives the desired inverse without invoking a nonexistent claim that restriction preserves K-injectivity.

For step 4 I reopened the computation lemma's final sentence: it states the canonical transition c_a' c_a inverse, its invertibility, its cocycle identity, and its compatibility with the morphism formula. Thus the quoted statement really supplies each claimed change of resolution. The equation L2 = dG L1 dF inverse follows by inserting the definitions and canceling, and identifies the right-hand sides for both choices. This addresses all choices, including changing u and v simultaneously. No step is over 2000 characters (lengths 805, 545, 516, 770); no hidden independent comparison lemma remains.

I checked identity resolutions, zero complexes, F=G=0, r=s=identity, and a restricted complex rJ that is not K-injective. In the identity case the formula reduces to the normalization; zero cases are the unique arrows between zero objects; in the last case the proof uses v and never an unavailable eta at rJ inverse. No boundedness, left exactness of F/G, monomorphic resolution, Grothendieck hypothesis or preservation of K-injectives is smuggled into the argument. There is no statement dispute, SGA citation, new definition, new node, duplicated item clause, or cycle introduced. I checked every proof-step citation against its statement and copied its exact used clause into citations.json.
