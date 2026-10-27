# Stage-1 report: lem-trf-etale-localization-valuation-domain

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-localization-valuation-domain.json: statement item, now split into four steps; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-weak-dimension-one-valuation-criterion.json: new statement-only lemma, unsplit; no Mathlib match. It states the general equivalence of length-one flat resolutions with valuation local rings, and its nonzero local-ring specialization.
- citations.json: one verbatim statement quote for each of the seven step/node pairs.

One new node; zero Mathlib leaves. The new node has no proof, proof dependencies or hidden proof sketch. The item's assembly proof is 1646 characters, with no step approaching 2000 characters.

## Attachments

None. I searched the current project source lean/WeilConjectures by the exact item id and valuation terminology. There is no declaration of the complete item. In WeilConjectures/RingTheory/ProEtale/WeakDimension.lean, Ring.WeakDimensionLEOne.pi_of_isValuationRing (line 110) proves a product version for finitely generated flat ideals, and Ring.WeakDimensionLEOne.of_weaklyEtale (line 357) proves ascent in that formulation. Neither states the item or the new equivalence, so neither is an attachment. No Lean file was written or compiled.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## Errors and discrepancies

The item statement is correct and was preserved verbatim. Its injected/local assertion needs an argument in addition to the weak-dimension paragraph of 0ASJ; step 2 supplies it through the existing general flat-localization lemma. No henselian, rank, Noetherian or module-finiteness hypothesis has been added. The later weakly-unramified conclusion of 0ASJ is not part of the item.

The item's inherited blueprint ancestry records the older nearby-cycle/Temkin supporting branch. I read the latest chapter, unit, locality statement and locality proof under literature/blueprint/latest/. That locality proof now quotes the contracting-correspondence theorem directly. This delivery keeps the assigned algebraic item and inherited ancestry, and does not edit an ancestor, a unit or a chapter. The new criterion identifies precisely the 092S input used in the assigned 0ASJ branch. No alternative route above the item is asserted.

During searching I once passed the proposed new-node id rather than the assigned item id as the msearch item argument. I corrected the argument and reran those searches under the assigned item. Every search recorded in either delivered node is present in this item's searches.jsonl; no search result is invented and no launcher script was modified.

## Unfinished work

The general 092S criterion is intentionally left statement-only for the next stage-1 item. Its proof is the equivalence (1) and (5) in the cited source, with the length-one resolution made explicit in the source's (4) implies (1) paragraph. This is the sole new mathematical obligation. The assigned item's proof is complete relative to its cited statements.

## Not duplicates

lem-trf-weak-dimension-one-valuation-criterion vs lem-weil-pbc-weak-etale-tor: the new statement characterizes a ring's flat-resolution bound by its valuation local rings; the existing node transports bounds between two rings and compares Tor. It contains no valuation-ring characterization.

lem-trf-weak-dimension-one-valuation-criterion vs lem-sfb-semihereditary-topological-coefficients-admissible: the existing node assumes projectivity of finitely generated ideals and concludes coherence, finite projective resolutions of finitely presented modules, and flatness of continuous-function algebras. It neither asserts a length-one bound for every module nor a valuation-local-ring equivalence.

lem-trf-weak-dimension-one-valuation-criterion vs lem-dl-a1-ind-etale-domain-generic-field: that node identifies the generic fibre and separable fraction-field extension for an injective ind-etale map of domains. It does not characterize weak dimension or valuation localizations.

lem-trf-weak-dimension-one-valuation-criterion vs lem-trf-etale-localization-valuation-domain: the new statement concerns an arbitrary ring and its flat resolutions, without an etale algebra, a base valuation ring, or a prime over a prescribed closed point. The item still has to establish the bound on A, transport it to B and establish injectivity and locality. The new node restates none of the item's clauses.

I searched the whole DAG for 092S, 092D, 092E, lemma-weak-dimension, weak dimension, and flat resolution lengths, and read the relevant statements. tools/blueprint_refs.py searches for weak dimension, valuation domain, 092S, 092E, flat resolution, and valuation plus flat found no blueprint node giving the new equivalence. I also searched the newest blueprint text; its weak-etale Tor node mentions finitely generated ideals and ascent, not the characterization. The source-tag search found no existing node whose source is the new 092S criterion.

## Review by Q91

I read Stacks more-algebra.tex, Tag 0ASJ (lemma-etale-extension-valuation-ring), its statement and first proof paragraph. The source first applies 092S to the valuation base, then 092N and 092E to the etale algebra, and finally 092S to its local ring. This is exactly the proof route here. I read Tag 092N (lemma-when-weakly-etale), Tag 092E (lemma-weak-dimension-goes-up), and the full statement/proof of Tag 092S (lemma-weak-dimension-at-most-1), including (4) implies (1) and the local-ring argument. Tag 092D defines weak dimension via Tor dimension; the short exact flat resolution in the new node is explicitly the resolution the 092S proof constructs. Thus the node records a resolution statement with actual modules and maps, not an undefined reference to a numbered condition.

For step 1 I opened det-pe-morphisms-etale-comparison and read its statement. Its clause (1) applies to the given morphism of schemes, and clause (4) applies to the whole affine charts Spec B and Spec A, giving both required flat maps. I opened def-weil-pbc-ind-etale-algebra: its final equivalence defines weak etaleness as exactly those two flatness conditions. I deliberately did not use lem-trf-etale-ring-map-weakly-etale, whose statement starts with an infinitesimal lifting hypothesis that is not directly the scheme hypothesis of this item. Both cited statements give exactly what step 1 uses.

For step 2 I opened lem-trf-flat-localized-field-descent. Its source ring and target ring are arbitrary commutative rings; it assumes flatness, a maximal base prime and a source prime with that contraction. Step 1 gives flatness, the specified maximal ideal of A supplies the base prime, and the item's hypothesis gives the contraction. Its statement explicitly gives an injective, local map between the two localizations. I read def-weil-pbc-localization-at-prime to check the fraction formula and the target maximal ideal. The inverse of A to its localization at its maximal ideal is written out as a/s mapped to a times the unit inverse of s. Consequently the supplied natural map is this composite. The contraction equality is also spelled out, so there is no implicit switch between an unspecified local embedding and the natural homomorphism.

For step 3 the new criterion's local specialization takes the given valuation domain A, which is nonzero and local, and supplies a length-one flat resolution for every A-module. I read the entire statement of lem-weil-pbc-weak-etale-tor: its last sentence transports a common bound on flat-resolution lengths for all A-modules to all B-modules under weak etaleness. This uses its statement, not a construction hidden in its proof. Step 1 provides exactly its ring-map hypothesis. I declare both this node and the affine comparison as generic off-unit tools in split_report.tool_uses; no unit proof is replaced.

For step 4 the new criterion is applied to the commutative ring B and its supplied prime q. Its condition (ii) explicitly says B_q is a valuation domain. B itself need not be a domain or local, so this criterion is deliberately stated for arbitrary commutative rings; applying a domain-only criterion here would be an error. The injectivity and localness conclusions are already independently proved in step 2.

I tested the item when A is a field: an etale B has finite separable field factors, and localization at a prime picks a field; products are allowed and B need not be a domain. B=A gives the identity assertion; the zero algebra has no q and is excluded by that hypothesis. Arbitrary-rank and nonhenselian valuation rings are allowed throughout. For the new criterion, a field and a finite product of fields satisfy both sides; a product demonstrates why R must not be assumed a domain. The zero ring satisfies (i) and has no primes, so (ii) is vacuous; the local specialization explicitly requires nonzero. Z/4 fails both sides, and a nonvaluation local domain cannot pass the stated equivalence merely by having Krull dimension one. No bound is imposed on Krull dimension.

I inspected the Mathlib hits: ValuationRing.TFAE and iff_local_bezout_domain require an existing domain and characterize the Bezout condition, while Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal (Flat/TorsionFree.lean:125, read with lines 90--141) assumes a domain and valuation localizations and concludes a torsion criterion. The localized-flatness and finite-flat-local-free hits are ingredients, not the new equivalence. DVR hits add Noetherian/rank assumptions. A second semantic phrasing searched flat resolution lengths, and source grep found no weak-dimension or flat-resolution characterization in Mathlib. All recorded queries are actual logged queries, and all used services answered successfully.

Against delivery-errors B--E: the new lemma is self-contained and statement-only, defines its resolution maps and local-ring condition, and cites the existing notions of flatness, prime localization and valuation domain. It has single-escaped TeX, the verified Stacks tag and label, full blueprint ancestry, and real search records. It is a general input rather than a clause of the item. Every non-elementary use has a node, and the seven citations quote statements verbatim. No argument is hidden in a long elementary step: all four steps are conservatively non-elementary and below 2000 characters. The source hypotheses, contraction ideal, flatness direction and natural map were checked as described above. No statement dispute, source error or new hollow definition was found.
