# Stage-1 report: lem-pur-twist-cancellation

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-twist-cancellation.json`: statement, split; six proof steps; no Mathlib match for the full statement.
- `citations.json`: five verbatim node-statement excerpts for all citations in the six steps.
- `report.md`: this report. `searches.jsonl` is the search command's unchanged log.

New nodes: 0. New Mathlib leaves: 0. No unit record was changed: this item realizes part of the already bound key node, rather than being the key node itself.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact item id, twist cancellation, co-projection, dualizing twist, and regular-immersion purity; also searched the exact id in Comparator. There is no declaration with this item's tag. Read `EtaleCohomology/Purity/Smooth/RegularImmersion.lean`: `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_of_isRegularImmersion`, lines 350 ff., is a `sorry` theorem under regularity and smoothness hypotheses, and asserts only existence, not this specified-input composite. It is not an attachment. Read the twist co-projection declaration in `Smooth/Coprojection.lean`, lines 245 ff.: it supplies a related ingredient, not the item and not the pro-etale constructible statement in its entirety. The exact upstream master is reference material only; no completion is inferred from its declarations.

## WANTED

None. The proof is an agent-written expansion of the current blueprint's formal calculation, so `proof_origin.by` is `agent`. No external purity theorem or SGA source is used.

## Findings and changes

The statement was correct and was retained byte-for-byte. Its title mentions a regular immersion, but the text deliberately takes the three orientation isomorphisms as data and does not assume regularity. That is sufficient for this formal lemma and is not a statement dispute. The inherited node had no proof. The split now writes down the exact three initial arrows, the inverse co-projection that supplies the last arrow, the cancellation giving the untwisted result, and the cohomology calculation.

The statement dependency `sk-def-sp-tate-twist` was made explicit for the meaning of all signed Tate twists. The other three statement dependencies remain: the coefficient convention, the exceptional functor, and the specified co-projection. No new geometric, normalization, finite-Tor hypothesis on the arbitrary orientation inputs, or scalar-coefficient comparison was added. Co-projection is applied only to Tate shifts or the coefficient unit, whose finite-Tor property is established before the applications.

## Blueprint, DAG, and Mathlib searches

Read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-thm-regular.json`, and the current main-20261015 `sk-thm-regular/_section.md` and `sk-thm-regular.proof.md`. The current proof's Step 2 is the route followed; the unit record retains older affine-space references in later steps, which this item never uses or changes. The blueprint ancestry command returns `sk-thm-regular`, consistent with the existing `from` record.

Searched the whole imported blueprint for twist and cancellation, and the DAG for signed-twist, additivity, invertibility and pullback statements. Reused `det-def-sp-tate-twist-locally-free`, `sk-def-sp-tate-twist`, `det-prop-sfb-cartesian-coefficients-twists`, and `lem-pur-coprojection`; none states the full specified composite. `sk-thm-regular` is the parent theorem with stronger geometric content, not a smaller result to cite here. No blueprint node states this formal supplied-input lemma exactly, so `same_as` remains empty. Read each reused statement, including the current corrected finite-coefficient restriction of co-projection. Checked that none has a dependency path back to this item.

Retained the item's inherited searches and read their recorded results. Ran six additional searches, recorded exactly in the item and in the command log: LeanFinder with two phrasings, Loogle for `CategoryTheory.TwistShiftData`, LeanSearch for invertible tensor and exceptional inverse image, and two Mathlib grep queries. All services returned results; none was marked unavailable. The results give generic monoidal inverse identities, module cancellation and cohomological-shift data. Read `Mathlib/CategoryTheory/Shift/Twist.lean`: its `TwistShiftData` changes the associativity of a shift action and does not construct Tate sheaves or an exceptional inverse image. Read the monoidal-category source for the generic tensor operations. These facts cannot specialize in one line to the item's sheaf-theoretic construction without the existing DAG ingredients, so the item is not a Mathlib leaf. The broad grep's matches such as “state” and “rotate” are irrelevant; the second targeted query finds coproduct coprojections, not exceptional inverse images.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. Signed tensor additivity, shift cancellation, functorial preservation of inverses and the degree-zero calculation remain explicit proof steps rather than being promoted to nodes.

## Review by Q93

I read the current main-20261015 regular-immersion proof, especially its entire Step 2, against the supplied-data statement. I also read the blueprint source files for the three reused theorem/definition ingredients: `sk-prop-an/sk-def-sp-tate-twist-locally-free.md`, `sk-prop-an/sk-prop-sfb-cartesian-coefficients-twists.md`, and `sk-proetale-coefficients/sk-def-sp-tate-twist/_section.md` (in its actual `sec-proetale-coefficients` location); and the older `sk-lem-coprojection/lem-pur-coprojection.md`. The DAG statements, not the older source's broader informal hypotheses, are the interfaces used. No new node needs an additional source.

Step 1 cites the finite Tate-line invertibility and inverse-twist functors stated in `det-def-sp-tate-twist-locally-free`, and the signed tensor-power/dual definitions stated in `sk-def-sp-tate-twist`. Both say what the argument takes. I wrote out the local generator formula and its change-of-basis check for all integer exponents, then the shift arithmetic. Local tensoring by a rank-one free module is exact and locally the identity, so the bounded constructible and finite-Tor typings used later follow directly. This is a short calculation from the cited statements, not an unstated independent purity lemma.

Step 2 cites `det-prop-sfb-cartesian-coefficients-twists`, whose statement explicitly gives inverse images of every signed twist with the coefficient-module structures. The finite coefficient ring is admissible and the prime is invertible on both schemes. Because the line is flat and the coefficient pullback is identified, the sheaf identification gives the stated derived identification, and shifts simply carry along. The node is not merely a definition of pullback.

Step 3 uses only the supplied isomorphisms and the identity that applying a functor to a map and its inverse again gives mutually inverse maps. I checked the direction: start with Pi_Z inverse after the negative m shift, then b, then Ri! Pi_X, all with that same negative m shift. Its target has N still inside Ri!, exactly as required.

Step 4 cites `lem-pur-coprojection`, whose displayed formula is copied verbatim into citations.json. Here its K is T_X(N), not an arbitrary object being assumed perfect; its L is T_X(-m). Step 1 makes L invertible in the finite-Tor category and K bounded constructible. Step 2 identifies its derived restriction. Taking the inverse co-projection gives precisely the statement's last arrow, then signed additivity gives N-m=c. Thus this proves the actual chosen composite is invertible, not just that its source and target happen to be isomorphic.

Step 5 cites the same co-projection statement at K=Lambda_X and L=T_X(c). Both meet the same hypotheses. I checked the direction of the final isomorphism by inverting C composed with Phi before tensoring by T_Z(-c); its source then cancels to Ri! Lambda_X and its target becomes Lambda_Z(-c)[-2c]. Step 6 applies the definition of cohomology of a complex concentrated in degree zero and preservation of inverses by the cohomology functor. It gives vanishing in every nonzero degree as well as the degree-zero identification, with no claim about a distinguished generator or frame normalization.

I checked B--E of delivery-errors point by point: there are no new-node form or duplication issues; each non-elementary ingredient is an existing cited statement and every citation has its exact excerpt; no parent theorem, definition-only substitute, or source proof is used as a theorem; all co-projection hypotheses have been verified; the proof is an actual calculation rather than a new node restating the conclusion; no cycle is introduced. There are no steps longer than 2000 characters (the longest is 980), and no hidden comparison lemma or omitted standard argument.

Small cases: with c=0 and N=m, the final cancellation is the unit twist and the untwisted conclusion has no shift. With m=0 and N=c, the initial negative-m functor is the identity and the last arrow is unit co-projection. For N=3, m=1, c=2, the final untwisted shift is -4 and twist -2, confirming both signs. Empty schemes give zero coefficient objects and the argument still applies. For c=0, i the identity and b multiplication by any coefficient unit, the composite changes by that unit; hence it would be false to assert a normalized fundamental class for arbitrary inputs, and this split correctly asserts only the statement's invertibility. Ramified E and n=1 introduce no extra freeness or divisibility assumption: the argument uses only the invertible finite Tate line. No smoothness or regularity is used surreptitiously.

## Unfinished work

None within the requested one-level split. All remaining non-elementary work is already represented by existing DAG nodes. No Lean was written or compiled, and no live project file was changed.
