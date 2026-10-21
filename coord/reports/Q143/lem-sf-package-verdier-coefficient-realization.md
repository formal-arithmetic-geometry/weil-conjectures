# Q143: lem-sf-package-verdier-coefficient-realization

## Files written

- `dag/nodes/sec-six-functors/lem-sf-package-verdier-coefficient-realization.json`: statement, split; unchanged statement; seven proof steps; no Mathlib match.
- `citations.json`: one entry for every step/node citation, quoting the part of the existing node's statement used.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. The only node file delivered is the assigned item. `searches.jsonl` contains the actual search-command records; `write_split.py` is sandbox-only scratch work.

## Attachments

None. Searched `lean/WeilConjectures/` for the item id, Verdier/biduality, and the exchange declarations. Read `SixFunctors/Etale/Derived/TensorHom.lean` around lines 390--431 and `Package.lean`, including the explicit list of coefficient/naturality clauses omitted from that finite-ring package. `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek` supplies finite étale objectwise exchange, not the entire item with the higher coefficient categories and specified evaluation, boundary, and coefficient comparisons. It is therefore not an attachment for this item.

## WANTED

None. All source texts needed for this one-level assembly are present. The proof is marked agent-origin because the immediate source is the agent-written blueprint, not because of an unavailable document.

## Problems found and changes made

The item was unsplit, with no proof or proof dependencies. Its mathematical statement is retained verbatim, including finite-Tor inputs at finite coefficients, the full derived-complete bounded constructible category at integral coefficients, and rationalized/common-stage field categories.

The source paragraph names `fix-cor-verdier-exchange`, but the current DAG statement of that older theorem assumes exceptional admissibility for f and the structure morphisms. This is a stronger hypothesis than the item has, so simply citing it would violate C4/E1. The blueprint's current unit `sk-thm-sf-verdier-exchange` gives exactly the unconditional constructible theorem, explicitly excluding ambient admissibility and specifying higher-stage comparisons. It is already on the package unit's route. I used that existing node, whose statement and proof I opened, rather than extending the older conditional theorem or introducing a duplicate. This changes the reference used in the assembly, not the statement or the unit's tensor--Hom/mate route.

The original item already specified the appropriate integral and field domains, so no STATEMENT-DISPUTED repair was needed. I did not silently replace finite-Tor by bounded constructible at a finite ring stage. The dualizing object in the integral duality theorem is identified with the exceptional value at the unit by the existing `prop-coef-integral-dualizing`; the rational identification with actual internal Hom and exceptional operations is explicitly supplied by `lem-coef-rational-operations`.

## Unfinished work

None for the one-level split. The existing cited nodes retain their own proof obligations and metadata; no claim is made that their upstream Lean implementations prove all these clauses.

## Not duplicates

No new nodes were created. Whole-DAG and blueprint searches for Verdier exchange, integral Verdier, and biduality located the finite geometric, boundary, and coefficient-passage theorems already in the graph. I reused those instead of creating nodes that restate the item's clauses. I also inspected the canonical-exchange datum and finite-Tor definition for the normalization and domain checks. No new elementary facts, new definitions, or replacement umbrella lemma were introduced.

## Mathlib searches

Ran all searches through the required msearch.py command under Q143 and this item, and read each returned hit. The two LeanFinder phrasings asked first for constructible finite/adic duality and then for internal Hom exchanging compact-support and ordinary direct image. The results were ordinary sheaf/condensed adjunctions and pushforward-composition facts, not constructible Verdier duality. LeanSearch returned linear-module dual base change, linear perfect pairings, sheaf pullback conjugation, and opposite complexes. Loogle's `CategoryTheory.Equivalence.op` only turns a given equivalence into one on opposite categories; it does not construct geometric duality or its maps. The Mathlib grep for `verdierDual|dualizingComplex|biduality` returned no hits. These are no-match searches, with their exact queries and returned summaries appended to the item's existing searches and logged in searches.jsonl. No service was unavailable in these searches.

## Review by Q143

I read the worker brief, stage-1 contract, SETUP's three blueprint levels, GOAL, the package chapter/unit records, and delivery-errors B--E. The source for the item is the current `main-20261015/.../sk-thm-sf-package/prop-functor-package.proof.md`, specifically its paragraph beginning “For (7)” and its integral/field anti-equivalence sentence. I followed that assembly, with the unconditional exchange replacement explained above. I also read the current finite-biduality and boundary-discharge statement/proof files in `sec-smooth-purity/sk-lem-sp-tower`, the integral and rational statement/proof files there, and the qbar statement/proof and rational-operation statement files in `sec-six-functors/sk-thm-sf-package`. The current files have moved relative to some older node source paths; the proof steps give their actual main-20261015 paths. There are no new nodes whose sources need separate review.

For step 1 I read the complete statements of `thm-fix-general-biduality` and `lem-weil-duality-pairing`. The first applies on the small pro-étale site with exactly a separated finite-type scheme over the given algebraic closure and A_n. It gives exact anti-equivalence and invertibility of the natural delta without boundary input. The second specifies that delta is the transpose of evaluation, including its formal pro-étale construction once the dualizing object is supplied. The item uses that very dualizing object. Tensor symmetry only accounts for the order of the two factors in evaluation.

For step 2 I read `cor-weil-boundary-duality-discharge` and `def-weil-boundary-duality-input`. The corollary covers every locally closed piece and every closed immersion in the definition, with all finite stages quantified. Its conclusion is the canonical evaluation-defined beta, not an objectwise existence claim. The definition gives its exact pairing, and the corollary discharges the input as a consequence rather than requiring it as a hypothesis. Thus there is no circular invocation of boundary exchange to establish the biduality used in step 1.

For step 3 I read `prop-coef-integral-dualizing` and `thm-coef-integral-verdier` in full. The former is a value-at-the-unit assertion on the same completed coefficient sheaf, sufficient for identifying omega; it does not require an ambient exceptional adjoint for all pro-étale complexes. The latter states equality of the full bounded constructible and uniform finite-Tor domains, exact anti-equivalence, the canonical reduction maps, reconstruction, the dimension-dependent interval, evaluation compatibility and reduction of the actual delta. Every one of those clauses is present in its statement, and the step cites both nodes. The hypothesis dim T <= d is used only in the explicitly conditional interval assertion, for every such nonnegative bound d.

For step 4 I read `thm-coef-rational-verdier` and `lem-coef-rational-operations`. The theorem concerns the given raw rationalized category and gives the actual rationalized evaluations/deltas, as well as coherent finite-extension comparisons. The lemma identifies the resulting dual with internal Hom into the exceptional value at E and says that evaluations are preserved. Thus an abstract rationalized equivalence is not silently substituted for the functor in the item.

For step 5 I read `thm-coef-qbar-verdier`. Its statement includes the common-stage functor, its identification with internal Hom into Ra_T^! qbar, the descended evaluation and biduality maps, and compatibility with retracts. I use its statement, not the common-field construction hidden in its proof. Its separated finite-type and coefficient hypotheses are identical to the item's. This is finite coefficient-field passage, not an infinite topological tensor extension.

For step 6 I read `def-weil-finite-tor-amplitude`. The field equalities with bounded constructible categories are explicitly definitions there. At R the equality is the theorem used in step 3, and at A_n finite-Tor remains an assumption. This elementary domain check ensures that the exchange theorem is applied to every input allowed by the item and only on its asserted domain.

For step 7 I read the complete current statement and proof of `sk-thm-sf-verdier-exchange` and the statement of `def-sf-verdier-exchange-data`. The theorem states natural canonical exchange at all four coefficient stages, identifies Rf^! omega_Y with omega_X, retains the completed/rationalized/common-stage conventions, and supplies coefficient and shift compatibility. The datum specifies the evaluation/projection transpose normalization of that canonical arrow. The theorem's proof constructs it by inverse tensor--Hom exchange followed by substitution of the composition mate. Thus the map used here is the evaluation-defined arrow; no invertibility claim is taken from a definition alone. All scheme, morphism and input-category hypotheses have been checked in the earlier steps.

I checked B--E against the delivered JSON and these open statements: no new unsplit node hides a proof, no tag stands in place of an uncited result, no extra hypothesis is used, and no clause has been moved into a newly created node. All citations have exact statement substrings in citations.json. The proof dependency list is exactly the union of uses. A read-only dependency traversal found no path from any cited theorem back to this item. Every step is below 2,000 characters, and each is a theorem application or the explicit elementary domain check; none hides an additional comparison lemma. All statements used are existing nodes on the package route (definitions need no route exception); no off-route tool use is requested.

I tested the scope on the empty scheme and zero complex (all conclusions reduce to zero-category identities), on T = Spec k and f = identity (ordinary perfect coefficient duality and canonical identity exchange), and at n = 1 (field coefficients). At n > 1, a nonperfect residue module over R/(varpi^n) is excluded by the finite-Tor hypothesis; integral R/varpi remains an allowed integral object with compatible derived reductions, not a falsely assumed flat reduction. These checks support retaining the original statement without adding hypotheses or dropping clauses.
