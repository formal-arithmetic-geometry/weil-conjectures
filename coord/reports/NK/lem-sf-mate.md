# Worker report: lem-sf-mate

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-mate.json: existing statement, now a Mathlib leaf. Mathematical content and statement dependencies unchanged; the context opening is expanded into explicit coefficient and scheme parameters, and a clausewise match covers the complete item.
- citations.json: [], since a Mathlib leaf has no proof steps and no step citations.
- report.md: this report. The required search command wrote searches.jsonl.

New nodes: 0. Mathlib leaves delivered: 1 (the item).

## Attachments

None. I read slopmaster2 WeilConjectures/SixFunctors/Etale/Derived/Adjunctions.lean:243-273, particularly AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.exists_rightDerivedLowerShriekAdjunction_comp_eq at line 253, and the related declarations in Etale/Derived/Composition.lean:104,144. They contain no local sorry, but assume finite coefficient rings, while this item also quantifies over integral and rational stages of def-sf-datum. The pro-etale UpperShriekComposition.lean finite-Tor result likewise assumes finite coefficients. These are not exact attachments. The project general conjugation-transport theorem in WeilConjectures/Mathlib/CategoryTheory/Adjunction/Mates.lean confirms the formal argument, but Mathlib already suffices; no project theorem is attached and no transitive sorry claim is made.

## Sources

WANTED: literature/blueprint/master/blueprint/sec-smooth-purity/sk-lem-sf-mate/lem-sf-mate.md, original imported statement and proof, for lem-sf-mate. The blueprint directory is absent from the read-only shared checkout. I read the imported node, chapter, and full unit record and verified the leaf against pinned Mathlib itself; no download was made.

For this item I read Mathlib CategoryTheory/Adjunction/Basic.lean:561-587 and CategoryTheory/Adjunction/Mates.lean:258-435, including parameters, conjugation, unit/counit compatibility, preservation of inverses and conjugateIsoEquiv. The composition construction is explicitly tagged Stacks 0DV0 at Basic.lean:566. No new Stacks-dependent node is created. The Mathlib source is the proof source of this leaf, rather than an agent-written replacement for missing literature.

## What changed and what was wrong

The old proof only referenced fix-prop-adjunctions. Its complete conditional formal content already belongs to Mathlib. The item assumes the three adjunctions and the left composition isomorphism; it does not establish exceptional-adjoint existence or preservation.

The unit sk-lem-sf-mate is broader: it also has optional ambient and unconditional constructible forms, with transport from the etale site. I did not replace the item's explicitly conditional restricted-ambient statement by that unconditional statement or claim that this one node realizes the entire unit. I therefore did not fill the unit realization fields with that false claim. There is no statement dispute: the conditional statement is true.

The search wrapper misparses single-file rg results, labeling line numbers as filenames. I repeated both searches over the directory with anchored patterns, obtaining actual files and lines for all six declarations. Both the malformed wrapper output and the successful repeat are recorded honestly.

## Explicit clausewise match

Write $F=Rf_!$, $G=Rg_!$, $H=R(gf)_!$, $U=Rf^!$, $V=Rg^!$, $W=R(gf)^!$, with given adjunctions $a_f:F\dashv U$, $a_g:G\dashv V$, $a_h:H\dashv W$. Use ordinary mathematical composition and the given $e:H\xrightarrow{\sim}GF$ (inverse to $\alpha_{g,f}$ in thm-sf-comp-composition).

1. Adjunction.comp (Basic.lean:567) gives $GF\dashv UV$. Its unit is $U(\eta_g)F\circ\eta_f$ (comp_unit_app, line 575); its counit is $\varepsilon_g\circ G(\varepsilon_f)V$ (comp_counit_app, line 580). These type-check at objects of the assumed finite-Tor categories.
2. conjugateIsoEquiv (Mates.lean:425), with first adjunction $a_f.comp\,a_g$, second $a_h$, and input $e$, gives $\theta:UV\xrightarrow{\sim}W$. Its inverse is the required $W\xrightarrow{\sim}UV$. This is one-line specialization with the composite adjunction as a parameter.
3. unit_conjugateEquiv (Mates.lean:300), applied to $e.hom$, states $\theta_{GFK}\circ\eta_{\mathrm{paste},K}=W(e_K)\circ\eta_{h,K}$. conjugateEquiv_counit (line 285) states $\varepsilon_{h,L}\circ H(\theta_L)=\varepsilon_{\mathrm{paste},L}\circ e_{UVL}$. These identify both units and counits; their reverse readings use the given inverses of $e$ and $\theta$.

These numbered entries explain the clausewise Mathlib leaf; they are not DAG proof steps. Its proof is empty. The match names a declaration, file and line for every clause. No claim about existence of a concrete geometric right adjoint, constructibility, or change of coefficient category is required to instantiate these categorical declarations.

## Searches and reuse

Every Mathlib search recorded in the node was run with msearch.py NK lem-sf-mate; exact tool/query pairs came from its log. LeanSearch returned HTTP 500, recorded unavailable. Two LeanFinder phrasings returned composition and conjugation results. Loogle returned conjugateIsoEquiv. Directory-scope grep returned all six exact source locations, which I opened.

A whole-DAG statement/title search found lem-cat-right-adjoint-composition, def-weil-pbc-composite-adjunction and lem-weil-pbc-mate-pasting. I opened their statements: literal-composite right-adjoint uniqueness, the composite's pasted formulas, and square pasting respectively. No duplicate helper is created. Blueprint searches for conjugateIsoEquiv, pasted adjunction, and Mates along an isomorphism found respectively none, this item, and lem-trf-adjoint-mate. That last node gives an abstract two-adjunction comparison with additional exact-triangulated hypotheses and uniqueness assertions, rather than another copy of this geometric conditional statement. No exactly duplicate blueprint item is recorded in same_as, and no off-unit proof tool is used.

## Not duplicates

No new nodes; no new/existing Stacks-tag pairs.

## Review by NK

I checked the mathematical statement against def-sf-datum, def-weil-exceptional-adjoint-admissibility, thm-sf-comp-composition, and fix-prop-adjunctions, reading their actual statements. The first permits four coefficient stages; the second distinguishes optional ambient data from unconditional constructible exceptional adjoints. Our finite-Tor adjunctions are hypotheses. No preservation result, ambient existence claim for all morphisms, or finite-coefficient instance is imported into the argument. The left comparison is given by hypothesis and axiom A4 of the supplied datum.

For clause 1 I read Adjunction.comp and both component formulas, rather than treating a definition as a theorem. For clause 2 I checked the reversal of direction: H to GF yields UV to W, and the item uses its inverse. For the last clauses I read and substituted both compatibility identities with the same adjunctions and e.hom, writing their component formulas above. This establishes the two compatibilities in addition to existence of an isomorphism. All categories are arbitrary Mathlib category parameters, so integral/rational stages need no new theorem. There are no proof-step citations: the C4 quote audit is empty and citations.json records this accurately.

For edge cases I checked identity functors with identity adjunctions (all formulas are identities), identity functors with nontrivial adjunction choices (the formulas retain the actual units and counits), empty categories (componentwise statements are vacuous), and noninvertible transformations (conjugation only guarantees a transformation, so the explicitly assumed isomorphism is essential). Mathlib conjugateIsoEquiv constructs both inverse maps; no unjustified assertion that mates of arbitrary square isomorphisms are invertible is used.

Against delivery-errors B--E: no new node with a proof sketch, missing object, or unverified hypothesis; no changed mathematical claim or unmarked weakening; no non-elementary fact hidden behind an elementary marker; no use of a cited node's proof rather than its statement; no new relabelled clause or duplicate. I replaced the reference-only proof by the full checked Mathlib match. I wrote no Lean and ran no compiler, Lake or build. The final required dry run checks the delivery form; this pass does not push.

## Dry-run repair

The first required dry run failed only B2: the opening phrase “In the setting of” did not introduce the objects. I expanded it using the existing def-sf-datum parameters: distinct primes p and ell, a p-power q, k, E, its valuation ring and uniformizer, n, the four coefficient stages, and finite-type k-schemes X,Y,Z. These are the inherited hypotheses, not additional restrictions. The adjunction and composition clauses and statement-dependency list remain the same. The report's earlier discussion of the mathematical statement refers to this identical conditional claim. This was a presentation correction, not a statement dispute or weakening.

## Unfinished work

No clause of this conditional item remains unmatched. The unit's broader assertions are separate. The independent second reader must review the leaf classification and deliver.

## Second reading by NK

- Item statement: checked the explicit coefficient, scheme, morphism, adjunction, finite-Tor, mate, and pasted-unit/counit clauses against the imported node and the blueprint source; verdict: pass, with no added or dropped hypothesis.
- Mathlib leaf match: checked `Adjunction.comp`, `comp_unit_app`, `comp_counit_app`, `conjugateIsoEquiv`, `unit_conjugateEquiv`, and `conjugateEquiv_counit` in the Mathlib source at the recorded lines; verdict: pass, and the inverse orientation gives $(gf)^!\cong f^!g^!$.
- Proof steps: the delivered item has no proof steps because its complete formal content is recorded as a Mathlib leaf; verdict: pass, with no uncited step or hidden geometric assertion.
- New nodes: none; there are no new-node statements or nodes requiring B1--B7 review.
- Edge cases: rechecked identity functors and identity adjunctions, empty categories, and the necessity of the assumed left-adjoint isomorphism; verdict: pass.
- Changes made in this second reading: appended this audit only; the statement, Mathlib declaration list, search log, and citations remain unchanged.
