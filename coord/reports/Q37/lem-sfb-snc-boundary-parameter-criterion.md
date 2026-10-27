## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-snc-boundary-parameter-criterion.json`: existing statement, split into nine steps, with 18 existing proof dependencies and no new nodes. No Mathlib match for the whole equivalence.
- `citations.json`: 29 entries, one for each step/node citation, containing verbatim statements of the cited nodes.
- `searches.jsonl`: actual Q37 msearch records, retained with their results.
- `report.md`: this report.

## Attachments

None. Searches in `lean/WeilConjectures/` for the blueprint tag, strict-normal-crossings names, and boundary/parameter terminology found no declaration stating this equivalence. The codimension-two regular-boundary docstring is about a different result. No Lean files were written and no compiler, Lake, or build tool was run.

## WANTED

None. Stacks and the ILO volume used here are locally available.

## Audit of the imported item

The statement is correct, including its use of ordinary local rings rather than strict henselizations. I kept it unchanged. Its source is Stacks 0BI9 (`definition-strict-normal-crossings`) and 0BIA (`lemma-strict-normal-crossings`) in `etale.tex`, checked against ILO VIII Remark 4.2.2(i), printed pp.118–119 (PDF pp.124–125). I also read Stacks 00NR and 00NQ in `algebra.tex`, 0AG0 in `more-algebra.tex`, and 0AG8 (`lemma-effective-Cartier-in-points`) in `divisors.tex`. These account respectively for regular quotient kernels, parameter quotients, prime parameters, and spreading a stalk equation. There was no imported proof to retain: the item was unsplit with an empty proof.

The chapter and unit records were read, as were the current main-20261015 direct-images proof and the parent's final-boundary use. This remains a local geometry tool in the alteration reduction; it changes no chapter or unit route. The inherited `blueprint.from.node` is null, and `blueprint_refs.py ancestor` reports that historical broken provenance chain. Its existing detailed `from.place` identifies `det-thm-sf-ctf-stability-direct-images`, proof (3), and the final-boundary clause of the parent; I retained that provenance and searched the whole blueprint for strict normal crossings and parameters. No equivalent blueprint statement was found. No unit realization record is changed: this auxiliary node is not the unit's key theorem.

## Mathlib and reuse

I searched the whole DAG before deciding that no new supporting lemma was necessary. In particular, I reused the existing 00NR, 00NQ, 0AG0, 00E3, 00CT, 00ES, 01J3 and finite-component nodes. The item was searched using msearch with LeanFinder, Loogle, LeanSearch and Mathlib grep, with a second semantic phrasing and a second grep in RingTheory. All searches that completed returned successfully; the search records are appended to the item's prior search history without rewriting that history. The results include Weierstrass preparation, reduced/integral scheme properties, and localization of regular sequences. The RingTheory grep also locates the definition of a regular local ring and a polynomial-localization regularity lemma. None states the entire boundary/parameter equivalence or gives a one-line specialization of it.

## Not duplicates

No new nodes. The existing scheme-theoretic component identification theorem for an etale chart assumes the boundary components are already regular, so it cannot be used to prove their regularity in this item. Instead step 8 uses the existing general minimal-prime and localization statements without this circular hypothesis. I also did not create a duplicate of the regular quotient theorem or a node merely restating either direction of the item.

## Review by Q37

I read the item's cited Stacks definition and both directions of the proof of 0BIA, and the actual boundary definition node. The latter asks for a pointwise dimension equality and includes the empty index subset; I prove that precise equality, rather than silently substituting a global codimension convention. The ambient scheme is regular everywhere by hypothesis, so the off-boundary condition and the empty-index intersection introduce no additional hypothesis.

For step 1 I opened the closed-immersion definition and the quotient-localization and reduced-induced-closed-subscheme nodes. The first gives the affine quotient description, the second the local quotient ring, and the third the unique radical ideal with a prescribed closed support. I wrote the sum-of-ideals universal-property check and the finite-denominator check for localizing intersections, so the proof does not cite a definition for an unproved identification.

For step 2 I opened the regular-quotient-kernel-parameters node and the regular-local-generators-regular-sequence node. The boundary's singleton condition gives a proper ideal with regular quotient of dimension d-1. The first cited theorem makes its ideal a parameter ideal, and the second forces its length to be one. All needed regularity and Noetherian hypotheses are present. I did not take simultaneous equations from separately chosen parameter systems. In step 3 I instead used the full intersection's regular local ring of dimension d-r, as stated in the boundary definition, lifted d-r generators, and explicitly checked that the resulting d elements generate the ambient maximal ideal. That is elementary from the regular-system definition and does not conceal an application of Nakayama.

For step 4 I read the UFD-boundary-factorization node, the permutable parameter-quotient theorem and the closed-immersion-ideal-stalk-range node. Their statements give parameter primality in a domain, the nonzero image of one parameter modulo another, and the unit ideal off the closed subscheme. I wrote the divisibility argument giving intersection equals product, applying reduced-union calculus only because H and the C_i are reduced. Step 5 uses exactly the same algebra in the other direction and the reduced-scheme definition, whose statement really does characterize reducedness on local rings. Thus no global assertion of reducedness is inferred from mere support equality.

For step 6 I read Stacks 0AG8 in full and wrote its finite-generation proof in the item. Both the defining ideal and its annihilator are finitely generated because the affine ring is Noetherian. The localization definition supplies the fraction equality and vanishing rules, and the effective-Cartier-ideal definition is used only after an actual neighborhood and a nonzerodivisor generator have been produced. This is a routine finite-denominator argument, not a separate hypothesis-bearing auxiliary theorem. It is marked elementary and does not merely assert that stalkwise principal ideals are locally principal.

For step 7 I opened the Noetherian-closed-subset-finite-components node, the reduced-induced-structure theorem and the integral-scheme definition. They give exactly a finite family, its actual closed scheme structures, and integrality from nonempty reduced irreducible support. For step 8 I opened the Spec/minimal-prime theorem, prime-localization theorem, quotient-localization theorem and reduced-induced-structure theorem. The localization theorem is an inclusion-preserving bijection, which is the property required to transport minimality; it is not merely a map of spectra. The paragraph explains both restriction to an affine neighborhood and minimality below the chosen prime. No regularity of the components is assumed in this direction.

For step 9 I used the parameter-quotient theorem for any permutation to compute the ring and dimension of every selected intersection. The regular-scheme definition explicitly permits the locally Noetherian, stalkwise-regular criterion. The Noetherian quotient check is written out. This proves component regularity as a consequence, and all the boundary clauses then apply to the same reduced scheme H and the same components chosen in step 7.

I checked the small cases: the empty scheme, empty H, a point outside H, d=0 (only r=0 is possible), r=1, r=d, the empty subset of components, and subsets with empty intersection. A doubled hyperplane has nonradical ideal and cannot satisfy the parameter condition. The three lines xy(x+y)=0 in a regular two-dimensional local ring fail the expected-codimension condition at their common point and cannot be a product of distinct parameters; this also checks the essential dimension hypothesis emphasized by ILO Remark 4.2.2(ii). An irreducible nodal curve does not supply a counterexample: an ordinary local ring of an integral component is a domain and hence cannot have the split equation xy. No excellence, algebraic closedness, finite-dimensional global bound, or finite-type-over-a-field assumption was introduced.

I checked delivery-errors B–E against the finished artifact: all dependencies exist, the existing statements supply the assertions taken from them, no new statement or relabelled clause was introduced, there is no hidden induction or change of coefficients, and every non-elementary input is cited. The only steps marked elementary are the explicit generator-lifting argument and finite-denominator argument. Every step has fewer than 2000 characters. Generic statements filed outside the unit are declared as tool uses in `split_report.tool_uses`; they do not replace any higher-level proof route. The quoted citations are complete verbatim node statements so a reader can independently check each use.

## Unfinished work

None in the one-level split. Server validation and delivery results are recorded below when available.

## Server validation

- `srvcheck.py ... review_split`: PASS, zero new nodes. It notes that the existing unit has no realization recorded; this auxiliary split does not own that unit record.
- `deliver.py Q37 lem-sfb-snc-boundary-parameter-criterion --no-push`: exited successfully and printed `OK (not pushed)` at `4ad0506de19`, with server preflight passed.
