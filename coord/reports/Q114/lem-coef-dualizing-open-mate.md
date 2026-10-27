# Worker report: lem-coef-dualizing-open-mate

## Files written

- dag/nodes/sec-six-functors/lem-coef-dualizing-open-mate.json: existing statement, split into five proof steps using existing nodes; no Mathlib match for the whole statement.
- citations.json: verbatim statement quotations for every cited node in every proof step.
- searches.jsonl: actual Mathlib searches through msearch.py, read before recording verdicts.

No new nodes and no Mathlib leaves. The statement, hypotheses, coefficient categories and all maintainer-owned metadata are unchanged. The preparatory Python script stays in this sandbox and is not part of the delivery.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, dualizing/coefficient combinations and the relevant SixFunctors sources. The existing dualizing objects and general adjunction constructions do not state this quotient-coefficient open-restriction identity with its two specified adjunct equalities. In particular the pro-etale sources are not substituted for the ordinary small-etale assertion.

## WANTED

None.

## Findings and changes

The imported item is a genuine open-locality calculation, not an exceptional coefficient isomorphism theorem. Its initial proof was empty. Rather than restating its conclusion as a new node, the proof now uses three existing tools: lem-coef-dualizing-open-adjoint supplies the actual normalized structural counit, lem-coef-etale-open-tensor supplies the B-linear open comparison and its evaluation equation, and lem-sf-compact-coefficient-composition supplies the coefficient/compositor square. The inverse naturality equation and the final adjunct uniqueness argument are written explicitly.

The existing lem-fix-open-scalar-tensor-normalization and lem-coef-open-scalar-adjunction-counit concern pro-etale categories; they were read but deliberately not used for the ordinary-etale calculation. The older lem-amb-etale-adjoint-locality statement alone does not assert the displayed normalized counit formula; the existing stronger lem-coef-dualizing-open-adjoint is the citation that actually provides it. This avoids taking material merely from a cited node's proof.

No statement dispute or change of unit route. The item is not the unit's key statement, so no unit realization fields are modified. Its blueprint ancestor is lem-coef-finite-dualizing; its existing from.place already specifies paragraph 3, sentences 2-3 and is retained. Whole-blueprint searches for 'open scalar', 'coefficient composition', and 'dualizing' found no other blueprint statement equal to this item; same_as is empty.

## Not duplicates

No new nodes were created. Existing ordinary-etale open tensor, structural open adjunction and compact-support coefficient composition nodes were reused. No clause of the item was moved to a new node.

## Review by Q114

I read the item's complete statement and its source, literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-dualizing.proof.md, especially the paragraph asserting that the local and global maps have the same composite-adjunction transpose. This is an agent-written blueprint argument, so the expanded proof is recorded with proof_origin.by = agent. I also read the Stacks source more-etale.tex at lemma-shriek-composition (Tag 0F7J) and remark-Rf-lower-shriek-change-of-rings (Tag 0GL6), and sites-cohomology.tex/sites-modules.tex at lemma-j-shriek-and-tensor (Tags 0GL1/0E8I). These explain the composition and tensor route; the proof cites the existing DAG statements for the stronger normalization assertions, not the Stacks tags as if they asserted all those equations verbatim. No SGA source is used.

For step 1 I opened lem-coef-dualizing-open-adjoint and verified that its statement gives both F_U = F_Y j_! and epsilon_U = epsilon_Y F_Y(e), with counit-preserving dualizing identifications in the same ordinary small-etale categories. Its field, quotient-ring and separated finite-type hypotheses are precisely the item's. Thus L is the assumed bounded constructible finite-Tor omega_U, not an arbitrary unsupported restriction claim.

For step 2 I read def-weil-pbc-constructible-complexes and def-kun-tor-amplitude, the statement of ordinary-etale exactness lem-weil-pbc-extension-by-zero-exact, the ordinary-etale open projection and exact restriction statements in lem-coef-etale-open-tensor, and the entire statement of lem-fix-compact-support-coefficient-change. Extending the finitely many cohomology stratifications by the closed complement proves constructibility; exactness preserves the cohomological interval; the projection identity for every degree-zero test sheaf proves the Tor interval. This is a direct argument from the cited statements and definitions, and is marked elementary. The open is quasi-compact since it is affine in a finite-type scheme, so the extended strata remain constructible. The comparison inverses in the rest of the proof occur only at W, L and j_!L, all now checked. In particular I have not inferred finite Tor amplitude from boundedness alone, or flatness of B over A.

For step 3 I opened lem-coef-etale-open-tensor and checked that its statement contains the B-linear open comparison and exactly the equation e_B j_!(r) d = T(e_A); it has no coefficient-flatness hypothesis. Naturality of the evaluation natural transformation moves j^*u_Y past that evaluation. The proof displays the resulting equation before applying F_Y and the defining counit identity of u_Y, which yields the first asserted adjunct expression. The r_W comparison is explicitly present before being suppressed by the stipulated identification.

For step 4 I opened lem-sf-compact-coefficient-composition and checked its exact displayed equation, on ordinary small-etale categories and for bounded constructible finite-Tor inputs. Its specialization is f=j, g=a_Y and K=L; these are separated finite-type maps of separated finite-type k-schemes with the same quotient pair A to B. Its open-factor coefficient comparison is the canonical open tensor map d_L of lem-coef-etale-open-tensor. The proof explicitly writes c_U = F_Y(d_L)c_Y,j_!L and its inverse, rather than claiming unspecified compatibility. The other equality is naturality of the canonical comparison from lem-fix-compact-support-coefficient-change at the evaluation e_A. Multiplying these equalities and the normalized structural counit equation from step 1 proves the second asserted adjunct equality with all arrows having the right source and target.

For step 5 I checked thm-amb-etale-exceptional-adjoint: the finite quotient rings and structure maps have the adjunctions named in the item. Equality of the two actual adjuncts implies equality of maps by injectivity of its Hom bijection. This is an elementary consequence of an adjunction, with no assertion that an exceptional-adjoint coefficient comparison has already been constructed.

I checked edge cases: m=n makes the scalar maps identity; U=Y makes the two evaluations and composition identifications identity; U empty makes the unique maps from the zero object agree. The argument never inverts u_Y or u_U, so it does not presuppose the dualizing coefficient theorem it supports. I traced the dependencies of the three substantive cited normalization nodes and found no path back to this item. All steps are shorter than 2000 characters. Every uses entry has a verbatim statement quote in citations.json; proof_deps is their exact union. The only off-unit generic tool recorded in split_report.tool_uses is ordinary-etale extension-by-zero exactness for the domain calculation; definitions are notion dependencies. I checked delivery-errors B through E: no new statement-only nodes to audit, no duplicate or relabelled conclusion, no hidden source citation, no pro-etale/etale category substitution, no new hypotheses or inverse outside its verified domain.

## Unfinished work

None in this one-level split. Existing unsplit dependencies remain their own queue items. Direct delivery is subject to the required server dry run and independent maintainer review.
