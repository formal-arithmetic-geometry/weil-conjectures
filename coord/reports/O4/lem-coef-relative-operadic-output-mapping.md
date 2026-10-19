# Worker report: lem-coef-relative-operadic-output-mapping

## Files written

- `dag/nodes/sec-six-functors/lem-coef-relative-operadic-output-mapping.json`: existing statement, now split into six steps. No statement or statement-dependency change. Mathlib verdict: no match, after the four required search tools and a second LeanFinder phrasing.
- `citations.json`: verbatim statement extracts for every proof-step citation, checked against the shared DAG.
- `searches.jsonl`: the search command's unmodified log. All inherited item searches were retained in the item; the actual searches of this attempt were appended separately.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record, Lean file, shared repository, live launcher, or target was edited.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag, operad/operadic, inert projection, Segal, and output/mapping vocabulary found no declaration stating the item. The upstream master source was also searched for the item and output-mapping phrase; it supplied no attachment and its sorry declarations would not establish completion.

## Sources wanted

WANTED: Jacob Lurie, *Higher Algebra*, September 18, 2017 edition, Construction 2.1.1.7, Definition 2.1.1.10, Proposition 2.1.2.22, Remarks 2.1.2.16 and 2.1.3.4, for lem-coef-relative-operadic-output-mapping. Read the Harvard PDF online at https://people.math.harvard.edu/~lurie/papers/HA.pdf; no local archive was found under literature/. The proof is therefore explicitly marked agent-written.

WANTED: archives of Kerodon Tags 0110 (homotopy-pullback pasting) and 032B (invariance), read online for the existing tool statements used here. These identifiers are Kerodon tags, not Stacks tags. There is no Stacks tag for the infinity-operadic result. No SGA source is used.

## What needed repair

The item was statement-only, with no proof or proof dependencies. Its existing statement is correct; no STATEMENT-DISPUTED repair was needed. The tempting shortcut of calling an inert edge q-cocartesian merely because q preserves inert edges is incomplete: preservation concerns the projections to Fin_*, not the relative map q. Step 1 supplies the missing argument by pasting mapping squares. Step 2 takes a relative fiber over the full operator f, rather than only restricting to its underlying pointed map. Step 3 keeps exactly the block of inputs belonging to each output, including the empty block. Step 5 accounts for coherent naturality rather than selecting unrelated inverses object by object.

The current blueprint source for the historical ancestor is `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. I read its middle mapping-complex comparison and the older master proof named by the existing ancestry. This item supports the already extracted colored-operation section reconstruction beneath that comparison; it does not change the unit route or assert a new reconstruction theorem. The chapter and bound unit record were read. The historical unit and blueprint ancestry are retained.

## Not duplicates

No new nodes were created, so there are no new/existing tag pairs. Whole-DAG and whole-blueprint searches for operad, colored, mapping spaces, relative output mapping, output fiber mapping, and output color/colour mapping supplied existing tools or the item itself. I reused those tools rather than creating a Segal-formula lemma or a transport-factorization lemma restating the item's clauses. `blueprint_refs.py ancestor` confirmed prop-coef-integral-exceptional-adjoint; the blueprint searches found no equivalent imported node, so same_as stays empty.

## Review by N4

I checked the item against Higher Algebra (2017), printed pp. 173-174 (operator category and mapping Segal axiom), pp. 182-184 (operation transport and relative inert edges), and pp. 184-185 (coherent pointwise families). The operator remembers one operation per non-basepoint output, not an operation on discarded inputs. The hypothesis that q is a cocartesian fibration is used for active as well as inert transports; a bare operadic fibration would not justify step 4. Both E and B are symmetric infinity-operads, and their arity maps are inner fibrations. The assumed Segal equivalence concerns degreewise fibers over the exact color tuples. Nothing is replaced by an ordinary category of modules or by a homotopy category. No new statement node has to be checked against a source.

Step 1 uses the statement of lem-coef-relative-operadic-terminal-active-mapping only for its explicitly written definitions of symmetric infinity-operad, inert edge, and operad map. It does not use that theorem's free-algebra conclusion. I opened lem-coef-infinity-cocartesian-mapping-criterion: it states the needed equivalence of horn cocartesianness with a mapping-space pullback for every target, for any inner fibration. I opened lem-coef-infinity-homotopy-pullback-pasting: it permits cancelling a known pullback square against the outer rectangle, including specified commutation homotopies. Those statements apply to the stacked q and arity mapping squares, after transposing. The image edge is inert because q is an operad map. Conversely the same test proves that the frame's q-cocartesian lifts over inert operators are inert upstairs. This avoids adding a separate general transitivity node.

Step 2 uses the actual Segal mapping clause written in lem-coef-relative-operadic-terminal-active-mapping. I checked that it is a mapping-space product assertion and not merely a product assertion about objects. The chosen output projections are inert by step 1. The statement of lem-coef-infinity-inner-mapping-fiber applies to the arity inner fibrations and yields Kan inverse images over the discrete pointed-map sets. For an ordinary nerve, the right-pinched formula immediately makes its mapping spaces discrete arrow sets in every degree; the lower Segal map is literally the operator's list of output operations. I opened lem-coef-kan-homotopy-pullback-invariance and checked that all three maps between its cospans are equivalences here: the top Segal equivalence, the discrete bottom isomorphism, and the point-to-point identity. Thus it applies to the homotopy fiber. Products of those fibers are obtained by expanding the path definition coordinate by coordinate, an elementary step and not an unproved interchange theorem.

Step 3 uses exactly the composition and comparison-of-initial-lifts conclusions of lem-coef-infinity-cocartesian-composition-initiality, whose statement I read. The two projections being compared have the same initial object X and the same singleton operator in the base, so its target comparison is genuinely an equivalence in the correct degreewise fiber. I also read def-coef-colored-operator-systems: its transport frame really includes coherent cocartesian lifts and the Segal equivalences, not just a list of functors. This identifies the block transport with the listed T_theta and ties the two composable lifts to the desired composite over h_j. It does not infer a map merely from containment of sets of inputs.

Step 4 uses the displayed natural relative mapping-fiber equivalence of lem-coef-infinity-pointwise-cocartesian-transport at K=Delta[0]. I checked that its target H belongs to the exact target fiber E_dj, and that the chosen source and lift are X and e_j. The mapping criterion already read converts its edge convention to the horn convention. The resulting equivalence is induced by precomposition with e_j, so its inverse is precisely the required factorization comparison. No terminal-active slice or colimit theorem is used.

Step 5 uses the coherent successive-transport and compatibility-with-precomposition clauses of that same pointwise transport node and the coherent frame definition. Their statements give compatibility with diagram parameters and composition. Output projection is functorial in Y; precomposition makes it contravariant in X. Therefore the equivalences assembled in step 4 are equivalences of the specified space-valued functors. Inversion takes place for this natural equivalence and does not discard its coherences. The source's pointwise-family remark agrees with this construction.

Step 6 is elementary from the preceding formulas and the stated empty Segal hypothesis. I checked n=k=0, n>0 with k=0 and all inputs discarded, k=1 with unary identity, and n=0 with k>0 and available nullary operations. For k=0 the unique empty operator and the empty product are points. For a nullary operation with a surviving output the factor Map(T_theta(()),y_j) remains: for an ordinary monoidal category it is a Hom-set from the unit and need not be a singleton. Empty color fibers cause no inference of an object where none exists; the cocartesian lift is used only from an already specified X. Discarded inputs appear in no selected block. Arbitrary color-fiber limits and colimits never enter the proof.

I checked B-E of delivery-errors.md: no new-node formatting or duplication issue, no item clause moved into another node, and no reliance on the proof rather than the statement of a cited node. Every non-elementary step has existing node citations. I checked that none of the cited dependencies has a dependency path back to the item. All proof steps are below 2000 characters (1211, 1537, 1289, 966, 1034, 871), and each has a distinct argument: inert recognition, relative Segal fiber, block identification, representation, naturality, and edge cases. No hidden standard comparison remains without a cited statement. Searches of all four kinds were run through msearch.py and their hits read; the second semantic phrasing returned multiequalizer and simplex-product material, not a competing operadic theorem. IsCocartesian/IsStronglyCocartesian and Fiber were read at their Mathlib source lines and are only ordinary-category statements, so there is no exact or one-line-specialization Mathlib leaf. No services were reported unavailable.

## Unfinished work

No part of this one-level split is left unfinished. The existing cited tools remain separate DAG items according to their own status. Validation and delivery use the required server preflight; no local checker or compiler is run.
