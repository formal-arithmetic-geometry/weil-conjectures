# Q123: lem-pur-dualizing-sigma-cocycle-locality

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-dualizing-sigma-cocycle-locality.json`: existing statement split in seven steps; statement and statement dependencies unchanged; no new nodes, no Mathlib leaves.
- `citations.json`: one verbatim statement extract for each use in every numbered proof step.
- `report.md`: this report. `searches.jsonl` contains the actual search-command log. The item-local `write_split.py` is only a sandbox generation aid, not a project file.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag, dualizing/cocycle terminology, and tensor/composition terminology found no declaration stating all of this item. The project has dualizing-object and smooth-purity infrastructure, but that is not an attachment for the three specified coherence identities and the finite-expression restriction assertion. No compiler was run.

## WANTED

None. The proof is explicitly agent-written; it expands the blueprint's formal coherence argument using existing DAG statements. It makes no claim that the blueprint itself is a human proof.

## Source and route

I read GOAL.md, the stage-1 brief, SETUP.md's three levels, roles/worker.md, stages/1-dag.md, delivery-errors.md B--E (including the repeated new-target checklist), and the chapter and unit records. The item's ancestor is `thm-pur-composition-coherence`, with `lem-pur-diagonal-section-pasting` in its existing via list. I read the current main-20261015 proof of composition coherence, especially Step 1's canonical composition/tensor reassociation and its final paragraph on smooth-base-change constituents, and the current composition unit's `_section.md`. I also read the current proof of `lem-pur-co-smooth-etale-locality`, whose Steps 1, 3 and 4 explain the etale normalization and locality that this item makes precise.

For the formal background I read Stacks `sites-cohomology.tex`, Remarks 0E46 (`remark-compose-base-change`) and 0E47 (`remark-compose-base-change-horizontal`), which omit the verifications, and Tag 07A4 (`lemma-pullback-tensor-product`) including its K-flat proof. I used DAG statements rather than those omitted verifications. In particular `lem-pur-smooth-exceptional-tensor-pasting` already states the necessary exceptional and tensor pasting equations. No SGA source is used, and no orientation, Tate twist or trace-based purity route is introduced.

The existing `lem-pur-composition-tensor-mate`, `lem-pur-smooth-exceptional-tensor-pasting`, and `lem-pur-finite-etale-dualizing-normalization` are strictly smaller ingredients of this item. Their full statements were read, including coefficient/category domains and the exact normalization of their maps. The site-transport lemma was also read: its last paragraph explicitly identifies conjugates of compositors and transposes of exchanges, so we do not silently identify etale and pro-etale formulas.

## Searches and reuse

There was no prior split or report in the sandbox and no active Q123 delivery process on resumption. I retained all pre-existing item metadata and search records. I searched the whole DAG through its JSON statements and blueprint references (`ancestor`, searches for `dualizing`, `cocycle`, and `tensor formula`), and read the relevant candidate nodes. The blueprint theorem on cohomological smoothness has broad composition compatibility, but does not by itself state all the normalized equations of this item. I therefore used the explicit existing tensor-transpose and pasting statements. I checked their entire statement/proof dependency closures; none reaches this item, so their use creates no cycle.

For the item I ran both phrasings recorded in the appended Mathlib searches: one about dualizing tensor associativity and etale restriction, one about counit transposes and pentagon/open compatibility. LeanFinder, LeanSearch, Loogle and the source grep all ran. The best abstract hit was `CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv`; the confirming grep found it at `Mathlib/CategoryTheory/Adjunction/CompositionIso.lean:82` and abstract associativity at line 170. I read lines 60--87 and 125--183. These are useful generic adjunction results, but they do not identify the actual geometric dualizing tensor maps, rho, eta, or etale source restriction. The other hits are ordinary ring tensor algebra, generic monoidal localization, ordinary scheme module restriction, or generic counit identities. None states the complete item or specializes to it in one line. I added no Mathlib leaf.

## Not duplicates

No new nodes were created. All substantive facts required for the split were reused from the live DAG; no elementary cancellation, item clause, or specialization was made into a node.

## Problems corrected

The old item had no proof. Its statement passed the type and domain checks, so I did not change it. I made the normalized comparison choices explicit in the proof and distinguished the lower base-change arrow v from the upper arrow u. I also wrote the mixed source/target open factorization, rather than incorrectly assuming an arbitrary source-open restriction square is Cartesian. The broad final assertion is proved by structural induction on the four stated expression-forming operations, not by an unsupported claim that all canonical maps commute.

## Review by Q123

I reviewed the split as its author against the actual source and cited statements, not just its dependency names. There are no new-node sources to review.

Step 1 uses the precise domain and invertibility paragraphs of `lem-pur-composition-tensor-mate`. They cover finite-type schemes without absolute separatedness, separated finite-type morphisms, pure smooth dimensions, bounded constructible finite-Tor inputs and etale-origin witnesses. The coefficient ring is exactly A_{E,n}, with n >= 1 and ell invertible. `lem-pur-finite-site-counit-projection-transport` explicitly carries the same compositors and exchange transposes to the pro-etale category. I used the associativity clause of `thm-sf-comp-composition`, the composition bijection in `def-weil-pbc-adjunction-conjugate`, and clause 2 of `lem-weil-pbc-mate-pasting` to obtain the equality for C, rather than citing a definition for associativity. The final sentence of `lem-pur-smooth-exceptional-tensor-pasting` states the precise threefold/symmetry reassociation consistency being used. The compact-support theorem is restricted to bounded-below etale-origin objects; the tensor-mate lemma explicitly supplies these, so no unrestricted right adjoint to a functor on an incorrect domain is invoked.

Step 2 specializes equation (*) of `lem-pur-composition-tensor-mate` to K = omega_w. Its statement ensures this is in D^b_ctf. I checked both routes have domain omega_u tensor u*omega_v tensor u*v*omega_w and codomain G_u G_v omega_w after postcomposition with the same C. The text displays the identical resulting arrow and the actual permutation s. Naturality of theta follows from its definition in `def-pur-co-smoothness`: projection, counit and tensor constraints are natural, and the adjunction bijection is natural. This is a direct substitution in existing equations, not a new threefold-coherence node. Cancellation is only by the specified isomorphism C.

Step 3 uses exactly clause 3 of `lem-pur-finite-etale-dualizing-normalization`, with h = v and h = wv. I checked that E sigma is eta tensor identity, not an arbitrary unit identification. Postcomposition of Step 2 and cancellation of sigma_u,v tensor identity give the displayed source-locality formula, with matching domains. This is an elementary consequence of two cited equalities, not a node duplicating one clause of the item.

Step 4 uses the last displayed equation and first iteration equation in `lem-pur-smooth-exceptional-tensor-pasting`. That node states arbitrary horizontal base change, smooth vertical arrows, the identity normalization and the same prescribed c, theta, beta. It therefore really does provide the intertwining and iteration needed here, unlike a definition of beta alone.

Step 5 again uses that node, this time on the tower e,h. An etale map has pure smooth dimension zero, and e' is its Cartesian base change. Clause 2 of the normalization node gives eta_e' beta_e,u = u1*eta_e; clause 3 supplies both E sigma formulas. I substituted them in the tower equation and wrote the cancellation explicitly. I verified that the square for he has lower arrow v and that both resulting arrows start at u1*omega_he and end at e'*omega_h'. This is where an unnoticed change of base-change arrow would have made the claim ill-typed.

Step 6 uses the rho composition law and its identity clause from the same normalization node. The equation for successive E maps follows by substituting rho c, the previously established c associativity, and naturality of rho. The text spells out the substitution; no stronger non-Cartesian base-change theorem is assumed. Its target-open comparison is the specific etale-horizontal formula of clause 3. Any compatible pair of source and target opens factors through the actual target pullback, then an open inclusion. The mixed commutation is Step 5. Thus source restrictions use E and need no Cartesian hypothesis on their general square.

Step 7 uses only functoriality plus the two explicitly cited natural comparison statements for tensor and pullback, and the reassociation clause of the existing pasting node. I checked composition, inverse, tensor and pullback separately. The inverse case contains its cancellation formula. Sections are handled by applying a derived pullback functor to an already proved equality, so smoothness of a section is not assumed. This covers the statement's final sentence without importing a purity theorem for sections.

For delivery-errors B--E: the item is self-contained and unchanged, all proof uses have verbatim quotes, all non-elementary comparisons are existing nodes rather than uncited tags or definition-only claims, all dependency closures are acyclic, and no new statements or hidden lemmas were introduced. Each step is below 2000 characters. I tested identities, an etale first map, dimension-zero pairs, the empty source, two successive source opens, target opens, and a compatible source/target restriction which is not Cartesian. The formulas reduce to their normalized units or to equalities after applying the zero-category functor as appropriate; no nonemptiness, positive dimension, absolute separatedness or global orientation is used. The report and node preserve the blueprint route.

## Unfinished work

None for this one-level stage-1 split. Existing unsplit dependencies remain their own items; they were not copied, split, or modified here. No Lean was written and no compiler, Lake, build, or local preflight/check_dag/review_split was run.
