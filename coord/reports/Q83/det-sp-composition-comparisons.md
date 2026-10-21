# Q83: det-sp-composition-comparisons

## Files written

- `dag/nodes/sec-smooth-purity/det-sp-composition-comparisons.json`: statement, split into ten proof steps; Mathlib has categorical adjunction ingredients but no theorem stating this complete finite-coefficient and tower comparison assertion.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report.

New nodes: **0**. Mathlib leaves created: **0**. Existing structural nodes suffice. No unit realization fields changed: this item is a subsidiary comparison lemma, not the unit's key statement. No Lean was written and no compiler was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint id and composition/coefficient/adjunction terminology. There is no declaration tagged for this item. The generic adjunction/tensor-map composition declarations in `CategoryTheory/Adjunction/ProjectionTensorMap.lean` and the inverse-image coefficient-square discussion in `AlgebraicGeometry/EtaleRestrictScalarsPullbackSquare.lean` do not state all the compact-support, exceptional, strict-tower and integral clauses of this item.

## WANTED

None. The item and its proof are present in the current blueprint, and the underlying compactification/coefficient arguments are present in the local Stacks source.

## Corrections and source audit

**STATEMENT-DISPUTED: the displayed equations suppress indispensable composition comparisons, and the imported item has no statement dependencies defining its coefficient categories or maps.** Explicit endpoint check: `b_{gf}` starts at `S F_{gf,A} M`, whereas `F_{g,B}(b_f) b_g` starts at `S F_{g,A} F_{f,A} M`. These are isomorphic objects, not the same specified object. Likewise `c_{gf}` ends at `H_{gf,B} S K`, while the two-stage composite ends at `H_{f,B} H_{g,B} S K`. I repaired the statement by naming the canonical maps alpha and theta and putting them into both equations. Forgetting these maps recovers exactly the intended shorthand. No conclusion is weakened.

I also made the surrounding standing hypotheses explicit: separated finite-type schemes over the specified characteristic-p field, ell invertible, unital maps of finite commutative coefficient rings, and ordinary uncompleted finite-level constant-ring module categories. These are the actual domains of the existing reduction and exceptional lemmas. The integral realization statement explicitly uses the global finite-field setting of its cited integral adjunction theorem. The integral categories use completed ring sheaves; they are not silently identified with finite-level constant coefficients. The tower index is n >= 1 and means O_E/ell^n, as in the source, not an unannounced switch to uniformizer powers.

The source proof's sentence about finite-free terms and totalization does not provide, in its cited node's statement, a general theorem that equality on free terms yields the desired geometric composition equation. I instead expanded the structural coefficient-square argument using existing proper/open mate and refinement nodes. This is a choice below the unit: the unit still compares orientations and tensor maps using the composite adjunction, then proceeds through towers and derived limit. No purity or orientation theorem is used to prove its own composition law.

The source's reference to `det-sp-integral-adjunction-bijection` for the normalized-tower equivalence was too indirect. I cite `det-sp-normalized-equivalence` for that precise equivalence and reserve the integral adjunction node for its actual statement about the exceptional functor, units and counits. Tower evaluation is used only after the tower morphisms have been constructed. I never claim that evaluation is faithful on derived morphisms.

## Searches and reuse

The sandbox initially contained no item or report. I copied the current imported item once. `searches.jsonl` contains the six searches actually made by msearch.py: LeanFinder with two phrasings, Loogle for the adjunction names, two Mathlib grep queries, and LeanSearch. Their exact tool/query strings and returned log records are in `mathlib_searches`. All services answered. The initial LeanFinder returned module-sheaf pushforward composition, not compact support or exceptional/tower comparisons; LeanSearch returned unrelated compactly-supported continuous maps and generic sheaf functors. Loogle's combined name query returned no hits; the targeted source grep located `Adjunction.comp` and `rightAdjointUniq`. I read `Basic.lean` lines 565-590 (including the composite counit) and `Unique.lean`'s uniqueness and counit interface. These are already represented by existing mate-pasting/adjoint-uniqueness nodes and do not finish this item.

Whole-DAG and blueprint searches used the item id, composition, coefficient comparisons, adjunction uniqueness, proper/open coefficient and tower calculus terminology. I opened the actual statements of all 26 proof dependencies, not only their imported proofs. In particular, the finite-free compact-composition node only covers special coefficient-field quotient extensions, and `thm-sf-comp-composition` currently covers DVR quotients; neither was misused for arbitrary finite rings. The existing arbitrary-finite-ring compact-support comparison and proper/open coefficient-mate nodes supply the correct interfaces instead. A traversal through statement and proof dependencies found no path from any proposed dependency back to this item.

## Not duplicates

No new nodes are proposed. Existing categorical, arbitrary-finite-ring proper/open, tower and integral realization nodes are reused; no clause of this item was moved into a new statement.

## Review by Q83

I read the item and its separate proof in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/`, the unit statement and all four proof paragraphs, and the chapter record. For the geometric comparison I read `literature/stacks-project/more-etale.tex`: Tag 0F7B, label `lemma-shriek-proper-and-open`; Tag 0F7I, label `lemma-shriek-well-defined`; Tag 0F7J, label `lemma-shriek-composition`; and Tag 0GL6, label `remark-Rf-lower-shriek-change-of-rings`. The local tags table confirms those labels. Stacks supplies the proper/open construction and coefficient comparison background; the expanded normalization/pasting calculation is marked agent-written, rather than attributed verbatim to Stacks. There are no new nodes whose sources would need a separate audit. No SGA source is used.

Step 1 checks actual domains. The standing-setting node supplies chosen compactifications inside the finite-type separated setting; finite type over a field is Noetherian by the cited Noetherian-base statement and the elementary ideal check for a field. The relative-dimension permanence statement gives d+e for gf. The preservation node states the restricted adjunction, not merely a definition of f!, and the scalar-extension node states preservation of the finite-Tor constructible category for arbitrary finite ring maps. Thus no flatness or finite-projective-dimension hypothesis slips in.

Step 2 uses precisely the compatible-tower statement to obtain the cartesian proper/open square. The arbitrary-finite-ring unbounded compact-support comparison statement supplies the normalized composition and refinement independence. The finite-ring derived-origin statement supplies bounded etale origin and full faithfulness, unlike the older quotient-ring-only origin lemma. The specified proper site mate, open comparison and site equation in the proper/open coefficient-mate statement fix the pro-etale presentation. All proper maps here are between Noetherian finite-type schemes, so those statements apply.

Step 3 composes the two Hom bijections explicitly and writes their inverse formula. The mate-pasting statement includes the exact composite counit; the common-left-adjunction uniqueness statement supplies existence of the right-adjoint isomorphism. Its normalization and uniqueness are then checked by the displayed Hom bijection, rather than presumed to be an extra clause in the short uniqueness-node statement.

Step 4 uses the definition of the coefficient direct-image comparison for the actual B-linear proper mate and normalized open comparison. Mate-pasting applies to the two pullback/scalar squares. The scalar/tensor-normalization statement gives the K-flat inverse-image generator formula, which makes their pasted square the composite square by reassociation; for opens the maps extend the identical tensor section. Open-extension composition supplies the compositor being used. This is an explicit naturality/pasting calculation, not a new theorem about detecting arbitrary derived maps after forgetting scalars.

Step 5 opens the proper/open coefficient-mate statement and uses its displayed coefficient equation on exactly the cartesian square of step 2; its second displayed equation is the site transport square. The bounded-below assumptions on the input and its scalar extension hold by finite Tor amplitude and exact extension by zero. Scalar/site compatibility is checked by the generator and mate normalizations from step 4. The refinement node really states coefficient compatibility for noncartesian refinement squares, so it applies when moving back to the chosen compactifications. Pasting the three stated squares gives the complete b equation, including alpha on both sides.

Step 6 uses the *statement* of the exceptional-reduction node: the equation defining c as a counit transpose. I checked the successive substitution first for f, then g, and used naturality of b_g^{-1} with the map epsilon_f. The inverse is taken of the whole composite `F_g(b_f) b_g`, in that order. The resulting expression is exactly the defining transpose for c_{gf} by step 5 and the normalized composite counit. Injectivity of the Hom bijection proves equality of actual B-linear maps.

Steps 7 and 8 distinguish construction from evaluation. The tower-bound statement verifies the preservation hypothesis explicitly assumed by the tower compact-support calculus. That calculus states an actual compositor before evaluation. Tower gluing states an actual tower adjunction and says its evaluation comparisons preserve units and counits. Right-adjoint uniqueness constructs theta in the tower category; evaluating its counit equation identifies its finite evaluation by the finite Hom bijection. I checked that no unsupported lift of a family of derived maps is being used.

Step 9 quotes the tower calculus's *actual reduction formula* for F and tower gluing's *actual reduction formula* for H, not just their level functors. Substituting twice and moving the input reduction through the natural compositor leaves the b and c identities already proved. Normalization follows because these reduction maps are composites of isomorphisms. Uniform bounds are supplied separately by the tower bound and gluing, so invertible transitions alone are not being mistaken for constructibility or uniform amplitude.

Step 10 uses the reduction/Rlim equivalence only on Noetherian schemes and normalized towers. The direct-image and adjunction statements identify the actual integral functors with their tower realizations. I wrote the insertion of `red Rlim = 1` at the intermediate scheme in the functor composite; its applicability follows from step 9. The same calculation for right adjoints gives the exceptional compositor, with counits fixed by the integral adjunction statement. This is not an assertion that Rlim commutes with arbitrary functor composites without these comparisons.

For small cases I checked f or g equal to the identity (the proper/open compositor becomes its unit comparison and the Hom formula is unchanged), d=0 or e=0, empty source schemes, A=B (coefficient maps are tensor unit identifications), and a nonflat coefficient reduction such as Z/ell^2 -> Z/ell. The last case still uses B-linear mates and the already stated isomorphism b, never a bounded projective resolution. Towers use m=n as an identity reduction; arbitrary ramification of E causes no switch away from O_E/ell^n. There is no positivity or nonemptiness requirement hidden in the steps.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 against these files: no unsplit new-node proofs, duplicate or clause nodes, false leaf claims, nonexistent citations, reliance on an existing node's proof in place of its statement, cycles, or unannounced unit-route changes remain. Off-unit structural tools are declared individually in `split_report.tool_uses`; they provide the comparisons and categorical operations used by the unit, rather than replacing its purity argument. All ten proof steps are shorter than 2000 characters. `citations.json` uses verbatim text from the current statements; multiple-clause interfaces retain their whole statement where needed.

## Unfinished work

None in this one-level split. The previously existing dependencies retain their own statuses. Server checks and direct delivery are performed after this report is written.
