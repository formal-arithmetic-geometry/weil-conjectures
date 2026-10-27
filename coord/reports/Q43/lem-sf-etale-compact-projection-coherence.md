# Q43 stage-1 report

1. Files written:
   - `dag/nodes/sec-six-functors-basics/lem-sf-etale-compact-projection-coherence.json`: item, statement, split into eight steps; no Mathlib match.
   - `dag/nodes/sec-six-functors-basics/lem-sf-etale-proper-open-tensor-square.json`: new statement-only lemma; no Mathlib match.
   - `dag/nodes/sec-six-functors-basics/lem-sf-etale-locally-closed-graph-model.json`: new statement-only lemma; no Mathlib match.
   - `citations.json`: verbatim statement quotations, one for every step/node pair. Existing search records are preserved in `searches.jsonl`; the node search fields reproduce the queries and logged results.
2. Attachments: none. The item's projection associativity and composition-coherence declarations in `LowerShriekCompositionCoherence.lean` have `sorry`. The graph-model existence theorem is present in `LowerShriekComposition.lean`, but its declaration does not state the additional normalized construction recorded here. Its existing proof is source material, not an assertion of an independently audited closed attachment.
3. WANTED: none.
4. Corrections: retained the item's statement and its arbitrary-scheme, unbounded, ordinary-etale scope. Preserved its computed null blueprint ancestor: the created.item chain passes through exceptional tensor transitivity and stops at the maintainer-created smooth-dualizing node, whose created.item is null. The from.place and split report identify `sk-prop-sf-rf-shriek-preservation` as the conceptual unit and give its exact proof location, without inventing a provenance edge. The imported route did not supply the morphism-level tensor compatibility of graph comparisons; the split exposes the Cartesian tensor square and the explicit graph comparison instead of treating an existential functor isomorphism as a coherent one. No Noetherian, quasi-compact-open, pro-etale, or constructibility-restricted lemma is silently substituted.
5. Unfinished mathematical subwork: the two new nodes intentionally have statements only, as required by a one-level split. No Lean was written and no compiler, Lake, or build was run. The delivery checks are recorded below after they complete.

## Review by Q43

I read the current blueprint's `thm-asd-smooth-tensor.proof.md`, paragraph 3, in the smooth case of the unit. The relevant assertion is the identification of both transposes with projection followed by the composite counit. I checked the item against its ordinary-etale Lean declarations and found no finished declaration giving all clauses. The graph comparisons are read directly from `LowerShriekComposition.lean`, especially lines 193–268 and 309–380, rather than inferred from the existence-only statement of compact-support composition.

For the new Cartesian tensor-square node I read Stacks `more-etale.tex`, Tag 0F7B, including torsion-ring case (b): proper verticals, separated locally quasi-finite horizontals (in particular opens), arbitrary schemes, and the entire unbounded derived category. I also read the projection-map definition and compatible-diagram calculation in `sites-cohomology.tex` (0B56, 0E48), and the open tensor map 0GL1 / 0E8I. The source's interchange theorem alone does not assert the tensor square: that extra mate compatibility is stated explicitly as new work. Its formula has source J_i R_r M tensor N and target R_p J_k(M tensor P_k P_p N); both sides have these endpoints under the pullback compositor. The beta, unit and counit order is checked against the source's open exchange construction.

For the new graph-model node I read the full product/graph proof of `nonempty_iso_rightDerivedLowerShriekOfCompactification`, including its eA, eC, eB maps, not just its signature. O1 and O2 are opens in the same product T, their intersection contains the graph, and the map into the intersection is proper because its composite with the separated open projection is proper. B1 uses p2, B2 uses p1, with the equality cp2=pi p1 identifying their proper output. This is a real comparison construction; it does not assert either tensor law of the item. The item proves tensor compatibility by checking the constituent replacements.

Step 1 uses the ambient adjoint/projection theorem exactly for invertibility on all unbounded finite-coefficient etale objects, the projection definition for its counit normalization, the open tensor theorem for delta, and ringed monoidal comparisons for the canonical pullback constraints. I checked all four statements. Constant-ring module pullback is the exact etale inverse image. Naturality of inverses is obtained by multiplying the naturality equation by inverse components.

Step 2 uses the open tensor statement, the site tensor-descent statement, and the open-composition projection statement. The first fixes the actual sheaf map; the second permits its flat-term total-complex calculation to descend to D, and the third supplies open composition. For ordinary A-modules the sheaf-composition hypotheses are the restriction-normalized open adjunctions, tensor and their canonical compositors; functorial flat resolutions and flat-preserving inverse image are the same module models of the tensor-descent statement. The calculation is equality of chain maps on each triple totalization summand, not a false inference that geometric stalk functors detect equality of derived arrows. I marked this step non-elementary because it invokes derived tensor descent.

Step 3 reads the associativity clause of `lem-sfb-ringed-projection-tensor-composition`, applicable to arbitrary small ringed topoi and arbitrary unbounded inputs. Naturality moves the open comparison past the proper projection, leaving precisely that clause and the open calculation. Inversion gives the requested q equation, with the reversed order of factors.

Step 4 uses that same node's direct-image-composition clause and the new square's actual displayed equality. The latter, rather than its mere isomorphism assertion, is what licenses moving the base tensor factor through an interchange. Inverting, whiskering and pasting commuting squares is explicitly justified by multiplying components and functoriality. Step 5 uses only the graph-model statement, whose B1/B12/B2 are explicitly products of these generators, and applies step 4 to each constituent. It does not take tensor compatibility from an existence theorem.

Step 6 checks the geometric hypotheses previously implicit in the graph argument. I opened the proper base-change, proper-composition, open base-change, proper-to-separated-target, and proper-definition statements. O to X is proper by base change, so separated; the composite of a with it is the identity, making a proper by the proper-to-separated-target theorem. Since u a'=a and u is open (its diagonal is an isomorphism), the same theorem makes a' proper. The remaining proper maps are base changes or composites of supplied proper maps, and the opens are base changes of the supplied opens. Thus this use requires neither a finite-type base nor a quasi-compact open.

Step 7 uses the explicit normalized graph-model comparisons twice. The existing compact-support-composition node is cited for the endpoints/existence of the composition isomorphism; the actual normalization is the written e1/e3/e2 word from the Lean source, assembled using steps 4–6. The intervening proper/open comparison for a map factoring through an open is indeed the Cartesian special case: its pullback along that open identifies with its source. Step 8 uses only cancellation and functorial preservation of inverse maps. I checked the order of q_g and F_g(q_f) by composing back with their forward projections.

I tested identity opens and proper maps: beta and the identity compositors collapse to identities, the square becomes the projection naturality identity, and the graph word reduces to the ordinary direct-image compositor. Empty schemes, zero complexes and the zero ring give zero objects and valid identity isomorphisms. Non-quasi-compact opens are allowed by the actual 0F7B torsion case and the arbitrary-base graph construction; no finite cohomological-dimension bound is imposed globally. Every finite ring is torsion, including the zero ring. I reviewed delivery-errors B–E: no clause of the item has simply been moved into a new node, all non-elementary inputs are named, all step citations have verbatim statement quotations, and no forbidden SGA route is used. All proof steps remain below 2000 characters after separating the geometry from comparison pasting.

## Not duplicates

lem-sf-etale-proper-open-tensor-square vs lem-sbc-strict-perfect-tower-projection: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-proper-open-tensor-square vs def-sbc-quotient-exchange-scalar-comparisons: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-proper-open-tensor-square vs def-sbc-strict-augmented-coefficient-presentation: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-proper-open-tensor-square vs lem-sbc-strict-reduction-pullback-square: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-proper-open-tensor-square vs lem-sbc-strict-projection-coaugmentation: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-proper-open-tensor-square vs def-sbc-quotient-coefficient-presentation: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-proper-open-tensor-square vs lem-sbc-strict-tower-mate-evaluation: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-proper-open-tensor-square vs lem-sbc-strict-quotient-exchange-unit-equation: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-proper-open-tensor-square vs def-sbc-strict-coefficient-exchange-arrows: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-proper-open-tensor-square vs lem-sf-constant-semilinear-generator-comparison: The existing statement concerns integral/semilinear reductions with etale-origin and bounded-amplitude input restrictions; the new square is ordinary etale, constant finite coefficient, arbitrary-base and all-unbounded, without those restrictions.

lem-sf-etale-proper-open-tensor-square vs lem-sf-generator-reduction-coherence: The existing statement concerns integral/semilinear reductions with etale-origin and bounded-amplitude input restrictions; the new square is ordinary etale, constant finite coefficient, arbitrary-base and all-unbounded, without those restrictions.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-completed-reduction-pullback-square: The existing statement concerns strict coefficient towers, reductions, or their evaluated exchange arrows; the new statement concerns constant finite coefficients on ordinary etale sites and the Cartesian proper/open interchange with its explicit projection square.

lem-sf-etale-locally-closed-graph-model vs lem-sf-ambient-clopen-restriction-uniqueness: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs lem-sf-clopen-comparison-tensor-square: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs lem-sf-projection-refinement-descent: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs lem-sf-unbounded-compact-support-proper-composition: The existing theorem assumes proper f and separated finite-type schemes over a field; the new statement constructs the normalized proper-open-proper graph model for arbitrary schemes and an arbitrary proper-open-proper factorization.

lem-sf-etale-locally-closed-graph-model vs lem-sf-ambient-proper-open-pasting: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs lem-sf-ambient-exact-clopen-comparison-localization: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs lem-sf-native-weil-open-proper-interchange: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs lem-sf-semilinear-proper-open-mate-pasting: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs def-coef-semilinear-proper-open-mate: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs lem-sf-composition-projection-mate: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs lem-sf-proper-open-projection-mate: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

lem-sf-etale-locally-closed-graph-model vs def-sf-semilinear-proper-open-comparisons: The existing statement concerns pro-etale or semilinear coefficient comparisons (or their restricted constructible realization); it does not state the arbitrary-base ordinary-etale product/intersection graph model B1/B12/B2, which asserts no tensor law.

The closer potential duplicates were also opened: `lem-amb-unbounded-proper-open-interchange` and `lem-amb-unbounded-compact-support-comparisons` assume Noetherian schemes, so cannot provide the arbitrary-base input; `lem-sf-proper-open-projection-mate` and `lem-sf-clopen-comparison-tensor-square` use pro-etale sites and quasi-compact opens; `lem-etale-unbounded-compact-support-composition` states existence, not the specified product/intersection graph comparison. The ringed projection and monoidal comparison statements do apply and are reused rather than recreated. The recorded Mathlib hits are structure-sheaf restriction/pushforward, general monoidal exchange identities, or unrelated compact-support topology; none specializes in one line to either new derived-etale statement. DAG, tag, blueprint and project-Lean searches from the interrupted work were retained.

lem-sf-etale-locally-closed-graph-model vs lem-weil-pbc-etale-open-proper-interchange: Existing bounded-below interchange assumes a quasi-compact open and states no arbitrary proper-open-proper product/intersection graph model; the new statement is all-unbounded without quasi-compactness.

lem-sf-etale-locally-closed-graph-model vs lem-sfb-exact-compactification-unit-composition: Existing exact-functor unit composition assumes Noetherian schemes and quasi-compact finite-type maps; the new statement constructs B for arbitrary schemes, without exact sheaf functor data or unit comparison equations.

lem-sf-etale-locally-closed-graph-model vs lem-sfb-exact-compactification-unit-refinement: Existing theorem compares exact-functor units under Noetherian compactification refinements; new B is an explicit product/intersection construction for arbitrary-base proper-open-proper factorizations.

lem-sf-etale-locally-closed-graph-model vs lem-sfb-proper-open-tower-derived-unit: Existing theorem assumes Noetherian schemes and proves a homotopy between K-injective resolution paths in a tower; the new node states a normalized graph-model isomorphism for arbitrary schemes.

lem-sf-etale-locally-closed-graph-model vs lem-sfb-proper-open-tower-single-unit-formula: Existing statement is a conditional equation of representative paths with a supplied sheaf isomorphism; it neither constructs nor states B1/B12/B2 for product graph models.

lem-sf-etale-locally-closed-graph-model vs lem-sfb-proper-open-tower-successive-unit-formula: Existing statement is a conditional successive-unit representative equation given resolutions and Gamma; new B fixes a different product/intersection graph comparison, without such supplied representative hypotheses.

lem-sf-etale-locally-closed-graph-model vs def-sf-etale-support-compositor: Existing definition uses the compactification ofComp/restrict tower and assumes f and gf quasi-compact; new graph B works without quasi-compactness and specifies the proper-open-proper comparison rather than defining the support compositor.

lem-sf-etale-proper-open-tensor-square vs def-weil-pbc-ringed-tensor-square-presentation: Existing definition specifies inverse-image square data, not extension by zero, interchange invertibility, or its proper-adjoint projection equation.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-completed-exchange-unit: Existing equation compares ordered completed exchange with ambient exchange via completion units; the new square uses open extension by zero, with no completion operation.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-finite-level-rectangle: Existing finite-level coefficient rectangle has no open extension by zero or proper/open interchange map; the new equality concerns those operations.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-finite-reduction-pullback-coherence: Existing statement compares two coefficient-reduction pullback paths; the new statement has a proper-adjoint interchange and open tensor projections, not coefficient reduction.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-finite-reduction-pullback-square: Existing statement is the reduction/pullback inverse-image square, not the J_i R_r to R_p J_k projection square.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-flat-scalar-tower-exchange: Existing theorem intertwines exchange under flat scalar restriction on strict towers; new square concerns open extension by zero at fixed finite coefficients and states interchange invertibility.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: Existing coefficient rectangle intertwines finite reduction with the ordinary pullback/direct-image exchange. It does not involve J_i or the proper/open mate Gamma.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-ordered-exchange-coefficient-comparison: Existing theorem compares ordered completed exchange with constant coefficient towers on complete inputs; the new statement has neither adic completion nor tower input, and uses open extension by zero.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-ringed-exchange-tensor-coherence: Existing theorem proves tensor compatibility of the Lg* Rf* to Rf'* Lg'* exchange. Open extension by zero J_i is a different left adjoint from inverse image, so its J_i R_r to R_p J_k mate square is not a one-line instance; moreover the new node states proper/open invertibility.

lem-sf-etale-proper-open-tensor-square vs lem-weil-pbc-ringed-square-tensor-compatibility: Existing theorem asserts tensor compatibility of a pullback square only on flat-term K-flat representatives, expressly excluding projection and adjunction-mate claims. New statement is the proper/open mate projection equation on all derived inputs.

lem-sf-etale-proper-open-tensor-square vs lemma-weil-pbc-completed-exchange-coherence: Existing theorem states identity/pasting for completed exchange, not the open-extension proper-adjoint tensor square or its invertibility.

## Delivery validation

The first dry run exited before server preflight with a duplicate-report diagnostic; nothing was pushed. I opened all additional statements it named and recorded the distinctions above. The generic ringed exchange theorem applies to inverse image, not to the different open-extension left adjoint, so it does not replace the new proper/open square.

The second dry run reached server preflight and returned only two B9 ancestor diagnostics. I ran the prescribed blueprint ancestor command: it returns None. I corrected both new nodes to that computed value, restored the item to its inherited null value, and retained the conceptual blueprint location in from.place. No ancestor nodes or tools were changed.
