# Stage-1 delivery: lem-trf-scheme-descent-quotient-chart-isomorphism

## Files written

- dag/nodes/sec-trace-formula/lem-trf-scheme-descent-quotient-chart-isomorphism.json: statement, split into six proof steps; not a Mathlib leaf.
- citations.json: all 16 step/node citations, with verbatim statement quotations.
- searches.jsonl: five current searches actually run with msearch.py. The item's older searches and their results remain intact.

New nodes: 0. New Mathlib leaves: 0. No unit record changed.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and descent/quotient/chart notions. No declaration states every clause of this item. The source hits concerning section-ring quotient charts, affine descent, and coefficient quotients are different results.

## WANTED

None. Sources used are available in literature/stacks-project.

## Corrections and limitations

The statement is unchanged and not disputed. The imported node had no proof. The proof must not assume that an arbitrary section of F lifts globally to V: it uses the existing generic local-lifting node and explicitly glues the transported local sections. Nor may one treat theta_ii as the identity everywhere on U_ii: it is only normalized after pullback along the diagonal. Both potential gaps are resolved in the written steps.

The current latest blueprint is main-20261023-1620 (7284bb09daf97437d544c51882b325f9c52cd345). Read the latest chapter/unit and lem-trf-local-term-locality statement/proof. The latter now follows contracting correspondences and does not contain the historical descent sentence recorded in this item's ancestry. This item is an already-created auxiliary to the live polarized-scheme-descent input, not a proposal to replace the current unit route. Its existing ancestry and all metadata are retained; the split_report explains the historical place. Searches of the whole imported blueprint for quotient, subcanonical, descent datum, and base chart found no exact alternate statement; same_as remains empty.

Off-unit tool use: lem-a1-representable-etale-fppf-local-lifting supplies local lifts for any assumed representable surjective etale scheme atlas. The same-unit quotient presentation theorems require identifying F as a particular sheafified quotient, which is not a hypothesis of this item. The general local-lifting statement is precisely the weaker tool needed. The sheaf definition in def-weil-pbc-sites-and-cohomology is also declared for its equalizer condition. All other off-unit results used are existing Mathlib leaves (scheme coproducts, open immersion definition, scheme fibre products, etale composition, fpqc representable descent).

Nothing remains mathematically unfinished in this split; the existing cited nodes keep their own proof obligations.

## Not duplicates

No new nodes. In particular the existing local-lifting node, fppf-is-fpqc node, and representable fpqc descent node are reused. The existing etale-relation-quotient node constructs a quotient, whereas this item recovers schemes over base charts from an assumed kernel-pair presentation; citing it as the whole argument would not prove chart recovery.

## Review by Q75

I read Stacks spaces.tex Tags 0262 (lemma-space-presentation), 02WV (lemma-when-it-works-it-works), and 02WW (theorem-presentation), plus the scheme-test definition of a representable map with a property (025V). They justify the presentation/local-lift method, not by themselves the chart isomorphisms. The written normalized-cocycle calculation supplies that missing argument. I also read Descent Tag 023Q, Topologies Tag 022C, Schemes Tags 01JB/01JC, and Morphisms Tags 02GP/02GN/02GO. Tag-label lookup corrected my draft reference for the scheme-test property to 025V. No SGA source is used.

Step 1 uses the existing scheme-coproduct statement: it supplies disjoint open components covering the coproduct, not a false equality Hom(T,coprod X_i)=coprod Hom(T,X_i). A general T can meet many components. The argument restricts an actual relation section r: T -> R; because its two projections land in the fixed i,j components, all inverse images except R_ij are empty. The open-immersion definition then supplies factorization. The assumed kernel-pair isomorphism supplies uniqueness. Thus the component identification is proved rather than presumed or delegated to a new restatement node.

Step 2 uses exactly the fibre-product universal property from def-pc-fibre-product. Equal images under a_i give equal structure maps to U_i, so the relation section lies over (u,u). The normalization hypothesis applies on precisely this diagonal pullback and makes the second projection equal to the first. This checks injectivity without assuming that U_i -> S is a monomorphism.

Step 3 uses the statement of lem-a1-representable-etale-fppf-local-lifting: its pullback scheme comes with a surjective etale projection and an actual atlas lift. Its hypotheses are satisfied by the assumed atlas q and the fppf sheaf F. Pulling back the coproduct's open components gives the pieces of that lift; open immersions are etale and etale maps compose by the cited Mathlib leaf. The definitions of etale and fppf then verify that the resulting family covers. The fibre-product definition gives r_j from the two base maps. The explicitly assumed base compatibility and qs=qt prove the two equations for c_j. No quotient construction theorem is invoked under stronger hypotheses than available.

Step 4 uses the fppf-is-fpqc node literally on this family, then the full statement of representable fpqc descent to glue the compatible c_j into a scheme morphism. Their compatibility is the preceding injectivity calculation. That descent statement allows arbitrary schemes and arbitrary fpqc covering families, so no quasi-compactness of T, finiteness of I, affineness of intersections, or separation of X_i is added. Its uniqueness clause applied to target S and target U_i checks that the glued map respects the required base structures. The sheaf definition's equalizer clause, together with F being an fppf sheaf by the algebraic-space hypothesis, gives q_i(c)=z. Naturality of the inverse follows from the explicit uniqueness, so sectionwise bijections really yield the claimed isomorphism.

Step 5 is the direct transition formula: theta_ij(x,(u_i,u_j)) has the same quotient coordinate z and the required new base coordinate u_j. Injectivity from Step 2 uniquely identifies it with a_j inverse of (z,u_j). This proves the precise specified transition rather than merely an unspecified isomorphism. It cites no new fact beyond earlier steps and the item's hypotheses.

Step 6 checks the final covering assertion on every scheme test. The definition of etaleness/surjectivity for the representable atlas provides P -> T; the coproduct lemma provides its open cover by the pullbacks of X_i. These are the scheme-test pullbacks of q_i by the fibre-product universal property. Etale composition makes each projection etale, and their joint surjectivity follows from covering P and surjectivity onto T. This proves the family's covering property, and does not incorrectly assert that each individual q_i is surjective.

Edge cases: an empty test has unique maps where required, with all equalities tautological; I empty forces V and F empty by the assumed surjective atlas, so the assertions hold; an empty chart X_i is recovered as an empty base change by the same transport argument. For a cover with repeated/non-monomorphic U_i, U_ii may be larger than U_i, which is why Step 2 uses only the diagonal. For the trivial single identity cover, theta normalization makes the construction the identity. There is no use of a globally chosen chart for a section or a connected-test assumption.

Against B--E: all new-node checks are vacuous; none was created. The item retains source, original search records, ancestry, and import metadata; no Lean was written or compiled. Current searches used only msearch.py, and their logged query texts are copied exactly. Read the Zariski open-cover hypotheses in Mathlib RelativeGluing.lean and Sites/Representability.lean and the generic pullFunctor result: none recovers etale quotient charts as required. Every non-elementary external input is an existing cited statement; citations.json quotes that statement verbatim. Every step is under 2000 characters. The central chart-recovery argument remains in the item, so this is not a relabelling or movement of the conclusion into a child node. No node created or modified outside the item, and no circular dependency is introduced by a new lemma.

## Validation

Server review_split: PASS, 0 new nodes; the generic local-lifting tool use was accepted by the route check. Required deliver.py --no-push completed with exit 0 and OK (not pushed), commit c028e735a2f; server preflight passed (including DAG and split checks). Direct delivery is authorized by this worker brief; the maintainer performs the independent subsequent review.
