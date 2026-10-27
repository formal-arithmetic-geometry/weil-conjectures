# Stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-local-dimension-chart-invariance.json: item split into five steps, no new nodes, no Mathlib match.
- citations.json: a verbatim statement quote for every step/node citation.
- searches.jsonl: the five searches actually run through msearch.py. The item's earlier search records were retained; the new logged searches independently check the same absence.

## Attachments

None for this item. Searches for its exact blueprint tag and AlgebraicSpace in lean/WeilConjectures found no project declaration stating it. The existing RingHom.Etale.ringKrullDim_localization_eq in WeilConjectures/RingTheory/Etale/LocalDimension.lean belongs to the already existing lem-sc-etale-local-dimension, so no duplicate node was made. I read that declaration and its proof; it treats ring localizations, not chart independence or existence on algebraic spaces.

## WANTED

None. All mathematical sources used are present locally.

## Problems found

No statement error or source error was found. The item was statement-only and had no proof. Its blueprint ancestor command returns None: the existing created.item chain has no recognized imported blueprint ancestor. I retained that computed value and its existing detailed from.place/via provenance rather than inventing an ancestor. The unit record names sec-six-functors while the item's fixed chapter is sec-six-functors-basics; both existing fields were retained. The latest direct-image proof is now under sec-six-functors-basics/sk-thm-sf-ctf-stability and has the identifier det-thm-sf-ctf-stability-direct-images; its clause (3) was read. This supporting dimension comparison does not replace any step of that unit's route.

## Unfinished work

None for this split. Existing dependency nodes retain their own current stage status. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes. The whole DAG was searched by 0BAM, 04NA, 04N2, 04N8, local dimension and chart keywords; blueprint_refs.py search was run for dimension/etale and local ring/dimension. The hits involving dimension concern schemes or other dimension bounds; none states a needed new fact absent from the existing inputs. In particular lem-sc-etale-local-dimension already supplies the exact algebraic equality and lem-a1-space-point-open-calculus already supplies common fibre-product points. The quasi-separated atlas-topological-dimension node is not used: it has additional hypotheses and concerns topological dimension rather than the local-ring dimension in this item.

## Review by Q32

I read Stacks spaces-properties.tex Tag 0BAM (lemma-pre-dimension-local-ring), the following definition 04NA, and its cited general germ lemma 04N2. That germ lemma says its proof is omitted; the delivered proof writes out the common-refinement argument instead of citing omitted details. I read descent.tex 04N8, which reduces scheme stalk dimension to prime localizations, and more-algebra.tex 07QP with its flat going-down and discrete-fibre proof. There is no Noetherian hypothesis in either lemma. For the geometric comparison I read spaces-properties.tex 03H4 and 03H5, including the common field extension argument and the scheme-point identification preceding them. For the stalk comparison I read schemes.tex 01HV(6) and the open-subspace stalk statement 01HF. There are no new nodes whose sources require a separate review.

Step 1 uses the actual definition of algebraic space, which gives a representable surjective etale atlas, and the exact point-surjectivity clause of lem-a1-space-point-open-calculus. A surjective atlas therefore has a point above x; this is not inferred from the definition of topology. Step 2 uses the actual fibre-product existence statement of lem-trf-space-fibre-products-etale-covers and the scheme-test definition of representable etaleness to obtain the scheme R and its two etale projections. Its point r comes from the explicitly stated surjection in lem-a1-space-point-open-calculus. Thus it does not assume either of the original charts is a surjective atlas, nor that a topological fibre product equals the point set of a scheme fibre product.

Step 3 uses the affine-local description explicitly included in def-weil-etale-morphism: near each r the scheme morphism is given by an etale ring map. For each projection the chosen affine neighborhoods may differ. The contraction of the prime of r is the prime of w_i because that is the point map of the affine scheme morphism. The statement of lem-weil-pbc-affine-open-stalk-localization explicitly provides the isomorphism between the prime localization and the ambient stalk, with no finiteness assumption. The statement of lem-sc-etale-local-dimension then gives exactly the equality needed for those primes. Preservation of prime chains by an isomorphism is written out, so no additional dimension theorem is implicit. I did not invoke the proof of any dependency as an unstated extra conclusion.

Step 4 takes only transitivity of the two dimension equalities and the chain definition in def-weil-pbc-krull-dimension-ring. A nonzero local stalk has a proper prime maximal ideal, so its dimension is not minus infinity. The chosen chart value exists, and every other chart has that value, proving uniqueness. Step 5 compares to the identity chart on T; the identity ring map is etale in the affine definition. No additional theorem about dimension on schemes is needed. Both final steps are elementary consequences of the preceding work and the cited definitions.

Small cases checked: empty X has no x, so the pointwise assertions are vacuous. For Spec k and any nonempty etale chart above its point, each local dimension is zero. For a positive-dimensional local scheme, using its identity chart gives its stalk dimension and does not confuse it with the dimension of a neighborhood. Disconnected and nonsurjective charts are allowed in step 2. Infinite local dimension is preserved by 07QP without finite subtraction or an induction on dimension. The fibre product is representable even for a non-quasi-separated algebraic space; its affineness or quasi-compactness is never assumed. No normality, finite type, or finite-dimensionality hypothesis was introduced.

I checked delivery-errors B--E: no new unsplit proof-bearing node, no undefined new notion, no duplicated node, no clause relabelled as a child, no missing non-elementary input, and no use of a stronger cited conclusion than its statement. Every citation quote was checked as a literal substring of the current cited statement. All five steps are shorter than 2000 characters. The four cross-unit generic tools are identified in split_report.tool_uses for the maintainer's review, not granted top-level tool_uses by this worker. The Mathlib searches returned scheme etaleness, affine charts and etale loci; these do not supply an algebraic-space theorem. Loogle returned no result, and the logged grep returned no algebraic-space/chart dimension declaration. Search results were read and are recorded as actually returned.
