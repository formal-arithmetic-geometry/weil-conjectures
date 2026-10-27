# Q73 stage-1 delivery: lem-sfb-nodal-surface-flat-hartogs

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-surface-flat-hartogs.json: statement, split into six steps; the statement is unchanged. Added the polynomial, quotient, Noetherian ring and topological dimension definition dependencies used by its objects. The proof uses existing nodes only. The renewed Mathlib searches find no exact match or one-line specialization of this whole statement.
- citations.json: fourteen step/node pairs, each with the complete verbatim statement of the cited node.
- report.md and searches.jsonl: report and actual search-command records. write_split.py is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, Hartogs, nodal surface, and uniformizer terminology. No declaration states all clauses. Existing depth-two Hartogs declarations concern locally Noetherian schemes and do not cover arbitrary flat T here. They were not treated as finished proofs of this item.

## Literature

WANTED: literature/alper-halpern-leistner-heinloth-cartan-iwahori-matsumoto.pdf, Section 2 Claim 2, printed p.2, for lem-sfb-nodal-surface-flat-hartogs.

The named file is not locally present. I read the authors' PDF at https://sites.math.washington.edu/~jarod/papers/iwahori.pdf, printed p.2, Claim 2: its regularity/codimension-two input and equality of functions are exactly the motivation for the item. Claim 2 does not state the arbitrary flat-base version, and its vector-bundle existence assertion is stronger than the Hom assertion here; neither is claimed merely by citing that paragraph. The proof_origin is explicitly agent, with the flat-base argument written out from the existing Laurent-intersection and flat tensor statements. No document was downloaded or written into the repository.

Read local Stacks algebra.tex, lemma-flat (00HD), lemma-tensor-localization (00DK) and lemma-tensor-product-localization (00DL); schemes.tex, lemma-spec-sheaves (01HV), lemma-morphism-into-affine (01I1), lemma-standard-open-affine (01I3); morphisms.tex, lemma-flat-characterize (01U5); properties.tex, lemma-characterize-integral (01ON) and lemma-dimension (04MU). The item is not using any SGA source.

## What was wrong or incomplete

The item had an empty proof. Its assertion is correct, including without a Noetherian hypothesis on T; there is no statement dispute or silent weakening. The key potential gap would be applying Noetherian depth/Hartogs directly to T. Instead the exact sequence over B is tensored with each flat affine chart. Also the map B_s direct-sum B_t to B_st is not claimed surjective: only its kernel is used, which is all flat exactness and sheaf gluing require.

The existing localization-tensor node's source metadata calls its statement Tag 00DE; the local tag table identifies 00DE as hom-from-tensor-product. Its actual statement is the correct localization tensor formula, supported by 00DK (lemma-tensor-localization), which I read and cite in the proof step's source. I have not edited that other node.

The item's blueprint ancestor is already null in the repository; blueprint_refs.py ancestor confirms null. I retained its full from.place and via history rather than fabricating an ancestor. I read the current latest chapter, sk-thm-sf-ctf-stability/_section.md, and direct-images.proof.md. The latest direct-images proof is formulated through proper base change and the open-coefficients results; it does not itself assert this elementary surface input. This split realizes the final supporting sentence already recorded in from.place, leaving the chapter/unit route untouched. It is not the unit's key statement, so no unit realization file is changed.

## Not duplicates

No new nodes were created. Whole-DAG title/statement searches for nodal, binomial, Laurent intersection, Hartogs, regular local geometry, flat exactness, and affine sections located the exact existing inputs lem-sfb-dvr-binomial-local-geometry and lem-sfb-binomial-laurent-normal-form. These are cited rather than renamed or recreated. The other generic inputs likewise already exist. Whole-blueprint searches via blueprint_refs.py for Hartogs, nodal surface, flat Hartogs and the polynomial expression found no exact blueprint equivalent of this full item; same_as remains []. A broad st- search returned unrelated matches, which were not listed as equivalents.

## Review by Q73

I checked delivery-errors B through E against the final files and the sources above. There are no new statements to test independently, no new unsplit nodes concealing a proof, and no Mathlib leaves whose declaration or line is being guessed. Every renewed search was actually run with msearch.py, and its query is copied from searches.jsonl. I read both semantic-search result sets and the LeanSearch results: flatness stability and affine uniqueness do not imply the item in one line. The regular-local Loogle results are structures, basic localizations and polynomial permanence, not nodal Hartogs. The grep nodal hits are interpolation polynomials. A second wording and the regular-local grep also find no whole-item match. Inherited search records remain intact.

For step 1 I read the complete statements of lem-sfb-dvr-binomial-local-geometry and lem-sfb-binomial-laurent-normal-form. The former genuinely includes all local dimension bounds, the dimension at the origin, regularity away from it, and regularity at it for e=1. Since pi=st, its ideal (pi,s,t) equals our (s,t). The latter genuinely supplies an injection into K(T) and the two Laurent rings; A is a domain and pi is nonzero by the cited DVR definition. The domain-spectrum theorem explicitly supplies integrality, rather than just a generic point. The regular-scheme definition contains the locally Noetherian/all-local-rings characterization; Noetherianity is already supplied by the binomial geometry statement. The dimension-local-rings theorem explicitly supplies the supremum, so the global dimension conclusion does not rely on an unstated equidimensionality theorem. Its use from another unit is declared in split_report.tool_uses as generic dimension theory.

For step 2 the same normal-form statement really says the intersection equals B, not just that B embeds. The common fraction-field embeddings let equality in B_st be read as equality in K(T). A matching pair is therefore one common element and comes uniquely from B. This is a short kernel calculation from the cited intersection, so it is elementary; it does not recreate an intersection lemma or assume surjectivity of the difference map.

For step 3 I opened the flat-affine criterion, flat tensor exactness, and principal localization tensor statements. Each says exactly what is used: C is flat over B for every affine V in T, the initial zero remains exact under tensor, and C tensor B_s is canonically C_s (with the displayed fraction formula). The binary direct-sum map is written explicitly rather than hidden in a new node. Its formulas show that the maps stay diagonal and difference maps. This works for non-Noetherian C and makes no assertion that general base change preserves kernels.

For step 4 I read the spec-module-tilde-sections statement: taking N=C gives the structure sheaf on the principal opens and the actual restriction maps. The local-ring-map argument identifies the pulled-back opens. The two-open sheaf axiom therefore gives exactly the already-computed kernel. Local inverses glue because uniqueness holds on affine subopens of intersections; no intersection of arbitrary affine opens is assumed affine. This proves an isomorphism of sheaves on every open, not just an equality of global section rings. The work beyond the cited principal sections formula is a direct use of the sheaf axiom, so the step is elementary.

For step 5 the finite locally free definition provides a common refinement trivializing M and N, with finite ranks which may vary. Basis images are the matrix columns, so each entry extends by step 4. The same injectivity forces agreement on overlaps and proves uniqueness. This is elementary from the definition and the proved function statement; it neither assumes vector bundles themselves extend nor introduces a node restating this clause.

For step 6 the affine-morphism definition makes q^{-1}(V) affine, while the affine adjunction explicitly applies to an arbitrary locally ringed source, hence also to V intersect U_T even though it need not be affine. I checked the base condition: D to C is a C-algebra map because restriction and its inverse fix the structural images of C. Uniqueness on affine subopens gives overlap agreement, so sections glue on T. The adjunction's naturality ensures that the obtained restriction is the original section. This avoids using the false principle that agreement on global functions determines maps to an arbitrary non-affine target.

Small cases checked: A=Z_(p) and A=k[[pi]], including residue characteristic two, satisfy every used hypothesis; the normal-form argument requires neither completeness nor algebraically closed residue fields. A field is not a DVR under the stated definition, and pi=0 is excluded. The special closed-point base change T=Spec k is not flat: it would make U_T empty and the asserted function isomorphism false, which confirms why flatness is essential rather than silently discardable. Flat localizations of B, the generic field, arbitrary non-Noetherian flat polynomial extensions of B, and the empty scheme are all covered. For zero rings and empty charts the exact sequence is zero and the unique section/rank-zero conclusions have the expected meanings. I did not infer normality or regularity of T from flatness.

All six proof steps are below 900 characters (none approaches 2000). The only non-elementary operations are the existing geometric, tensor, localization and affine-adjunction statements named in uses. Four elementary steps perform concrete kernel, sheaf, matrix and ring-map assembly from them. proof_deps is exactly the union of uses, and citations.json contains a verbatim complete statement for each of the fourteen citations. No data or proof is hidden behind a new definition, no clause is pushed into a renamed node, and no dependency depends back on the item as far as the local graph check and server preflight will verify.

## Unfinished work

No mathematical part remains. The required server dry run and direct push are the final delivery operations; their outcomes are recorded below after execution.
