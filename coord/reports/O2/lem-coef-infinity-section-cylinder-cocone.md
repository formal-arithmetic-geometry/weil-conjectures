# lem-coef-infinity-section-cylinder-cocone

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-section-cylinder-cocone.json`: statement item split into eight proof steps, statement unchanged; Mathlib searches found no match.
- `citations.json`: exact passages from every statement cited in each proof step.
- No new DAG nodes and no new Mathlib leaves. The auxiliary `write_split.py` only constructs the sandbox JSON and is not a delivery file.

## Attachments

None. Searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` for the blueprint id, section-cylinder terminology, right-fibration terminology, and lifted cocones; the only lifted-cocone hits are ordinary categorical algebra/limits, not the quasicategorical statement. The upstream-name table has no item entry. The item has no pre-existing completed Lean audit. No Lean file was written or compiled.

## WANTED

WANTED: Lurie, Higher Topos Theory, Corollaries 2.1.2.7, 2.1.2.9, 2.1.2.10 (right-handed forms), Proposition 2.2.3.11, Corollary 2.3.2.4, and Corollary 5.3.5.4, for lem-coef-infinity-section-cylinder-cocone. The PDF was consulted online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; it is not archived in literature/. No Stacks tag states this right-fibration result. The proof is correctly marked agent-written: Corollary 5.3.5.4 is the surrounding application and does not state this auxiliary lifting calculation.

## Corrections and scope

The imported item had a statement and searches but no proof. I preserved its statement and provenance, including the allowance that the transported section point is identified coherently rather than by equality in a separately chosen model. I supplied the strict-versus-homotopy-fiber comparison explicitly; without it a strict cylinder lift would only establish a different assertion. No statement dispute, no new hypotheses, and no change of coefficient category or of a base-change map is involved.

The general section/limit results in `lem-coef-right-fibration-section-limit` and `lem-coef-right-fibration-cone-section-criterion` do not assert this fixed-cylinder/fixed-apex mapping-fiber calculation. `lem-coef-infinity-constant-source-section-comparison` addresses maps out of a constant diagram and has no fixed-base lifting fiber. `lem-coef-infinity-cartesian-mapping-fiber` could be useful after proving an exponentiated edge cartesian; it is not an attachment or duplicate of this statement. I used existing pushout-product, exponential, pinch and Kan pullback statements directly instead of creating those specializations as new nodes.

## Not duplicates

No new nodes. Whole-DAG keyword searches and `tools/blueprint_refs.py search 'section cylinder cocone'` and `search 'right fibration'` found no blueprint duplicate. `tools/blueprint_refs.py ancestor` confirmed the retained ancestor `prop-coef-integral-exceptional-adjoint`. The main-20261015 proof's second paragraph is the derived mapping-complex adjunction: this item lies below the extracted presheaf/Ind foundation rather than changing that unit step. The chapter and unit records were read and not edited.

## Review by N2

I read delivery-errors B–E against the actual statement and each proof dependency. There are no new statement-only nodes to audit, no clause of the item moved into a new lemma, and no unlogged Mathlib query. I read the five new search results in `searches.jsonl`: Loogle and the scoped grep returned zero hits; LeanSearch returned ordinary LiftableCocone and Over/Under constructions; the two LeanFinder phrasings returned ordinary fibered-category morphism lifts and generic model path-object declarations. These do not have the objects or conclusion here. The imported search records were preserved. The new entries reproduce the tool/query text and logged result exactly.

For sources I read HTT's online printed pp.64–65, including the pushout-product and exponential corollaries and the homotopy extension lifting statement, and pp.403–404 around the Ind criterion. I read the current blueprint ancestor proof's paragraph 2. The cylinder proof is my expansion using existing DAG statements, not an alleged quotation from HTT. I opened the complete statement of every node in proof_deps before using it. The source references attached to the eight steps indicate which part is that expansion.

Step 1 uses the classification node's mapping-space formula, the constant-product clause, its dual right-fibration clause and pullback compatibility; these apply on any small simplicial base, including K, not merely a quasicategory. Pullback stability is proved by projecting each horn square, using exactly the fibration definition. Thus the section space is Kan for the arbitrary shapes in this item.

Step 2 takes exactly the right-anodyne pushout-product statement, not a false assertion that arbitrary monomorphisms are right anodyne. It writes the union domain of the transposed horn problem. The exponential node applies because this union inclusion is right anodyne and q is a right fibration. The resulting restriction map is right fibred; the space-fiber node applies because its target is already Kan by Step 1. This justifies the Kan fibration assertion and subsequent base changes.

Step 3 checks the endpoint direction: {1}, not {0}, is Lambda_1^1. Its product with K is right anodyne. The exponential node therefore gives a boundary-lifting map on cylinder lifts with final section fixed. Kan-Quillen's boundary characterization says that its pullback T to the fixed pair is a trivial fibration, hence T is nonempty, Kan and contractible. The initial restriction r is a pullback of the both-endpoints restriction from Step 2, so it is a Kan fibration even though its own underlying subset inclusion is not claimed right anodyne.

Step 4 checks contravariance: applying X to the cocone cylinder gives a transformation from the constant X(b) diagram to Xp^op, not its reverse. Under classification a section H_0 is a transformation from the terminal diagram to this full interval diagram. Its naturality square identifies u with X(lambda) applied to the constant point x. Classification expressly preserves composition, pullbacks and higher mapping data. This is the coherent endpoint identification allowed in the item's statement; I do not infer equality just from the values at vertices of K.

Step 5 checks both mapping-space models. The enhanced-functor node applies for arbitrary K. The inner pushout-product node proves Fun(K,q) inner fibred by the displayed transposition; no unproved right-fibration exponentiation for arbitrary inclusions is invoked here. The last clause of the isofibration-exponentiation statement requires only an inner fibration for its fixed-endpoint arrow-space Kan fibration, which is precisely what we have. Pinch is natural under Q and is identity on edge vertices, so its chosen basepoint is the exact cylinder lambda. The homotopy-fiber detection theorem with weak equivalences on total spaces and bases gives the fiber equivalence. The strict/path pullback theorem then applies to the arrow-space Kan fibration. Currying gives exactly L, retaining both endpoints and every parameter simplex.

Step 6 uses the strict/path pullback theorem with u=t and v=r; it suffices that r is Kan fibred. The invariance theorem is applied to a strictly commuting map of cospans with all three components weak equivalences: the selected point H_0 into contractible T, and the other two identity maps. This gives paths from t to u, so no unmentioned inversion or reversal of paths is needed. This is a routine pullback calculation, not an uncited abstract assertion about a right-fibration category of elements.

Step 7 supplies the actual prescribed-cylinder representative using the right-horn lifting property already established for r. Its value at the initial endpoint is in L. The equivalences of Step 5 imply surjectivity on components, so an arbitrary point of the homotopy fiber has a strict-cylinder representative in the meaning of an equivalence of spaces; literal equality of separately chosen simplicial models is not asserted.

Step 8 checks naturality on the actual maps before inversion, by writing the precomposition map on K times the interval times a parameter simplex. The choice of H_0 is kept in contractible T, so changing it includes its endpoint path and all higher coherences, rather than claiming a canonical strict choice. The relative parameter fillers use the same pushout-product and exponential theorem; those statements explicitly allow arbitrary small simplicial sets. None of these steps exceeds 2000 characters or hides an independent comparison lemma: the two comparisons are the cited generic Kan pullback and pinch results, specialized with their objects and maps written out.

I tested K empty (every space is a point), q the identity (unique lift/path), q:I to a point with I a disconnected Kan space (both spaces empty for incompatible components), K a point with a nontrivial fiber loop space (the full path space is retained, not just existence or pi_0), and arbitrary non-quasicategorical K such as a boundary simplicial set (all arguments use its products and inclusions, never horn filling in K). All simplicial sets remain small in the fixed universe. No SGA source is used.

The two off-unit statements declared in split_report.tool_uses are generic enhanced-functor calculus and right-fibration-over-space calculus. They supply foundational functor/Kan facts, and do not replace a step of the coefficient unit route.

## Unfinished work

None for this one-level split. Stage 2 and proof compilation remain outside the brief. Server dry-run and delivery results are the authoritative validation of the submitted DAG files.
