## Worker report

Files written: dag/nodes/sec-six-functors/lem-coef-fibrant-pullback-mapping-invariance.json (statement, split; no full Mathlib match), citations.json, searches.jsonl, and this report. The sandbox initially contained only dispatcher markers; no earlier split, report, search log or interrupted delivery existed to resume. Only sandbox files were written. The helper write_split.py records this attempt's construction.

Attachments: none. Searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the blueprint id, fibrancy, simplicial models and coherent nerves found no exact project declaration. No Lean or build commands were run. Master is not treated as proof evidence.

WANTED: Jacob Lurie, Higher Topos Theory, Remark A.2.4.5 and Appendix A.3.1, for lem-coef-fibrant-pullback-mapping-invariance; archival copy under literature/. I read the Harvard-hosted PDF online (printed p.816, PDF p.834, Remark A.2.4.5); it explicitly allows the fibrant-object alternative to right properness. The proof is marked agent reconstruction rather than a proof from an archived document. The source is https://people.math.harvard.edu/~lurie/papers/HTT.pdf . No Stacks tag states this homotopical result and no prohibited SGA source is used.

The item had an accurate statement but no proof. Its original statement, source, ancestry, unit, and maintainer metadata are retained. Its hypothesis that every object is cofibrant is used to make D and E legitimate test objects in the last step. No statement dispute or unit-route correction is needed. The six steps prove fibrancy, Kan/fibration properties, homotopy invariance of Map(T,a), strict preservation of this pullback by Map(T,-), the mapping equivalence, and the final equivalence edge. All step uses are collected exactly in proof_deps. Nothing remains unfinished in the split; its existing dependency nodes remain separate stage-1 work.

## New nodes

None. In particular, neither a clause of this item nor its whole content was moved to a new node. There are zero new Mathlib leaves.

## Searches and reuse

The fresh msearch.py searches are recorded in searches.jsonl and appended to the item's prior searches. LeanFinder was tried with both the mapping-space formulation and the more general fibrant-base-change formulation; Loogle, LeanSearch and grep also ran successfully. Read Instances.lean:223–246, PathObject.lean:260–290, JoyalTrick.lean:68–96 and BrownLemma.lean. The pullback weak-equivalence instances require the pulled-back map itself to be a trivial fibration. They do not apply to a merely weak equivalence a, and none provides the whole item. Brown factorization instances do not state the conclusion either. The original imported Q49 searches are preserved, distinguished by their original timestamps.

Whole-DAG statement searches found lem-coef-kan-quillen-model-right-proper-core, lem-coef-kan-pullback-fibration-invariance, lem-coef-kan-homotopy-pullback-invariance, lem-coef-brown-fibrant-localization-pullbacks and lem-coef-simplicial-model-nerve-localization. I use the core's existing exact right-properness clause, rather than creating another lemma or invoking the larger Brown localization theorem. tools/blueprint_refs.py searches for 'fibrant pullback' and 'mapping spaces' returned no matching blueprint node; ancestor returned prop-coef-integral-exceptional-adjoint. I read that blueprint node's proof paragraph 2. The present node remains its technical supporting input; the unit key statement and realized fields need no edit.

## Not duplicates

No new nodes were created. Existing general tools are cited directly.

## Review by NW

I read the item's full statement, the unit sk-prop-sf-biduality-general and the sec-six-functors chapter record, the ancestor's paragraph-2 coefficient-adjunction proof, and the actual statements of all five proof dependencies. HTT Remark A.2.4.5 confirms why no right properness of M is required. I preserved each hypothesis and conclusion, including containing universes, arbitrary bifibrant T, and equivalence of the specified projection h, not merely of some replacement object.

Step 1 takes the lifting characterization of fibrations and the definition of fibrant objects from lem-coef-simplicial-model-nerve-localization. It writes out pullback stability by reducing the square to b and pairing the lift with the map to U, then writes the composition argument. U is fibrant by hypothesis. This needs no separate stability lemma.

Step 2 uses the same node's precise cofibration/fibration mapping axiom, with the initial cofibration of T. The tensor/cotensor adjunction in def-coef-simplicial-tensor-cotensor supplies the degreewise ordinary-Hom formula and the initial/terminal mapping-set identifications; its statement really includes the enriched adjunction, not merely existence of objects named tensors. All four targets are fibrant by the hypotheses and Step 1. Thus the Kan assertions and the Kan fibration Map(T,b) have exactly the SM7 hypotheses.

Step 3 uses the natural represented mapping-space comparison of lem-coef-simplicial-model-nerve-localization, not a claimed right-properness consequence of that node. def-coef-coherent-localization-interface explicitly says that q inverts W. Since T is cofibrant and U,U' are fibrant, the comparison applies to both. The inverse of q(a) gives an inverse on the represented spaces; composition compatibility is explicitly included in the cited comparison theorem. No extra combinatorial or properness assumption enters.

Step 4 uses only the actual tensor adjunction and the defining ordinary pullback. The argument is given on n-simplices and on all simplex operators; this proves that the specific map Map(T,h) is the base-change projection. This elementary identification is not made into a new node.

Step 5 cites the exact sentence 'Pullback of any weak homotopy equivalence along any Kan fibration is a weak homotopy equivalence (right properness).' in lem-coef-kan-quillen-model-right-proper-core. Step 2 supplies that fibration and Step 3 supplies that weak equivalence. The source's right properness is for simplicial sets only. I deliberately used the core, which contains no Brown-localization dependency, rather than the larger wrapper.

Step 6 uses the earlier mapping-space result for T=E and T=D. Surjectivity yields k, and injectivity gives the other inverse equation; I corrected the wording to 'precomposing' for (hk)h=h. It explicitly turns the two component equations into edges by Kan two-horn fillings and then into two coherent-nerve triangles via the thickened [2]. The nerve's thickening is stated in lem-coef-simplicial-model-nerve-localization, and def-cbc-enhanced-diagrams-cones defines equivalence by precisely these two inverse triangles. Thus no uncited Yoneda or weak-equivalence-reflection theorem is hidden in the last line.

For small cases I checked a=identity (h is the pullback isomorphism), b=identity (h is a itself), E initial when this is permitted, and empty mapping complexes. Kan complexes may be empty; nothing in the right-properness step assumes a point. In Step 6 the particular target components contain identity vertices, which is exactly why surjectivity gives k even in these edge cases. There is no claim that an arbitrary Kan complex is nonempty. Fixed universes are unchanged and no new indexing category is introduced.

Against B–E: no new statements, duplicate nodes, relabelled clauses, hollow definitions or unsupported literature tags were introduced; every cited statement was opened and is included verbatim in citations.json. Definitions are used only for elementary constructions and the two non-elementary steps cite substantive theorems. All six steps are shorter than 2000 characters; the pullback identification and inverse calculation are written out, rather than described as 'standard'. No dependency cycle is intended: the selected Kan core avoids the higher localization wrapper. The server checks will verify the actual graph. This review is the worker's own signature under the direct-delivery brief, not a claim of independent review.
