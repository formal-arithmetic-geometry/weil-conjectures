# Stage-1 report: lem-coef-coherent-diagram-universe-naturality

## Files written

- `dag/nodes/sec-six-functors/lem-coef-coherent-diagram-universe-naturality.json`: statement, split into nine proof steps; no Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the 31 step/node citations.
- This report. `searches.jsonl` is the search command's own log; `write_split.py` is sandbox-only preparation, not a project file.

There are zero new nodes and zero Mathlib leaves. The item's statement, source, chapter, unit, ancestry, creation record and other protected metadata are unchanged. It is not the unit's key node, so no unit realization record is changed.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id, homotopy/coherent diagram terminology, Dwyer--Kan, rectification and coherent-nerve spellings found no candidate project declaration. No upstream-master sorry declaration has been treated as a proof.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Proposition 4.2.4.4, Remark 4.2.4.5, Theorem 4.2.4.1 and Proposition A.3.3.2, for lem-coef-coherent-diagram-universe-naturality. Not archived in literature/; read the author's HTT.pdf online. The item source calls the same reference highertopoi.pdf.

WANTED: Jacob Lurie, Higher Algebra, Construction 1.3.4.18, Theorem 1.3.4.20 and Remark 1.3.4.16, for lem-coef-coherent-diagram-universe-naturality. Not archived in literature/; read the author's HA.pdf online. Definition B.2.1 and Theorem B.0.20 are used through the existing pattern-model statement, which already records them.

No Stacks tag states this enriched rectification/universe result. No SGA source is used.

## What needed repair or clarification

The incoming node has a correct statement and an empty proof. Its explicit universe naturality is not a separately numbered assertion of HTT: its content must be checked on evaluation and actual cocones. The proof is therefore marked agent-written, with the precise source interfaces indicated, rather than attributed to a nonexistent theorem.

An objectwise ordinary functorial fibrant replacement need not be simplicially enriched. I did not apply such a functor objectwise to an enriched diagram. Instead, projective diagram models give a replacement of the whole enriched diagram; a cocone is first encoded as a diagram on an enriched index with an adjoined terminal object. Replacing the entire latter diagram retains its legs and apex together.

Another potential gap is the smaller-to-larger inclusion on projectively cofibrant diagrams. The common pattern generators in the existing universe-comparison node, free enriched-diagram generators in the existing coherent-diagrams node, and the explicit degreewise colimit construction show that every smaller projective cell presentation remains valid. No claim that inclusion is a Quillen adjunction is needed.

## Searches and reuse

Read the existing item and all the cited statements. The whole-DAG statement/title scan and searches for rectification, Dwyer--Kan, evaluation-induced comparisons, universe inclusion and projective cofibrancy led to the existing enriched-diagram-rectification, projective-model-calculus, diagram-size-generation, coherent-nerve and localization nodes. `tools/blueprint_refs.py search` was run for `rectification`, `coherent diagram`, `Dwyer`, `enriched diagram` and `universe`; there was no duplicate blueprint statement. The ancestor command confirms prop-coef-integral-exceptional-adjoint. Its source proof paragraph 2, the mapping-complex adjunction before the derived inverse limit, was read; the inherited operadic-foundation ancestry is retained.

All fresh Mathlib searches used msearch.py, and their exact query/result records are appended in the item and in the command-generated searches.jsonl. Two different LeanFinder phrasings, LeanSearch, Loogle and source grep were run. Hits included CategoryTheory.SimplicialNerve, SSet.uliftFunctor, ordinary universe-lift colimit preservation, ordinary homotopy-category localization replacements and enriched-functor-category composition projections. I read SimplicialNerve.lean (definition at 193; its projects at 28--35 still list the locally Kan/quasicategory theorem), SimplicialSet/Basic.lean:73--74, Limits/Preserves/Ulift.lean:66--76, ModelCategory/CofibrantObjectHomotopy.lean:250--280 and Enriched/FunctorCategory.lean:147--180. These supply useful definitions or ordinary categorical facts, not the full assertion of this item. No new auxiliary lemma is introduced merely to repackage such a fact.

## Not duplicates

No new node was created, so there are no new/existing-node pairs requiring distinction.

## Review by NA

I read delivery-errors B through E in full and checked this split against the actual source interfaces. HTT Proposition 4.2.4.4 compares the coherent nerve of strict enriched diagrams with the infinity functor category, Remark 4.2.4.5 permits the projective presentation, and the proof of Theorem 4.2.4.1 explicitly handles the natural transformation induced by a strict cone before testing its universal property. HA Construction 1.3.4.18 uses ordinary cofibrant objects on one end and bifibrant objects on the other; Theorem 1.3.4.20 and Remark 1.3.4.16 supply the localization identification. This supports the use of whole localization functor categories rather than a statement only about objects or the homotopy category. The extra universe verification is written out here, not claimed as a quotation of those sources.

Step 1 uses the size convention, the realization-and-homotopy definitions in def-cbc-enhanced-diagrams-cones, and the actual Dwyer--Kan/realization definitions in lem-coef-coherent-nerve-comparison. Every function graph between fixed smaller sets is already smaller; this applies also to continuous cube maps and the subsets testing continuity. Thus no unquoted theorem about model equivalences changing universes is hidden in that step. Both the local weak equivalences and the equivalence of component categories in the DK definition remain the same. The local Kan condition is a fixed collection of horn-lifting tests.

Step 2 uses exactly the monomorphism cofibrations and sharp mapping formula in categorical-pattern-model-calculus, fibrancy compatibility in finite-pattern-universe-comparison, and the definition/functoriality of the coherent nerve in coherent-nerve-comparison. These show that all objects are cofibrant, smaller fibrant objects remain so, and the sharp mapping simplicial sets agree with their composition. This constructs the actual simplicial inclusion underlying the stated j.

Step 3 reads the common generating cofibrations from finite-pattern-universe-comparison, the free-diagram generators and their cell-closure characterization from simplicial-model-coherent-diagrams, the marked tensor/sharp Hom adjunction from categorical-pattern-model-calculus and the objectwise colimit assertion from enriched-diagram-size-generation. On resumption I tightened the scope: J is locally Kan, its counit is Dwyer--Kan by the explicit statement of enriched-diagram-rectification, and the free-generator statement consequently applies with K equal to its coherent nerve. The projective structure itself is also cited directly from simplicial-projective-model-calculus, which states its existence for every small simplicial index. Both I and the terminal extension J used later satisfy the locally Kan condition. The smallness conditions hold for every index J used here. Coproducts, quotients and marking images are explicitly identical in both universes, so the cell presentation remains a valid one. This is an elementary specialization of those generator statements, not a new standalone lemma.

Step 4 uses the objectwise projective fibrancy/weak-equivalence statement, their pattern-universe comparison, and the exact enriched-end description from enriched-diagram-size-generation. It checks families of mapping simplices and their naturality equations, not just individual components. Thus it really gives a simplicial inclusion on bifibrant diagrams.

Step 5 uses evaluation preserving bifibrant objects from simplicial-projective-model-calculus and the evaluation-induced equivalence explicitly stated by enriched-diagram-rectification. The locally Kan target I and DK map u meet that statement's hypotheses; both pattern models are combinatorial simplicial model categories by the already cited pattern-model node. The explicit coherent nerve and coherent Fun definitions make the square an equality in every degree: evaluation is the same component followed by the same action map. This is the argument for higher naturality; I did not substitute a vague assertion that naturality is automatic.

Step 6 uses the full infinity-localization property and agreement of its inverse on bifibrant objects from simplicial-model-nerve-localization, together with the diagram model structures. Applying the property first to the ordinary bifibrant subcategory, which itself induces a localization equivalence by that same statement, identifies the square on all strict presentations. This also checks the coherence of transformations, rather than inferring it from agreement of objects.

Step 7 constructs the enriched terminal index explicitly; its functor laws are exactly the enriched naturality equations of t. The cited free-diagram and objectwise-colimit statements show that restriction of projectively cofibrant diagrams to I is cofibrant: the only extra generator restricts to the identity of the initial diagram. Objectwise fibrancy and weak equivalences restrict as well. This is a few-line generator argument, so it is kept as an elementary step rather than a new node.

Step 8 applies the functorial projective model factorizations to H as a single diagram. Its first replacement is cofibrant, its second is bifibrant, and the restriction is bifibrant by step 7. The apex is bifibrant by the evaluation theorem in simplicial-projective-model-calculus. The structure maps of BH define a genuine enriched natural transformation to the constant diagram, hence a functor I times [1] into bifibrant model objects. The coherent nerve/product formula makes its image an actual K times Delta^1 cocone. For this last identification I explicitly use the counit from coherent realization of N_hc J, which enriched-diagram-rectification states is DK because J is locally Kan. Restriction along the explicit I times [1] to J and evaluation at the apex commute with enriched evaluation, so the zigzag identifies the actual cocone through the named localization comparison. This avoids both a non-enriched objectwise replacement and an extra cofibrancy assumption on a constant diagram.

Step 9 applies the already proved comparison also to the enriched index J with its adjoined terminal object. Every object and every arrow in the replacement zigzag remains smaller and a weak equivalence. Both coherent cocones therefore are represented by the same maps of mapping simplices. The stated natural isomorphism of common fibrant replacements identifies the specified apex maps A to RA, and the formula for each leg is literally F_i to A to RA in both universes. The constant coherent diagram is checked on its identity action maps. This verifies the actual cocone clause without using a colimit property.

I checked edge cases: K empty (even when I has objects with empty/nonempty possibilities constrained by u), I empty, the empty categorical-pattern cone shapes, no pattern cones, the initial marked object, t an identity constant cocone, and a noncolimiting cocone. For K empty and a DK-equivalent I, essential surjectivity forces I empty, and the cocone encoding is just its apex; no nonempty test was silently used. Empty pattern shapes are covered by the existing universe-comparison hypothesis, without dropping their terminal-object conditions. Noncolimiting cocones never enter a mapping-space equivalence test for colimits. No finite bound on K or I was imposed; their smallness is enough, whereas finiteness of the pattern shapes is used only through the common-pattern comparison.

B: no new node, proof-bearing definition, unnamed object or Mathlib leaf was introduced. C: each cited node was opened and its statement read; citations.json copies actual substrings, and the non-elementary comparison/localization inputs all have named dependencies. The added proof edges stay within the unit except for definition nodes, which supply terminology. D: the steps carry the entire naturality argument rather than moving its clauses to new nodes. E: the two universes, fixed pattern, full scaling, finite pattern cone shapes, small enriched indices and actual sharp mapping objects are preserved throughout. No statement correction, hollow definition, source-route replacement or SGA citation occurs. All nine steps are shorter than 2000 characters, and I also checked the elementary cell and terminal-index arguments for hidden non-elementary subclaims.

## Unfinished work

No mathematical part of this one-level split remains open. The existing cited statement nodes retain their own independent stage-1 status; they were not edited or resplit. Server dry-run results and the delivery result are recorded by the required tools.

## Resumption validation

The preserved split passed the required server dry run (preflight, DAG and split review) at 7ce515c40f. I then tightened step 3 as described above and added its two verbatim citations; the final dry run and push must validate these exact revised files. No search was repeated and no new node was created.
