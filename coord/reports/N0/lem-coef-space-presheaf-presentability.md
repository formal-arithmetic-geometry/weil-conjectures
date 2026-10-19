# Stage-1 split: lem-coef-space-presheaf-presentability

## Files written

- `dag/nodes/sec-six-functors/lem-coef-space-presheaf-presentability.json`: statement, split into six proof steps; statement and statement dependency unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-space-yoneda-density.json`: statement, unsplit; no Mathlib match. Full mapping-space Yoneda evaluation and the small coherent density diagram.
- `dag/nodes/sec-six-functors/lem-coef-compact-small-colimits.json`: statement, unsplit; no Mathlib match. General closure of compact objects under bounded simplicial colimits.
- `dag/nodes/sec-six-functors/lem-coef-colimit-subdiagram-approximation.json`: statement, unsplit; no Mathlib match. General coherent assembly of prescribed partial colimits over bounded simplicial subsets.
- `citations.json`: 18 verbatim statement quotations, one for each step/node pair.

Three new nodes, zero new Mathlib leaves. New nodes contain statements only: no proof sketches in their statements, no proof steps or proof dependencies, and null proof origins. All introduce their universes and objects and cite the existing definitions of quasicategories, coherent diagrams, compactness and filteredness. TeX has single backslashes after JSON decoding.

## Attachments

None. I searched both read-only project source trees for the item tag and the relevant presheaf, Yoneda, compactness and subdiagram notions. The project declarations encountered concern ordinary presheaves, pro-categories, ring/sheaf objects and ordinary finitely presentable objects. None states these coherent-space assertions, so there is no attachment claim. Master is reference material, not proof evidence.

## Literature wanted

WANTED: Jacob Lurie, Higher Topos Theory, sections 1.1.5 and 5.1.2 (especially Proposition 1.1.5.10 and Proposition 5.1.2.2/Corollary 5.1.2.3), for lem-coef-space-presheaf-presentability and its existing coherent-nerve/pointwise-colimit inputs.

WANTED: Higher Topos Theory, Lemmas 5.1.5.2-5.1.5.3, printed pp. 321-323 of the March 10, 2012 PDF, for lem-coef-space-yoneda-density.

WANTED: Higher Topos Theory, Corollary 5.3.4.15, printed p. 398, for lem-coef-compact-small-colimits.

WANTED: Higher Topos Theory, Proposition 4.2.3.4, Proposition 4.2.3.8, Remark 4.2.3.9, Corollary 4.2.3.10 and proof of Corollary 4.2.3.11, printed pp. 249-253, for lem-coef-colimit-subdiagram-approximation.

WANTED: Higher Topos Theory, proof of Proposition 5.3.5.12 and Remark 5.5.3.7, for the bounded-generator accessibility argument in lem-coef-space-presheaf-presentability.

I read these passages online at https://www.math.ias.edu/~lurie/papers/highertopoi.pdf. They are not archived here; I did not download or alter literature. The item's proof is accordingly marked agent-written. The sources are infinity-categorical results for which no Stacks tag gives the required statement. No SGA source is used.

## Findings and corrections

The original item is true as written. No STATEMENT-DISPUTED, altered hypothesis or altered conclusion is needed. In particular a small ordinary category need not be nonempty or finite, and its presheaves here retain coherent transformations and higher homotopies.

A direct appeal to the general presentability of Fun(K,V) would move the whole claim to another node. Instead the proof constructs compact generators: representables, bounded colimits of them, and a filtered presentation of each arbitrary presheaf by those bounded colimits. None of the three new nodes asserts accessibility, existence of compact generators, or presentability of the presheaf category.

I corrected a potential C4 gap while assembling the proof. The existing lem-coef-infinity-yoneda-presheaf-limits explicitly gives the objectwise characterization of colimits; I do not infer coherent existence merely from that wording. Step 1 first applies the existing lem-coef-infinity-parameter-cone-extension to chosen colimit cocones at every vertex of the parameter simplicial set. Only after that extension supplies a coherent cocone does the pointwise characterization certify it as a colimit. This preserves the exact hypotheses of both nodes.

The filtered-approximation statement deliberately asserts only universe-smallness of the poset of bounded subsets. Corollary 4.2.3.11 uses a stronger relation between two regular cardinals to bound that poset by the outer cardinal. That stronger bound is not needed here and is not claimed. The new statement is extracted from the directed-union proof via 4.2.3.4 and 4.2.3.10. It explicitly allows prescribed colimiting cocones at the vertices, avoiding an unproved assertion that arbitrary choices of equivalent generator objects automatically assemble coherently.

I also wrote out the universe argument for local smallness and for the full generator subcategory, rather than invoking an uncited small-skeleton theorem for general infinity categories. In the Kan/coherent-nerve model, a small collection of presheaves takes values in a small full simplicial category of small Kan complexes, and the full coherent functor category on those values is small. Both the local-smallness assertion and the generator-subcategory assertion follow by counting actual simplicial data.

## Unfinished work

The three new statements remain unsplit, as required for a one-level split. This delivery does not claim Lean formalization or proof of those new nodes. No work on other DAG items, the fixed chapter, the unit record, a live repository or a launcher was performed. A second reader must independently review and deliver this sandbox. This worker runs only the required no-push dry run.

## Not duplicates

lem-coef-space-yoneda-density vs lem-coef-infinity-yoneda-presheaf-limits: the existing statement gives full faithfulness of Yoneda and objectwise (co)limit characterization, not the equivalence Map(h_c,F) = F(c) for arbitrary F and not a small colimiting diagram of representables for each F. These are distinct clauses, so the existing node is reused for what it actually says.

lem-coef-space-yoneda-density vs lem-pc-yoneda: the existing blueprint Yoneda result concerns representable ordinary functors and schemes; it does not assert the coherent-space evaluation equivalence or infinity-categorical density.

lem-coef-compact-small-colimits vs def-coef-presentable-infinity-category: the definition specifies compactness and accessibility but does not prove closure under bounded colimits. The new theorem applies to arbitrary locally small quasicategories with the indicated filtered colimits, with no presheaf hypothesis.

lem-coef-colimit-subdiagram-approximation vs lem-coef-infinity-grothendieck-limits-colimits: the existing theorem computes colimits in the total category of a cocartesian fibration from base and fiber colimits. It does not assert a coherent partial-colimit diagram over the bounded simplicial subsets of an arbitrary indexing shape, or its equivalence with the original colimit.

lem-coef-colimit-subdiagram-approximation vs lem-coef-small-direct-colimit-lifting: the latter is an ordinary diagram-lifting theorem for model-category small-object arguments, not a theorem assembling prescribed infinity-categorical colimit cocones on simplicial subsets.

The whole DAG has no occurrence of the precise HTT references 5.1.5.2, 5.1.5.3, 5.3.4.15, 4.2.3.4, 4.2.3.8, 4.2.3.10 or 4.2.3.11 at the time of this split. I searched the whole blueprint by Yoneda, presheaf presentability, compact objects, small colimits, kappa-compact, co-Yoneda and simplicial subset; no blueprint node states the new assertions. The returned ordinary or geometric results are not substitutes for the coherent-space statements. The three proposed ids did not exist in the shared DAG before creation.

## Mathlib search review

All searches recorded by this worker were run through msearch.py with group N0 and this item's id. The records retain the exact tool/query and the search log result, including grep subdirectories. The original item's pre-existing searches are retained. One exploratory Loogle query rejected unqualified identifiers; that query is recorded as unavailable, not as a negative result. The successful name-string search locates the actual ordinary presheaf presentability instance. No service outage is being used as evidence of absence.

For Yoneda/density I read CategoryTheory.yonedaEquiv at Mathlib/CategoryTheory/Yoneda.lean:724 and CategoryTheory.Presheaf.colimitOfRepresentable at Mathlib/CategoryTheory/Limits/Presheaf.lean:290. Their natural transformations are Hom sets and their presheaves are Type-valued. A first grep on the nonmatching CategoryTheory/Yoneda subpath was empty; subsequent logged greps found the actual files. Both semantic phrasings and the LeanSearch hits concern ordinary categories.

For compact closure I read CategoryTheory.isCardinalPresentable_of_isColimit and CategoryTheory.isClosedUnderColimitsOfShape_isCardinalPresentable at Mathlib/CategoryTheory/Presentable/Limits.lean:185,199. They bound the ordinary Arrow category and use ordinary Type-valued Hom functors. The source's infinity-categorical assertion bounds simplicial indexing sets and preserves full mapping-space colimits; it is not a one-line specialization of those declarations.

For approximation I read the entire Mathlib/AlgebraicTopology/SimplicialSet/SubcomplexEvaluation.lean, whose filtered-colimit-preservation instance at line 38 was the closest Loogle hit. It preserves ordinary filtered colimits of subcomplexes into SSet; it does not construct coherent diagrams of partial colimits in an arbitrary quasicategory. The file-target grep log has numeric entries in its `top` field because of the tool's output parser; the genuine command and its result were retained, and the file was read directly. Neither semantic phrasing nor LeanSearch supplies the required theorem.

For the item I read Mathlib/CategoryTheory/Presentable/Presheaf.lean:90-95. Its instance is ordinary local presentability of Type-valued presheaves, and does not settle this item. No new Mathlib leaf is claimed.

## Review by N0

I read the current blueprint ancestor prop-coef-integral-exceptional-adjoint, paragraph 2, whose displayed RHom and derived inverse-limit adjunction motivates the existing chain down to this item. I read the chapter and unit records and kept their route: all new statements are generic mapping-space foundations inside the same coefficient-adjunction unit. I searched the current main-20261015 blueprint and read the relevant historical ancestry; no SGA trace or purity argument is introduced. The item's blueprint provenance is retained and each child names that exact ancestor paragraph with the item prepended to its via chain.

For the item itself I read HTT Remark 5.5.3.7 and the proof of Proposition 5.5.3.6, then expanded the accessibility part using the bounded-family construction in the proof of Proposition 5.3.5.12. The general Fun(K,V) presentability result is not a new dependency that merely repeats the item. For the three new nodes I read, respectively, the evaluation/density proofs in 5.1.5.2-3; compact-colimit closure in 5.3.4.15; and the prescribed partial-colimit construction in 4.2.3.4 with the directed-union and comparison arguments in 4.2.3.8-11. I corrected the page citations to this particular online edition: density is printed pp. 321-323 and compact closure is p. 398. The source places, rather than an unrelated Stacks tag, identify the exact theorems.

Step 1 uses def-cbc-enhanced-diagrams-cones for the nerve and coherent Fun constructions and lem-coef-coherent-nerve-comparison for the ordinary nerve's quasicategory property. I opened both statements. The accessible-infinity-pullback node explicitly states that small spaces are presentable and that presentable categories have all small colimits, so its pullback clause is unused. I opened the parameter-cone-extension statement and checked P contains every vertex of B; the supplied cocones are colimits at every possible initial vertex. Its extension is exactly the required coherent cocone. I then use only the objectwise characterization actually written in infinity-yoneda-presheaf-limits. The shapes B and J are universe-small; no large-index colimit is being taken.

Step 2 again uses the explicit coherent-nerve construction and its locally-Kan quasicategory assertion. In the chosen model of small spaces the simplicial mapping complexes are the full Kan mapping complexes. For a small family of small Kan complexes these mapping complexes and all coherent-nerve simplices are small. I checked fullness using the actual statement of def-cbc-enhanced-diagrams-cones: full simplicial subcategories contain all simplices whose vertices are chosen, and Fun is formed degreewise by maps from a product with a simplex. This gives a small full Fun category containing each specified presheaf, rather than merely an unproved equivalence to a putative skeleton. With a pair of presheaves its mapping simplices are small, which verifies the locally-small condition in def-coef-presentable-infinity-category.

Step 3 uses the exact statement of small-family-regular-bound with J a singleton and X its countably infinite value. Thus the chosen regular cardinal is strictly larger than aleph_0 and lies in the smaller universe. The new density node explicitly gives the full Map(h_c,F) equivalence coherently in F; full faithfulness alone would not suffice. The existing pointwise characterization applied to the coherent cocones constructed in step 1 makes evaluation colimit-preserving. This is precisely the mapping-space compactness condition, whose definition I reread.

Step 4 proves that the indexing collection of bounded shapes and maps to fixed C is universe-small, by relabeling their simplices inside kappa. I checked the degeneracy count: uncountability of kappa and regularity bound the countable union of finite-dimensional degeneracies. No kappa-sized bound on the number of shapes is asserted. I choose one colimiting cocone per representative, a universal construction determined up to equivalence. The compact-small-colimits statement is applied only after local smallness and all filtered colimits are available, to diagrams with fewer than kappa nondegenerate simplices and compact vertex values. It says exactly that the apex is compact. This is not a use of the definition of compactness as if it proved closure.

Step 5 uses both clauses of the new density/approximation statements. Density supplies an actually small E_F, not a large slice silently treated as small. For every bounded L I use a simplicial isomorphism to the stored representative pair and precompose its chosen cocone; this is literal restriction/relabeling, so the apex is the stored generator. The approximation node is deliberately stated with prescribed cocones: it supplies their coherent transition maps and the colimiting comparison, which cannot be inferred merely from a list of apices. Its hypotheses hold by steps 1 and 3. Its index is small and kappa-filtered, including the empty-subset object. Fullness then factors the entire resulting simplicial diagram through the small full subcategory on those generator vertices. No unproved replacement of a coherent diagram by arbitrary equivalent vertices is needed.

Step 6 uses only the definitions: local smallness, the fixed regular cardinal, the compact generating small full subcategory, the small filtered presentations and all small simplicial colimits were established in earlier steps. It is marked elementary because it is their conjunction under the presentability definition, not a concealed proof of any earlier assertion.

I tested density on C empty and C terminal: the empty presheaf category is terminal with its empty colimit; on the terminal category, spaces are assembled by their point diagrams, including non-discrete spaces. This confirms that an ordinary set-valued theorem would be insufficient. Compact closure includes an empty diagram, the one-vertex diagram, and a finite coproduct; an initial object maps to the terminal mapping space, as required. Approximation includes K empty, when its subset poset is the singleton empty subset, and K already kappa-small, when that poset has terminal object K and the comparison is the original colimit. For general K, unions of fewer than kappa bounded simplicial subsets remain bounded, and every simplex lies in its finitely generated simplicial subset, so the filtration is nonempty and covers K. Empty D requires no exceptional hypothesis in the item. None of these tests exposes a false statement.

Against delivery-errors B-E I checked statement-only new nodes, introduced objects/definitions, decoded TeX, exact external source places, genuine logged searches, current blueprint provenance, attachment absence, every cited statement's actual content, complete proof-dependency coverage and the unit route. I removed potential C4 and E5 gaps by explicitly constructing coherent pointwise cocones and by requiring prescribed partial cocones. The new nodes are general technical inputs, not elementary bookkeeping and not restated presentability/accessibility clauses; the item's steps carry the generator construction itself. citations.json was generated from and checked against the exact cited node statements. Remote preflight and DAG review are the remaining mechanical checks; no local compiler or forbidden checker is invoked.

## Second reading by N0

I re-read the item statement against HTT Remark 5.5.3.7 (with Example 5.5.1.8 and Proposition 5.5.3.6) and checked the empty ordinary category, terminal category, and coherent space-valued presheaves; all hypotheses and conclusions agree, including higher transformations. I re-read each proof step against every cited node: steps 1–2 use the coherent-nerve, presentable-spaces, parameter-cone-extension, objectwise-colimit, and local-smallness statements exactly as quoted; step 3 uses the regular-bound, Yoneda-density, and compactness definitions; step 4 uses the bounded-colimit compactness statement and explicit universe counting; step 5 uses the density and prescribed-cocone approximation statements and fullness; step 6 is the definitional conjunction of accessibility and presentability. The only elementary step is step 6.

I re-read `lem-coef-space-yoneda-density` against HTT Lemmas 5.1.5.2–5.1.5.3 and tested empty and terminal shapes; its mapping-space evaluation and small coherent density clauses are both present. I re-read `lem-coef-compact-small-colimits` against Corollary 5.3.4.15 and tested empty, singleton, and finite coproduct diagrams; its hypotheses and conclusion are exact. I re-read `lem-coef-colimit-subdiagram-approximation` against HTT 4.2.3.4, 4.2.3.8–4.2.3.11 and tested empty and already-small indexing simplicial sets; the empty subset and universe-smallness qualifications are explicit. All three new nodes are statement-only, self-contained, use existing definition nodes, have exact TeX and source places, and record genuine Mathlib searches with no exact match. Greps of the DAG and blueprint found no duplicate or stronger existing node; no Lean attachment is available.

Changes made in this second reading: appended this per-step and per-node audit; no mathematical or node-file changes were required. The worker's explicit coherent cocone construction, prescribed partial cocones, edge-case clauses, blueprint provenance, and citation quotations were retained. Delivery preflight and DAG/review checks remain to be completed by the required remote dry run.
