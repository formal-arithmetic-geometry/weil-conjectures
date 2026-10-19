# Repair: lem-coef-dg-model-homotopy-colimits

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dg-model-homotopy-colimits.json`: repaired split; statement and Lean audit unchanged; retained original proof steps except the returned step 5, which becomes three short cited steps.
- `dag/nodes/sec-six-functors/lem-coef-dg-quillen-enriched-adjunction-descent.json`: new statement-only node, unsplit; no Mathlib match for a coherent chain-valued derived adjunction, including homotopical parameter families, without a stability hypothesis.
- `citations.json`: one verbatim statement excerpt for every step/node pair.

## Attachments

None. The item's Lean audit is `none`. Searches for its blueprint id in WeilConjectures returned none. Concept searches found ordinary derived tensor and adjunction declarations for abelian categories, not this enhanced model theorem. The new enriched-descent statement also has no project declaration found by id or concept.

## Wanted sources

WANTED: a general reference for enriched Quillen adjunction descent with coherent parameter naturality, for `lem-coef-dg-quillen-enriched-adjunction-descent`. The new statement is agent-formulated from the returned proof's adjunction-descent argument and the existing localization/mapping-comparison statements; no unavailable reference is passed off as a source. No Stacks tag is claimed for this chain-enriched foundation. The parent's existing source record also requests a full chain-enriched dg-model colimit reference; its Higher Algebra attribution covers only the underlying infinity-category assertions.

## Returned fault and correction

The human returned original step 5 (3154 characters) for hidden non-elementary comparison arguments. The preserved sandbox had shortened that step by removing the ordinary derived-adjunction comparison. That was not the requested repair: I compared the sandbox against the current repository's returned proof, restored its ordinary Quillen-adjunction route, retained its other steps verbatim except references to renumbered steps, and exposed the hidden arguments.

Replacement step 5 applies the existing ordinary model-to-infinity derived adjunction theorem and checks the required cofibrancy/fibrancy for the displayed Hom complexes. Replacement step 6 uses the dual of the existing fibrant-subcategory localization theorem for the ordinary cofibrant comparison instead of repeating its argument inline. Replacement step 7 cites the new enriched-descent node for the enriched adjunction and the existing multivariable universal property for its parameter naturality. The item still proves tensor construction, presentability, colimit preservation, the enriched colimit formula and saturation itself. The new node states none of those clauses. Every non-elementary step is now at most 1677 characters.

The item's exact statement, stmt_deps, pointers/source, ancestry, and Lean audit are preserved. The main blueprint ancestor's paragraph 2 was read: its middle mapping-complex comparison motivates this foundational chain; its integral exceptional-adjoint result is not substituted for a general model theorem.

## Not duplicates

lem-coef-dg-quillen-enriched-adjunction-descent vs lem-coef-dg-derived-quillen-calculus: the existing node assumes stable model categories; the new lemma supplies just enriched adjunction descent without stability. The parent has not yet established stability and needs only adjunction descent. The new node has no composition, monoidal functor or mate calculus assertions.

lem-coef-dg-quillen-enriched-adjunction-descent vs lem-coef-model-infinity-derived-adjunction: the latter supplies ordinary coherent mapping-space adjunctions; the new statement is an equivalence of derived chain-valued mapping objects with enriched parameter naturality.

lem-coef-dg-quillen-enriched-adjunction-descent vs lem-coef-dg-model-mapping-comparison: mapping comparison identifies individual derived Hom bifunctors and localized inclusions; it does not state that an enriched Quillen adjunction descends, or identify the derived left/right functors through an enriched adjunction.

lem-coef-dg-quillen-enriched-adjunction-descent vs lem-coef-enhanced-localization-universal: the existing node gives a universal property for separately homotopical enriched functors. The new statement supplies the model-theoretic Quillen hypotheses and derived adjunction identification, without assuming globally homotopical adjoints or enriched replacement functors.

lem-coef-dg-quillen-enriched-adjunction-descent vs lem-coef-enriched-right-quillen-equivalence: that node assumes simplicial models, every source object cofibrant, and a Quillen equivalence. It concludes a DK equivalence of bifibrant simplicial categories, not a chain-enriched adjunction.

The whole-DAG and blueprint searches used “enriched Quillen”, “derived adjunction”, “cofibrant subcategory”, “enriched adjunction”, “mapping complexes” and the corresponding Hom/Quillen concepts. No blueprint node states the new result. The ordinary cofibrant-localization argument needs no new node because the dual of lem-coef-fibrant-subcategory-localization states it.

## Mathlib search review

I read and reused the preserved searches.jsonl results. For the new node I ran LeanFinder, Loogle, grep and LeanSearch with its statement in mind, then a second semantic phrasing. All exact queries and raw log entries used for this verdict are in its mathlib_searches. Candidate CategoryTheory.Adjunction.derived was read in Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:35-75 and 138-150; it is an ordinary-category derived adjunction and does not assert derived Hom complexes or homotopy-coherent families. The Loogle hit CofibrantObject.HoCat.adj concerns ordinary homotopy categories. The second semantic search returned ordinary localization/homotopy-class declarations. The AlgebraicTopology enriched-adjunction grep found no hit. Consequently this node is unsplit, not a Mathlib leaf. The earlier item searches returned ordinary chain tensor and localization statements and no whole-item match.

## Review by Q13

I read coord/brief-stage1.md, stages/1-dag.md, SETUP.md's three levels, GOAL.md, coord/dag-sync.md and delivery-errors.md B–E. I read the chapter/unit records and the current ancestor proof, and compared the retained sandbox proof with the returned/current repository node. This is a repair of one proof step; the item and its recorded Lean statement are unchanged. The new node's source is explicitly the agent-formulated model foundation for the same paragraph. It is statement-only: its possible proof route is to use Brown preservation on cofibrant/fibrant objects, enriched mapping comparison on the two adjunction sides, and full multivariable localization to descend the actual Hom isomorphism. That argument is deliberately not stored as a proof in the unsplit node.

I opened every cited node and checked its statement rather than assuming the needed fact lay in its proof. Step 1 uses dg-model-underlying-localization for the ordinary universal property, combinatorial-localization-presentability for presentability, presentable-infinity-adjoints for completeness, and projective-chains-monoidal-model for D(Z)'s presentably monoidal chain model. The parent's set-generated factorizations and local presentability are exactly these hypotheses. Step 2 uses projective-cochain-monoidal-model's explicit fibrations and quasi-isomorphisms to read the enriched model axiom. Its zero-object argument is written out. Step 3 uses that same complex model and explicitly transposes lifting squares; the model weak factorization systems justify the lifting characterizations. It does not claim tensoring arbitrary noncofibrant inputs is Quillen.

Step 4 uses brown-split-factorizations only for its stated split factorization of maps between cofibrant objects. Two-out-of-three is applied to the displayed splitting. Mapping-comparison explicitly supplies localized cofibrant inclusion equivalences and homotopical Hom bifunctors. The complex model's Hom axiom is checked using the adjoint pushout-product calculation already stated. Enhanced-localization-universal explicitly includes the multivariable coherence and composition clauses needed for the tensor action; an enriched replacement functor is never assumed.

For replacement step 5, model-infinity-derived-adjunction actually states the preservation, mapping-space adjunction and replacement formulas used. The two ordinary adjunctions are the actual tensor/Hom and tensor/cotensor pairs, with preservation established in step 3. The cotensor of a fibrant object is fibrant because it is right Quillen. Projective-chains says every complex is fibrant. Mapping-comparison applies only with cofibrant first and fibrant second input, verified for all three displayed Hom complexes. For replacement step 6, I checked every hypothesis of fibrant-subcategory-localization on the opposite model: its terminal object is the original initial object; pullbacks become pushouts of cofibrations; trivial cofibrations are stable under these pushouts; and the required factorization is a model factorization. The ordinary universal property of dg-model-underlying-localization includes whole functor categories, so fully faithful restriction really identifies naturality homotopies as well as objects. No inferred equality of functors is based solely on their object values.

Replacement step 7 cites the new generic enriched Quillen-descent statement for its actual conclusion, not merely a definition of enrichment. Its no-stability hypotheses match the models in use. Mapping-comparison supplies separate homotopicality on the cofibrant/fibrant domains; the localization node explicitly allows opposites and finitely many variables. Thus the actual three-variable Hom isomorphism yields the claimed coherent comparison. Applying the unit mapping-space functor is the stipulated underlying-enrichment convention, not an additional comparison theorem. This new lemma is strictly smaller than the item: no cocompleteness, tensor construction, colimit formula, realization or saturation is in its conclusion.

Steps 8 and 9 use infinity-yoneda-presheaf-limits for both representable (co)limit tests, and step 9 additionally its full Yoneda assertion. I verified that this node allows arbitrary small simplicial shapes, rather than only nerves of ordinary categories. In step 9 every map is induced by the cocone or the natural adjunction; the tested map is exactly the displayed gamma. Step 10 is only the definition of realization/totalization and is correctly elementary. Step 11 uses only the initial homotopy-localization assertion of pointed-model-stability, not its conditional stability conclusion, then model-localization-detects-weak-equivalences with no endpoint cofibrancy assumption, and the definition's equivalence-edge criterion.

For small-case checks, the new statement reduces to the identity Hom comparison for the identity adjunction, and to zero complexes for zero adjoints. It permits noncofibrant arbitrary objects only after replacement; omitting replacements would fail and was not done. The parameter clause explicitly requires separate homotopicality; arbitrary parameter transformations are not asserted to descend. The parent still covers the empty diagram (Hom out of zero is zero, the terminal chain object), a singleton diagram (identity comparison), and Delta-op with its actual coherent structure maps. Neither boundedness, stability nor properness was added. I checked B1–B10 (complete introduced objects and notions, actual searches, no claimed Mathlib leaf or source tag), C1–C8 (all non-elementary arguments cited, verbatim quote file, no proof-only citation, generic tool declaration), D1–D5 (a genuine smaller lemma and retained proof route), and E1–E7 (the model/cofibrancy/size hypotheses above). No statement dispute was found.

## Incomplete work

Nothing needed for this stage-1 repair remains mathematically deferred beyond the intended new unsplit statement. Server dry-run validation and push results are recorded below when completed. No Lean was written or compiled.

## Validation repairs

The first dry run stopped before pushing because the verbatim completeness quote was shorter than the tool’s 40-character minimum. I expanded it to include the presentable-category hypotheses and the completeness sentence. No proof or statement changed.
