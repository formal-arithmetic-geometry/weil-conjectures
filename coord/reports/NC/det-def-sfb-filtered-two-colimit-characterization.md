# Worker report

1. Files written:
   - `dag/nodes/sec-six-functors-basics/det-def-sfb-filtered-two-colimit-characterization.json`: existing statement unchanged; re-split proof, 2633 characters in five steps.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-filtered-two-colimit-common-stage-images.json`: statement, unsplit; no Mathlib match. Simultaneous representatives and the comparison-image test at a common stage.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-filtered-two-colimit-diagonal-equality.json`: statement, unsplit; no Mathlib match. Diagonal representatives, their comparison and transition identities, and their eventual-equality criterion.
   - `citations.json`: one verbatim statement quotation for every step/node citation.
2. Attachments: none. The WeilConjectures tree defines CategoryCocone and its conditions, but does not state this comparison characterization. Sheaf.CategoryTheory.FilteredTwoColimitCharacterization already proves the item, with the two diagonal identities as local `have`s, not separate declarations. This is the human's deliberate stage-1 re-split of that existing item, expressly requested on 2026-10-21; it is not an attachment or a stale claim.
3. WANTED: none.
4. What needed repair: the existing 3936-character proof bundled separate arguments in one node. No statement or route error was found. The statement, statement dependencies, imported blueprint metadata, and historical Lean/review fields are preserved. Both new nodes are proper intermediate representative-calculus lemmas: neither mentions Full, Faithful, EssSurj, or the three cocone conditions, so neither restates an item clause. Their proofs are not included in their node files. The elementary essential-image and fullness assemblies remain explicit, as do the application of Hom-inj and the final categorical criterion.
5. Unfinished: no requested part left unfinished; the new nodes are intentionally statement-only for other stage-1 workers.

## Sources and search results

I read the current main-20261015 chapter and sk-def-sfb-filtered-two-colimit unit, the characterization statement and full proof, and the model and conditions statements. This item realizes the characterization in unit proof step 2, not the unit's defining statement, so no unit realization record is edited. Chapter and unit routes are preserved.

For both new nodes the direct source is characterization.proof.md, point 3: the first paragraph for common-stage images and the converse paragraph for diagonal equality. I read categories.tex at `section-directed-colimits`, Stacks Tag 04AX, particularly the explicit filtered-set equivalence relation after `definition-directed` (Tag 002V). This supplies representatives and eventual equality, not the cocone-conjugation identities, which are the additional category-specific argument. For the final assembly I read `lemma-equivalence-categories` (Tag 02C3) and `definition-equivalence-categories`.

Before creating either node I searched the whole DAG by the model, colimit, diagonal-representative and common-stage concepts, and the blueprint using blueprint_refs.py ancestor and searches `two-colimit`, `common stage`, `diagonal colimit`, and broader category-colimit searches. I inspected the potentially overlapping strict category-colimit nodes, their Hom-fiber construction and finite-list equality assertions. They do not state the coherent category-of-pairs comparison or its diagonal formulas. The model gives the construction and well-definedness; the two extracted assertions are consequences requiring representative manipulations, not assertions already included in its statement.

All Mathlib queries were run with the required msearch.py command and their complete actual outputs are kept in search-0.txt through search-9.txt. The new-node mathlib_searches contain the exact executed queries and actual returned hits. Both semantic phrasings were tried for each proposed argument. The hits include Functor.ιColimitType_eq_iff_of_isFiltered and its primed variant (Mathlib/CategoryTheory/Limits/Types/ColimitTypeFiltered.lean:65,72), and NatIso.naturality_1 (Mathlib/CategoryTheory/NatIso.lean:148); I opened those sources. The former only gives equality for a prescribed set diagram and the latter only gives conjugation naturality. Neither, singly or by a one-line specialization, states the category-specific assertions including simultaneous common-stage representatives, comparison-image cancellation or the two diagonal identifications. The existing filtered-set node is reused by the item. No new Mathlib leaf is created. The item's already logged Mathlib searches are retained rather than falsely re-recorded as fresh searches.

## Arguments moved to the new nodes

For common-stage-images, start with independent representatives f=[k,g] and h=[l,g'] supplied by the set-colimit representative property. Directedness gives m above both. The transition relations identify their classes with [m,t_km(g)] and [m,t_lm(g')]. Denote those arrows by u and v. Well-definedness of the comparison and its formula identify their images with theta_jm Phi_m(u) theta_im^{-1} and theta_jm Phi_m(v) theta_im^{-1}. Multiplying on the left by theta_jm^{-1} and on the right by theta_im proves the forward implication; substituting equal Phi_m images proves the reverse. This retains every common-stage choice, class identification, and cancellation used by the old forward faithfulness paragraph. It assumes no Hom-inj condition and can be worked on independently of diagonal-equality.

For diagonal-equality, put delta_k(g)=[k,T_kk(g)] for the fixed pair (k,x),(k,y). Naturality of theta_kk gives
Phi(delta_k(g)) = theta_kk,y Phi_k(T_kk(g)) theta_kk,x^{-1} = Phi_k(g).
For n >= k, naturality of tau_kkn gives
t_kn(T_kk(g)) = tau_kkn,y T_kn(T_kk(g)) tau_kkn,x^{-1} = T_kn(g).
In the strict normalized blueprint these are the identity comparisons; writing the naturality forms keeps the dependent endpoints correct in the live model. The Hom colimit over J_kk is small filtered. Its same-stage equality criterion says that the two diagonal classes agree exactly when there is one n >= k with equal transitions. Substituting the displayed transition identity for g and g' proves the new equality criterion in both directions. Thus the old reverse paragraph's normalized representatives, comparison-image identification, common later stage, normalization transport, and eventual equality all reappear as a separate task. It assumes no faithfulness hypothesis.

## Review by NC

I checked delivery-errors B–E against the actual node files and the above sources. Both new statements introduce their index, categories, cocone, fixed objects and arrows, and explicitly refer to the model for the coherence/normalization, Hom diagram, transition maps and comparison functor. They have only that statement dependency, no proof steps, no proof dependencies and no hidden proof in their statements. Both blueprint.from records point directly to this imported blueprint node, with the precise forward/converse places and an empty via chain. I found no equivalent blueprint assertion; same_as is empty.

Step 1 cites the model's statement that objects are pairs and that Phi(i,x)=Phi_i(x), and the conditions statement defining Obj. Inverting the isomorphism gives exactly the right orientation. No theorem about the model's proof is being used.

Step 2 cites the model's Hom-colimit and comparison formula, clause (1) of the filtered-set node, and the exact Hom-surj clause of the conditions. I verified the indexing category is a set, nonempty and directed under upper bounds; as a preorder it equalizes parallel arrows. Thus the small-filtered hypothesis of the set-colimit node applies. Fullness supplies a preimage, the representative theorem supplies its k,g, and the comparison formula is precisely the displayed Hom-surj equation; conversely the equation supplies a preimage. No choice of a strictly commuting category diagram is presumed.

Step 3 cites common-stage-images for simultaneous representatives with equal Phi_m images. The conditions node's Hom-inj statement applies to the two parallel arrows T_im(x) -> T_jm(y) in C_m, not to arrows from different categories. It supplies n >= m and equality after T_mn. The model states exactly the tau-conjugation formula for t_mn, so conjugation by the same endpoint isomorphisms gives equal transitions. Clause (3) of the filtered-set node then gives equality of the two classes. This is the application of the new lemma, not a repetition of its proof.

Step 4 cites diagonal-equality for both the comparison-image formula and the eventual-equality equivalence. Faithfulness applies to parallel arrows between (k,x) and (k,y), and the resulting n >= k with equal T_kn images is exactly the Hom-inj conclusion in the conditions node. Thus every part of the reverse argument is covered by a quoted statement. It uses neither the new node's unwritten proof nor facts from a definition's proof.

Step 5 cites the conditions for the conjunction and the existing Mathlib leaf lem-trf-fully-faithful-ess-surj-equivalence only for constructing an actual equivalence from the three properties. The reverse direction in the chosen live Lean statement is projection of the Faithful/Full/EssSurj fields of Functor.IsEquivalence, as in the old split; it does not demand an unquoted converse from that node. Functor.asEquivalence realizes the quasi-inverse. A common larger universe contains the categories and the Hom-indexing diagrams. Both existing off-unit citations are general Mathlib tools and do not replace the unit route.

I checked small cases: a singleton directed index reduces diagonal equality to equality of the original arrows, and the comparison formula to Phi_k. Empty stage categories give vacuous assertions for their nonexistent objects. A two-stage system of one-object categories arising from the group homomorphism Z -> 0 has distinct early arrows with equal diagonal classes only after the second stage, exactly as stated: neither new node wrongly asserts early equality or that stage inclusions are faithful. Non-antisymmetric preorders cause no issue: the source/target order proofs are proof-irrelevant, and upper bounds still yield a small filtered preorder. In the forward application all conjugations use the same source/target tau, so no unjustified cancellation or normalization is performed at unequal indices.

I compared each original step with the replacement: steps 1 and 2 are retained verbatim; the common-stage work from step 3 is assigned to common-stage-images, while the Hom-inj application and tau-conjugation remain explicit; all normalized calculations from old step 4 are assigned to diagonal-equality; the final field/quasi-inverse argument is retained with less repeated wording. No statement is weakened. The assembled proof is 2633 characters, and its longest step is 814 characters, so no >2000-character step hides a further argument. New node proofs stay intentionally empty. citations.json quotes are literal substrings of the actual statements, including both new statements.

## Not duplicates

lem-sfb-filtered-two-colimit-common-stage-images vs lem-pc-filtered-colimit-commrings-elementwise: the existing node concerns Filtered colimits of commutative rings, elementwise; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-pc-filtered-colimit-commrings-elementwise: the existing node concerns Filtered colimits of commutative rings, elementwise; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-per-local-system-finite-cover-germ-action: the existing node concerns Monodromy of a local system on germs over a finite etale neighbourhood; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-per-local-system-finite-cover-germ-action: the existing node concerns Monodromy of a local system on germs over a finite etale neighbourhood; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-sfb-scalar-unit-equality-detection: the existing node concerns An adjunction unit telescope detects equality at a scalar power; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-sfb-scalar-unit-equality-detection: the existing node concerns An adjunction unit telescope detects equality at a scalar power; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs def-weil-pbc-filtered-colimit-hom-fibers: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs def-weil-pbc-filtered-colimit-hom-fibers: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-colimit-constant-connected-diagram: the existing node concerns The colimit of a constant diagram over a connected (e.g. nonempty filtered) category; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-colimit-constant-connected-diagram: the existing node concerns The colimit of a constant diagram over a connected (e.g. nonempty filtered) category; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-colimit-of-sites-reduced: the existing node concerns Category colimit site construction after category witness; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-colimit-of-sites-reduced: the existing node concerns Category colimit site construction after category witness; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-colimit-of-sites: the existing node concerns The colimit of an inverse system of sites with finite coverings; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-colimit-of-sites: the existing node concerns The colimit of an inverse system of sites with finite coverings; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-colimit-site-abelian-stage-image-refinement: the existing node concerns Finite stage-image expressions have forward-stage representatives; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-colimit-site-abelian-stage-image-refinement: the existing node concerns Finite stage-image expressions have forward-stage representatives; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-colimit-site-covering-pullback-stage-presentation: the existing node concerns Common stage presentation of prescribed covering pullback squares; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-colimit-site-covering-pullback-stage-presentation: the existing node concerns Common stage presentation of prescribed covering pullback squares; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-colimit-site-finite-kan-arrow-lift: the existing node concerns Finite Kan arrow diagrams lift simultaneously above their stage; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-colimit-site-finite-kan-arrow-lift: the existing node concerns Finite Kan arrow diagrams lift simultaneously above their stage; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-colimit-site-kan-unit-relations: the existing node concerns Single-stage Kan unit relations vanish after refinement; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-colimit-site-kan-unit-relations: the existing node concerns Single-stage Kan unit relations vanish after refinement; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-etale-limit-affine-stage-eventual-zero-tail: the existing node concerns Finite-stage detection on affine tail; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-etale-limit-affine-stage-eventual-zero-tail: the existing node concerns Finite-stage detection on affine tail; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-etale-limit-affine-stage-eventual-zero: the existing node concerns Finite-stage detection of zero with one affine stage; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-etale-limit-affine-stage-eventual-zero: the existing node concerns Finite-stage detection of zero with one affine stage; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-etale-limit-affine-stage-tail-colimit: the existing node concerns Cohomology comparison is a colimit on the affine cofinal tail; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-etale-limit-affine-stage-tail-colimit: the existing node concerns Cohomology comparison is a colimit on the affine cofinal tail; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-etale-limit-reindex-transition-coherence: the existing node concerns Reindexing preserves inverse-image transition coherence; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-etale-limit-reindex-transition-coherence: the existing node concerns Reindexing preserves inverse-image transition coherence; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-algebras-elementwise: the existing node concerns Elements of a filtered colimit of commutative algebras come from a stage; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-algebras-elementwise: the existing node concerns Elements of a filtered colimit of commutative algebras come from a stage; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-categories: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-categories: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-category-descent: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-category-descent: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-category-finite-functor-lift: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-category-finite-functor-lift: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-category-finite-lift: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-category-finite-lift: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-category-iso: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-category-iso: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-category-list-equality: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-category-list-equality: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-category-structure: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-category-structure: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-fiber-laws: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-fiber-laws: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-fiber-operations: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-fiber-operations: the existing statement uses a strict Cat diagram and a colimit of object/arrow sets; the new node uses the coherent category-of-pairs Hom model and its cocone comparison or diagonal normalization, with neither strict composition of transitions nor a quotient object set.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-finite-iso-lift: the existing node concerns Finite isomorphisms lift above fixed stage objects; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-finite-iso-lift: the existing node concerns Finite isomorphisms lift above fixed stage objects; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-flat-modules: the existing node concerns Filtered colimits of flat modules are flat; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-flat-modules: the existing node concerns Filtered colimits of flat modules are flat; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-modules-criterion: the existing node concerns Elementwise criterion for a cocone of a filtered diagram of modules to be a colimit; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-modules-criterion: the existing node concerns Elementwise criterion for a cocone of a filtered diagram of modules to be a colimit; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-pullback-exists: the existing node concerns Factorization existence for a stable pullback image; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-pullback-exists: the existing node concerns Factorization existence for a stable pullback image; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-pullback-hom-ext: the existing node concerns Joint monicity of stable pullback image projections; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-pullback-hom-ext: the existing node concerns Joint monicity of stable pullback image projections; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-filtered-colimit-sets-elementwise: the existing statement is about an arbitrary set diagram; the new node additionally computes comparison images in a coherent category cocone.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-filtered-colimit-sets-elementwise: the existing statement has only diagram transition maps; the new node identifies those maps on diagonal representatives with T_kn and computes their Phi images.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-finite-presentation-hom-directed-colimit: the existing node concerns Maps from a module of finite presentation into a directed colimit factor through a stage, on a qcqs scheme (Stacks 01BS); the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-finite-presentation-hom-directed-colimit: the existing node concerns Maps from a module of finite presentation into a directed colimit factor through a stage, on a qcqs scheme (Stacks 01BS); the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-finite-type-ring-map-factors-filtered-colimit: the existing node concerns Maps from a ring of finite type over Z into a filtered colimit of rings factor through a stage; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-finite-type-ring-map-factors-filtered-colimit: the existing node concerns Maps from a ring of finite type over Z into a filtered colimit of rings factor through a stage; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-proetale-qcqs-fp-section-calculus: the existing node concerns Finite-presentation section calculus on the qcqs pro-etale site; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-proetale-qcqs-fp-section-calculus: the existing node concerns Finite-presentation section calculus on the qcqs pro-etale site; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-weil-pbc-strict-henselization-triples: the existing node concerns The colimit over etale algebras with a point and a residue embedding is strictly henselian; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-weil-pbc-strict-henselization-triples: the existing node concerns The colimit over etale algebras with a point and a residue embedding is strictly henselian; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-a1-sections-intersection-structure-colimit: the existing node concerns Structure-sheaf sections on an intersection are a filtered colimit; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-a1-sections-intersection-structure-colimit: the existing node concerns Structure-sheaf sections on an intersection are a filtered colimit; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-coef-accessible-small-object-factorization: the existing node concerns Accessible small-object factorizations; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-coef-accessible-small-object-factorization: the existing node concerns Accessible small-object factorizations; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-coef-cellular-tree-presentable-approximations: the existing node concerns Presentable approximations of a fixed cellular tree with compatible supports; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-coef-cellular-tree-presentable-approximations: the existing node concerns Presentable approximations of a fixed cellular tree with compatible supports; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-coef-diagram-compact-pushout-descent: the existing node concerns Simultaneous compact descent of pointwise pushout data; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-coef-diagram-compact-pushout-descent: the existing node concerns Simultaneous compact descent of pointwise pushout data; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-coef-joyal-filtered-equivalences: the existing node concerns Filtered colimits preserve Joyal categorical equivalences; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-coef-joyal-filtered-equivalences: the existing node concerns Filtered colimits preserve Joyal categorical equivalences; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-coef-presentable-cellular-factorization: the existing node concerns Cellular small object factorizations in locally presentable categories; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-coef-presentable-cellular-factorization: the existing node concerns Cellular small object factorizations in locally presentable categories; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-coef-presentable-presentation-comparison: the existing node concerns Comparison of large filtered presentations on small filtered subdiagrams; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-coef-presentable-presentation-comparison: the existing node concerns Comparison of large filtered presentations on small filtered subdiagrams; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-coef-small-cellular-tree-descent: the existing node concerns Compact-root descent of a small cellular tree; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-coef-small-cellular-tree-descent: the existing node concerns Compact-root descent of a small cellular tree; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-coef-small-right-lifting-accessibility: the existing node concerns Accessibility of a small right lifting class; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-coef-small-right-lifting-accessibility: the existing node concerns Accessibility of a small right lifting class; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs det-def-sfb-filtered-two-colimit-characterization: the item characterizes categorical properties by three cocone conditions; the new node is an intermediate representative calculation with no fullness, faithfulness or cocone-descent assumption.

lem-sfb-filtered-two-colimit-diagonal-equality vs det-def-sfb-filtered-two-colimit-characterization: the item characterizes categorical properties by three cocone conditions; the new node is an intermediate representative calculation with no fullness, faithfulness or cocone-descent assumption.

lem-sfb-filtered-two-colimit-common-stage-images vs det-def-sfb-filtered-two-colimit-model: the existing node constructs the Hom-colimit category and its comparison; the new node asserts simultaneous representatives and comparison-image cancellation.

lem-sfb-filtered-two-colimit-diagonal-equality vs det-def-sfb-filtered-two-colimit-model: the existing node constructs the Hom-colimit category; the new node identifies diagonal comparison/transition maps and proves the eventual-equality criterion for original stage arrows.

lem-sfb-filtered-two-colimit-common-stage-images vs def-weil-directed-colimit-abelian-groups: the existing node concerns Directed colimit of a directed system of abelian groups; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs def-weil-directed-colimit-abelian-groups: the existing node concerns Directed colimit of a directed system of abelian groups; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-trf-ind-etale-local-henselian-integral: the existing node concerns Local henselian ind-etale algebras are integral over the base henselization; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-trf-ind-etale-local-henselian-integral: the existing node concerns Local henselian ind-etale algebras are integral over the base henselization; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-trf-inverse-system-site-point: the existing node concerns Inverse systems satisfying finite-cover lifting define site points; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-trf-inverse-system-site-point: the existing node concerns Inverse systems satisfying finite-cover lifting define site points; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-common-stage-images vs lem-trf-site-point-fibre: the existing node concerns Fibre of a topos point as a filtered colimit over pointed site objects; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

lem-sfb-filtered-two-colimit-diagonal-equality vs lem-trf-site-point-fibre: the existing node concerns Fibre of a topos point as a filtered colimit over pointed site objects; the new node concerns Hom representatives in an arbitrary coherent normalized directed category cocone, with its specified theta/tau comparisons, and does not assert that existing specialized result.

