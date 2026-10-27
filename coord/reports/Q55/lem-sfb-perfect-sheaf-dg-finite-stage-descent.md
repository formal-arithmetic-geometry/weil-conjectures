# Q55 worker report

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-perfect-sheaf-dg-finite-stage-descent.json: statement split; existing affine descent reused.
   - dag/nodes/sec-six-functors-basics/lem-sfb-perfect-sheaf-dg-hom-continuity.json: new statement-only lemma; not in Mathlib.
   - dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-dg-binary-gluing.json: new statement-only lemma; not in Mathlib.
   - citations.json: exact statement quotations for every proof-step citation.
2. Attachments: none. Searches by the item's exact blueprint tag, finite dg descent, perfect sheaf dg, and coefficient/gluing terminology in lean/WeilConjectures found no declaration giving this item. The ordinary affine perfect complex declarations do not assert sheaf dg descent.
3. WANTED: none. The dg versions are explicitly agent statements, not assertions attributed to ordinary Stacks lemmas.
4. The imported node had no proof. Its source correctly warned that 09RF is ordinary scheme descent, not this sheaf dg assertion. I retain its mathematical statement and all hypotheses; I only added the missing inline definition reference for finite type algebras and its stmt_dep. No statement dispute was found. The inherited blueprint.from.node is null: blueprint_refs.py ancestor reports None because the created.item chain has no remaining blueprint ancestor. I preserved this value, the existing via chain and the precise inherited place; each child's via prepends the item. The latest blueprint direct-images proof (3) was read; it provides the surrounding direct-image route, not a theorem about dg coefficient objects.
5. Unfinished work: the two new lemmas are intentionally unsplit. No new Lean or compilation was attempted. All writes are in the Q55 item sandbox.

## Review by Q55

I read AGENTS.md, the stage-1 brief, worker role, all stage-1 rules, GOAL.md, the three route levels in SETUP.md, both copies of delivery-errors B--E, the chapter and unit records, and the current blueprint unit and direct-image proof. There was no prior sandbox split to recover and no repair note for this item. No SGA source is used.

For the item I read perfect.tex, lemma-descend-perfect (09RF), including its preceding lemma-descend-homomorphisms (09RE). The source glues maps to the restricted original object before transposing back to an isomorphism. That is necessary here too: arbitrary local isomorphisms cannot simply be declared to give an isomorphism from an arbitrary chosen gluing. I read cohomology.tex lemma-glue (08DG), including its target-map clause, and lemma-mayer-vietoris-hom (08BW). The new binary dg gluing lemma states exactly the additional dg version needed, with no uniqueness claim. It is a general ringed dg result with no finite coefficient, perfectness or descent conclusion, so it is smaller than the item and is not a renamed clause.

For the new Hom lemma I read 09RE's affine and Mayer--Vietoris proof and the existing standard-normalized-resolution-filtered-colimit node. The new statement uses the actual sheaf dg coefficient algebras rather than the ordinary schemes in 09RE. It is only full faithfulness for existing models; it asserts no existence of finite-stage objects. A proof can establish the affine case by finite-cell Hom complexes, their retracts, and the stated resolution continuity, then pass through a finite affine cover using dg Mayer--Vietoris. Those arguments remain work for this unsplit child, not undocumented assumptions in the assembly proof. The source reference says explicitly that it is an agent refinement. The indexing set is small (subalgebras of the given underlying set A), nonempty and directed because A is not finite type; finitely generated images fit in a common larger subalgebra. The exceptional constant R_D convention is excluded at all eventual subalgebra stages. No transition is assumed flat.

For step 1 I opened and read lft-affine-pairs for the finite type affine chart hypothesis, and the complete statements of ringed-dg-scalar-adjunction, sheaf-dg-hflat-computation, affine-dg-coefficient-module-comparison and dg-coefficient-realization. The first really gives an exact left adjoint, open compatibility and the specified counit for left modules via opposites. The second, added during this review, justifies the regular-module computation: its graded-flat/homotopically-flat hypotheses hold since balanced tensor with the regular module is the identity. This proves preservation of finite operations and retracts, rather than assuming that derived extension preserves an unstated finiteness property. The affine comparison gives the quasi-coherent category and finite-cell models. Composite extensions are identified as left adjoints to equal composite restriction functors, using the elementary uniqueness of adjoints; no separate tensor-associativity theorem is used. If A is finite type, identity extension settles the entire assertion, including A=0 and A=D.

For step 2 I opened the finite-affine-cover Mathlib leaf, lft-affine-pairs, the complete affine dg comparison and affine-perfect-dg-finite-stage-descent. Each says precisely what the proof takes: a finite cover of W, finite type coordinate algebras over the affine base, locally perfect objects identified with finite-cell retracts, and descent of such dg retracts. The coordinate algebra need not be D-flat. I read the existing affine descent proof as a check that retracts are homotopy idempotents, not strict idempotents. Only its statement is used in the item. The induction is over every open admitting at most r affine opens, with the empty and affine base cases stated, so no circular induction is hidden.

For step 3 I read separated-affine-open-intersection. It applies because Y is separated over Spec D and all charts map into that common affine base. It says the intersection with the final affine chart is covered by at most r-1 affines. Thus the overlap is quasi-compact. This uses separatedness, not a false assertion about arbitrary quasi-separated schemes. The two local coefficient algebras have finitely generated images in A, and their combined generators fit in the directed subalgebra set from step 1. The canonical composition identifications give the displayed local realization maps after enlargement.

For step 4 I read the new Hom statement in full against the exact objects used. Both restrictions are perfect E-objects on the quasi-compact overlap. Its surjectivity lifts the forward map and inverse; its injectivity detects each inverse equation after a later stage. Taking a common upper bound for these finitely many choices gives an actual derived isomorphism. The overlap statement is not applied to an arbitrary ordinary target or to an unbounded nonperfect object.

For step 5 I read the new dg gluing statement and the scalar-adjunction statement again. The target is the actual restricted dg object Res(H); it need not be perfect over E and the gluing lemma does not require that. The adjuncts a,b agree over the overlap because adjunction is natural and commutes with restriction. The output F_E is locally the two perfect quasi-coherent objects. Its map to Res(H) has an adjunct whose restrictions are the chosen local isomorphisms. Underlying cohomology is detected locally; hence this adjunct is inverted in the dg localization, exactly as defined in sheaf-dg-module-localization. This produces the global isomorphism, not merely compatible isomorphisms of cohomology groups.

I tested empty W, empty overlap, one affine, repeated affine charts, zero H, the zero ring, A=D, a finite type noninjective quotient D to A, and non-flat coefficients on non-flat affine charts. Empty cases give zero objects or the product gluing; finite type cases take E=A. The proof nowhere identifies O_W tensor R_A with the ordinary tensor O_W tensor A; that identification would be false without flatness. The generality of the two new statements covers these cases. Neither new lemma assumes the item's conclusion, and the old affine descent and scalar adjunction do not depend on this sheaf descent item. Each proof step is under 2000 characters; no long-step hidden lemma remains. proof_deps is exactly the union of uses, and every citation has a verbatim statement quotation in citations.json. The three off-unit geometric tools are declared in split_report.tool_uses.

I ran leanfinder twice per new statement and per item, plus Loogle, LeanSearch and source grep via msearch.py, and read all returned hits. The hits concern ordinary sheaf generators/colimits, Kähler differentials, ordinary gluing of sections or ringed spaces, and categorical colimit/limit interchange. I read representative source declarations in Sheaf/Quasicoherent.lean, Sheaf/Colimits.lean, Topology/Sheaves/SheafCondition/UniqueGluing.lean and Limits/FilteredColimitCommutesFiniteLimit.lean. None gives either dg statement or the item's descent. searches.jsonl retains actual calls and digests; the JSON records their exact tool/query and outcomes. No unavailable search was reported as a negative result.

## Not duplicates

The whole DAG was searched by source tags, terminology and the candidate ids; blueprint_refs searches for perfect descent, sheaf dg, 09RE, 08DG, Hom continuity and gluing found no blueprint node with either new statement. Ordinary perfect-complex descent and ordinary ringed-space gluing cannot be substituted by deleting the dg action: the missing assertion is precisely action-preserving derived descent. Same-source pairs follow, including peripheral uses of those tags. The comparison is with each node's statement, not its proof or title alone.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-trf-cotangent-resolution-data: the existing statement concerns polynomial resolutions or cotangent complexes; it does not compare sheaf dg derived Hom.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-trf-cotangent-resolution-coherence: the existing statement concerns polynomial resolutions or cotangent complexes; it does not compare sheaf dg derived Hom.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-trf-polynomial-augmentation-boundary: the existing statement concerns polynomial resolutions or cotangent complexes; it does not compare sheaf dg derived Hom.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-trf-cotangent-retract-scalar-cancellation: the existing statement concerns polynomial resolutions or cotangent complexes; it does not compare sheaf dg derived Hom.

lem-sfb-perfect-sheaf-dg-hom-continuity vs new-perfect-hom-open-restricted-maps: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Assembly of restricted transition and cocone fields); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-pc-perfect-hom-local-comparison: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (A pinned local filtered Hom comparison); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-diagram: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Functor and cocone of geometric Mayer–Vietoris triangles); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-pc-perfect-overlap-stage-equivalence: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Constructed cartesian overlap object and transition data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-model-coherent-object-comparisons: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Coherent affine object comparisons and one-arrow natural isomorphisms); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-push-pull-cocone: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (A representing cocone for the stage pullback Hom functors); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-finite-chain-squares-colimit-descent: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Eventual commutativity of a finite interval of chain squares); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-comparison: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Pinned exact five-term comparison for perfect Hom on a two-open cover); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-stage-rows-core: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Geometric Mayer–Vietoris rows with distinguished-triangle presentations); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-pc-perfect-hom-continuity-on: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Open-local perfect Hom continuity condition); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-object-realization: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Pinned categorical comparisons for the fixed geometric overlap); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-transition-comparison-core-coherence: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Fixed-stage coherent overlap comparison); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs new-perfect-hom-open-restricted-pinned-maps: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Transition coherence from pinned natural equivalences); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-transition-comparison-diagram: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Finite-stage overlap descent with coherent comparison data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-open-transport-square: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Open pullback Hom transport square); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-model-limit-hom-equation-of-coherent-objects: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Limit Hom equation from coherent object triangles); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-perfect-chain-map-equality-detection: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Eventual equality of chain maps from two stages); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-bounded-graded-map-colimit-descent: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Descent of bounded graded families of module maps); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs new-perfect-hom-open-restricted-stage-pinned: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Stage equation for restricted representing data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-descent-open-union: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Two-open induction step for perfect-complex descent); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-fp-module-map-canonical-preorder: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Canonical descent of one finitely presented module map over a directed preorder); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-hom-presentation: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Pinned geometric presentation of the two overlap Hom sets); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-object-realization-core-data-at: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Single-stage overlap comparison data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-geometric-columns: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Local recognition of the geometric outer columns); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-pc-affine-model-comparison-data: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Coherent affine model comparison data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-model-stage-hom-equation-of-coherent-objects: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Stage Hom equation from coherent object triangles); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-stage-colimit: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (The functor and colimit of stage Hom sets); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-recorded-perfect-hom-continuity: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Hom continuity for the recorded original-counit comparisons); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-composite-object-pin: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Canonical composite overlap transport satisfies the cartesian object pin); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-perfect-chain-map-descent: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Descent of chain maps between affine perfect complexes); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-perfect-chain-geometric-models: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Affine perfect models and geometric scalar-extension comparison); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-open-test-bijective: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Bijective open pullback Hom restriction on supported tests); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-object-realization-core-of-data: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Core realization from stagewise overlap comparison data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-base-change-model-isos-of-scheme-comparisons: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Model isomorphisms over fixed compatible scheme transports); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-pc-complex-scalar-extension-hom: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Scalar extension of maps between base-extended complexes); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-model-comparison-data-from-hom-equations: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Constructor interface for explicit affine comparison data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-perfect-homotopy-descent: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Descent of homotopies between affine perfect chain maps); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-continuity: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Cofinal-tail continuity of Hom between perfect complexes); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even-three: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Fixed even geometric outer column at index 3); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-open-restricted-data: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Pinned unshifted restriction of a representing pullback Hom cocone); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs new-perfect-hom-open-restricted-core: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Construction of restricted representing data from QCoh fields); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-pc-perfect-hom-local-map: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Maps built from the three local Hom comparisons); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-stage-rows: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Functorial exact stage Hom rows before colimit exactness); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-base-change-model-isos-core: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Nonempty affine model comparison data core); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-model-comparison-of-bottom-models: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Propagation of two bottom-stage affine models); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-hom-continuity: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Directed Hom continuity in the exact two-open comparison diagrams); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-triangle-cocone: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Coherent geometric Mayer–Vietoris triangle cocone before applying Hom); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs new-perfect-hom-open-restricted-qcoh: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Quasi-coherence after open restriction); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-base-change-model-comparison-isos: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Coherent geometric object isomorphisms for specified affine models); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-graded-scalar-extension-coherence: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Colimit coherence of a transported graded scalar-extension map); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-directed-perfect-hom-iso: the existing statement assumes abstract continuity/presentation data before lifting an isomorphism; the new statement establishes the coefficient sheaf dg Hom bijection itself.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-local-models-descended-transition: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Descended overlap transition acting on every realization); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-perfect-graded-hom-descent: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Descent of degree-minus-one graded maps on bounded finitely presented complexes); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-presentation: the existing statement assumes abstract continuity/presentation data before lifting an isomorphism; the new statement establishes the coefficient sheaf dg Hom bijection itself.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-pc-affine-base-change-ring-diagram: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Explicit affine base-change ring diagram on the order tail); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs new-perfect-hom-open-restriction-transport: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Stage and apex specializations of cartesian open transport); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-pc-perfect-hom-open-restriction-map: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Concrete cartesian open restriction of pullback Hom); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-object-realization-core-data: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Coherent diagrams for the fixed geometric overlap object data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-geometric-columns-odd: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Local recognition of the odd geometric outer columns); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs new-perfect-hom-open-restricted-equiv-fields: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Restricted Hom equivalence and naturality fields); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-scalar-extension-chain-hom-diagram: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Scalar-extension Hom diagram for bounded projective complexes); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-open-stage-maps: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Compatible Hom maps for an open stage); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-local-comparison: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Local continuity implies bijectivity of products of pinned comparisons); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-perfect-chain-hom-presentation: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Chain-level affine perfect Hom presentation); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-local-rows: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Exact comparison rows before local continuity); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-continuity-affine: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Affine-open base case for perfect Hom continuity); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-pc-perfect-overlap-hom-continuity-data: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Types of prescribed overlap transports and Hom continuity); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-perfect-hom-presentation: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Affine module-derived presentation of perfect Hom transport); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-continuity-union: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Affine-open adjoining step for perfect Hom continuity); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-transition-comparison-diagram-core: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Core prescribed overlap transition construction); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-open-colimit-local-comparison: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Pinned local presentation of a single-open Hom colimit comparison); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-open-restricted-data-exists: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Existence of restricted representing data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-transition-comparison-core-stage: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Eventual overlap transition existence); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-base-change-scheme-comparisons: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Compatible scheme identifications for the explicit affine pushout diagram); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-specified-model-chain-comparison: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Affine scalar/geometric comparison from specified projective models); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-transport: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Compatibility of canonical Hom transport with increasing a finite stage); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even-zero: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Fixed even geometric outer column at index 0); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-perfect-hom-colimit: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Affine full faithfulness for a perfect complex over a filtered colimit); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-open-stage-presentation: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Stage and apex presentations for a shifted single-open Hom system); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-overlap-object-realization-core-data-family: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Stagewise overlap comparison data family); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-affine-model-hom-transport-assembly: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Derived module Hom transport from coherent geometric object comparisons); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Local recognition of the even geometric outer columns); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-descend-morphisms: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Descent of morphisms between perfect complexes); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs new-perfect-hom-open-restricted-pinned-equiv: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Identity-normalized restricted Hom equivalences); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-pc-perfect-hom-open-restricted-data-pinned: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Pinned equations for restricted representing data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs new-perfect-hom-open-restricted-limit-pinned: the existing statement concerns ordinary scheme/module complexes or their pinned comparison data (Apex equation for restricted representing data); the new statement is for coefficient sheaf dg modules, which retain the non-flat derived algebra and its action.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sfb-standard-normalized-resolution-filtered-colimit: the existing statement is continuity of homogeneous elements and equations in the coefficient dg algebra; the new statement is continuity of morphisms in sheaf dg derived categories.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sfb-affine-perfect-dg-finite-stage-descent: the existing statement descends affine finite-cell retract objects over a ring; the new statement compares Hom between already specified sheaf dg models on a possibly nonaffine open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs def-sfb-dg-coefficient-realization: the existing node defines the coefficient model and normalized arrows; it does not assert continuity of Hom.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-open-stalk-chain-map-equality: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-open-stalk-chain-map-lift: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-open-stalk-inverse-homotopies-spread: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-stalk-quasi-iso-detection: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-open-stalk-degreewise-lift: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-finite-projective-open-stalk-maps-lift: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-open-stalk-derived-hom-descent: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-open-stalk-reverse-components-lift: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-stalk-derived-hom-lift: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-bounded-free-stalk-model-spread: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-open-stalk-homotopy-spread: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-stalk-derived-iso-spread: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-perfect-sheaf-dg-hom-continuity vs lem-sc-perfect-open-stalk-degreewise-shrink: the existing statement spreads ordinary strictly perfect stalk data near a point; the new statement compares global sheaf dg Hom under coefficient enlargement on a fixed quasi-compact open.

lem-sfb-sheaf-dg-binary-gluing vs def-trf-ringed-derived-open-hom-restriction: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Canonical derived Hom restriction between opens of a ringed space); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-localization-nested-adjunction-mate: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Exact localization preserves a nested adjunction mate); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-mayer-vietoris-diagram: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Functor and cocone of geometric Mayer–Vietoris triangles); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-open-hom-scalar-mayer-vietoris: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Scalar compatible derived Hom boundary on any open union); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-local-models-stage-comparisons: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Stage object and compatible local limit comparisons); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-push-pull-cocone: the existing statement is about ordinary module-derived objects or their restriction/comparison data (A representing cocone for the stage pullback Hom functors); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-triangle-presented-rows-exact: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Exactness of rows presented by additive Hom of distinguished triangles); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-mayer-vietoris-comparison: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Pinned exact five-term comparison for perfect Hom on a two-open cover); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-mayer-vietoris-stage-rows-core: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Geometric Mayer–Vietoris rows with distinguished-triangle presentations); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-overlap-transition-comparison-diagram: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Finite-stage overlap descent with coherent comparison data); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-triangle-row-presentations: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Canonical five-term additive Hom row and its three triangle presentations); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-open-hom-triangle-realization: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Additive Hom identifications and maps for the open-cover triangle); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-descent-open-union: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Two-open induction step for perfect-complex descent); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-open-intersection-mate-iso: the existing statement is about ordinary module-derived objects or their restriction/comparison data (The canonical derived direct-image restriction mate is invertible on the other open); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-open-union-restriction-transport: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Transport the relative restriction diagram to opens of the union scheme); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-mayer-vietoris-geometric-columns: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Local recognition of the geometric outer columns); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-local-models-eventually-compatible: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Eventual compatibility of two prescribed local perfect models); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-supported-relative-open-gluing: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Supported perfect gluing using relative restriction functors); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-open-gluing-objects: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Object gluing with prescribed derived transition); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-scheme-derived-hom-restriction-transport: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Transport of derived local Hom restriction to open subschemes); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-relative-open-difference-diagram: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Direct-image difference diagram for two arbitrary ambient opens); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-open-gluing: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Gluing derived complexes and compatible morphisms on two opens); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-local-models-stage-gluing: the existing statement is about ordinary module-derived objects or their restriction/comparison data (PerfectLocalModelsStageGluing); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-open-shriek-derived-adjunction: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Derived extension-by-zero and restriction adjunction); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-mayer-vietoris-stage-rows: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Functorial exact stage Hom rows before colimit exactness); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-open-union-restriction-comparison-diagram: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Canonical comparison diagram for open union restrictions); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-open-cover-mate-complex-short-exact: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Termwise open-cover short exact sequence with prescribed adjunction mates); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-mayer-vietoris-triangle-cocone: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Coherent geometric Mayer–Vietoris triangle cocone before applying Hom); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-open-union-restriction-comparison-coherence: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Overlap coherence of supplied direct restriction comparisons); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-relative-open-gluing: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Derived gluing over a relative two-open union); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-local-models-descended-transition: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Descended overlap transition acting on every realization); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs def-pc-perfect-open-gluing-data: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Compatible local data for gluing a perfect pullback comparison); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-ambient-open-gluing-object: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Extend two-open derived object data to the ambient scheme); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-hom-mayer-vietoris: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Mayer–Vietoris sequence for derived Hom on a two-open cover); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-supported-map-affine-union-gluing: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Perfect supported source and compatible map on an affine union); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-open-cover-adjunction-triangle: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Canonical open-cover triangle expressed as adjunction mates); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-open-gluing-data-global-model: the existing statement is about ordinary module-derived objects or their restriction/comparison data (PerfectOpenGluingDataOfGlobalModel); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-open-union-hom-gluing: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Glue local maps between fixed ambient objects on an open union); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-scheme-derived-hom-gluing: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Lifting compatible local morphisms between global derived objects); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-open-cross-components-iso: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Invertibility of the derived overlap counit on the opposite open); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-mayer-vietoris-local-rows: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Exact comparison rows before local continuity); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-open-difference-diagram: the existing statement is about ordinary module-derived objects or their restriction/comparison data (The derived two-open difference diagram has split local normal forms); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-open-union-restriction-comparison-data: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Direct restriction comparisons on the inverse image opens of a union); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-overlap-transition-comparison-diagram-core: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Core prescribed overlap transition construction); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-hom-open-colimit-local-comparison: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Pinned local presentation of a single-open Hom colimit comparison); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-pc-perfect-descent-compatible-local-data: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Compatible local descent data at a common finite stage); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-open-intersection-iso-detection: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Restriction to an open intersection detects isomorphisms between open direct images); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sc-derived-open-intersection-essential-image: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Restricted open direct images belong to the overlap direct-image essential image); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs def-sfb-sheaf-dg-module-localization: the existing node defines sheaf dg data, signs and localization; it asserts no existence of a binary gluing object or compatible global map.

lem-sfb-sheaf-dg-binary-gluing vs lem-sfb-binary-coefficient-one-degree-quotient: the existing statement is a conditional one-degree/coherent-factorization assertion with coefficient targets; the new statement is unrestricted binary sheaf dg object-and-target-map gluing with no coefficient descent.

lem-sfb-sheaf-dg-binary-gluing vs lem-sfb-ringed-dg-scalar-adjunction: the existing statement gives scalar-extension adjunction and open restriction compatibility, not gluing of dg objects from separate opens.

lem-sfb-sheaf-dg-binary-gluing vs lem-sfb-perfect-arrow-coherent-factorization-locality: the existing statement is a conditional one-degree/coherent-factorization assertion with coefficient targets; the new statement is unrestricted binary sheaf dg object-and-target-map gluing with no coefficient descent.

lem-sfb-sheaf-dg-binary-gluing vs def-sfb-dg-coefficient-realization: the existing node defines sheaf dg data, signs and localization; it asserts no existence of a binary gluing object or compatible global map.

lem-sfb-sheaf-dg-binary-gluing vs lem-sp-derived-split-fibre-projections: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Projection formulas for the fibre of a split difference map); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sp-ringed-topos-fibre-restriction: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Isomorphisms from the direct-image fibre on both opens); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sp-ringed-topos-ordinary-cross-restriction: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Ordinary direct-image cross-restriction for subterminals); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sp-ringed-topos-cross-direct-image-restriction: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Cross-restriction of the derived direct-image overlap maps); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sp-ringed-topos-direct-image-restriction: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Fully faithful derived open direct images and cross-restriction); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs def-sp-ringed-topos-binary-descent-models: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Termwise slice restriction models and normalized adjunction map); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sp-ringed-topos-binary-descent: the existing statement is about ordinary module-derived objects or their restriction/comparison data (Binary derived open descent for modules on a ringed topos); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).

lem-sfb-sheaf-dg-binary-gluing vs lem-sp-subterminal-derived-image-calculus: the existing statement is about ordinary module-derived objects or their restriction/comparison data (K-injective derived direct-image comparisons for subterminal slices); it neither retains an arbitrary dg-algebra action nor states binary gluing in D_X(C).
