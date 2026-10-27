## Worker report

Files written:
- dag/nodes/sec-deligne-laumon-a1/lem-per-varying-site-system-injective-resolutions.json: split, statement unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-varying-site-evaluation-adjoints.json: one new statement-only unsplit node, no Mathlib match.
- citations.json: every proof-step citation has a verbatim statement quote.

Attachments: none. The project source was searched for the blueprint tag, varying-site systems, system injectivity and evaluation adjoints. Existing EtaleCoefficientInjectiveSystem declarations concern directed preorders of schemes and give only stagewise injectivity, not all clauses here. Mathlib Evaluation.lean:38-67,88-115 covers a single fixed target category, not varying-site sheaves. The two semantic phrasings, Loogle and grep were run with msearch.py and read; exact queries and actual returned records are in searches.jsonl and the node records. The item's previous searches are preserved, with additional searches from this attempt.

WANTED: none.

What was wrong: no statement dispute was found. The unsplit item had no proof. Stacks 0EXZ gives componentwise injective embeddings under its stronger setup; it does not itself say that the embedding target is injective in the category of all systems. The proof supplies that missing categorical assertion by cofree evaluation and products. It also supplies the free evaluation argument needed for evaluation to preserve injectivity. This is explicitly an agent generalization of the Stacks constructions, not a claim that 0EXZ states the item verbatim.

Unfinished: the new adjunction node is intentionally statement-only. No other part of the one-level split remains open.

## New nodes

lem-per-varying-site-evaluation-adjoints: the free/cofree evaluation adjunctions and their transition and Hom formulas for arbitrary coherent small varying-site diagrams. It asserts none of the item's abelian, injectivity or resolution conclusions. It is a genuine auxiliary construction, not a renamed clause of the item. No new Mathlib leaves.

The argument retained for its future splitter is the universal-property calculation. On the free side the composition comparison sends the a-summand to the a composed with c summand. Restriction to the identity summand and extension by the coefficient transitions are inverse because the identity transition is the identity and the cocycle is the composition law. On the cofree side use product projections, direct-image composition, and the inverse-image/direct-image counit. Transposing each factor changes the system compatibility equation into the coefficient cocycle. Projection to the identity factor and extension by all transposed transition maps are inverse; the triangle identities prove the identity case. Checking each summand or each projection reduces associativity to the given pseudofunctor coherence. None of this assumes inverse image preserves products.

## Review by Q79

I read the item and its parent continuity node, the chapter and unit records, and the current latest blueprint proof of lem-per-artin-gabber-affine-curve, especially Step 3. This is a generic bounded-below resolution tool below the completion/continuity branch of that route; no chapter or unit assertion is changed. The current blueprint does not supply the proposed general system theorem as a separate statement. The inherited blueprint ancestry is retained and the new node's via list starts with this item.

For the item I read sites-cohomology.tex, Tag 0EXZ (lemma-colim-sites-injective), including the displayed product, the adjoint definition of its factors and its identity-factor monicity argument. I read derived.tex, Tag 013K (lemma-injective-resolutions-exist), all three clauses and the reduction of clause (3) to 05T6. For the new node I additionally read spaces-simplicial.tex, Tag 09WG (lemma-restriction-to-components-site), parts (5)-(7) and its coproduct Hom calculation, and 09WH for the reason to require an exact left adjoint. The arbitrary-small-category formulation and the cofree Hom formula are agent generalizations of those explicit constructions. I also read homology.tex Tags 0137 and 015Z, injectives.tex Tag 01DP, and sites-modules.tex Tag 03CO, to check the existing tools and the exactness argument.

Step 1 uses the actual abelian-and-enough-injectives conclusion of lem-weil-pbc-site-sheaves-enough-injectives and the kernel/cokernel preservation stated in lem-weil-pbc-site-pullback-abelian-exact. The kernel restriction and cokernel descent are written out; the component universal properties enforce the system morphism condition. The cited def-sp-abelian is used only for its definition, after the properties have been established. The inverse of a componentwise invertible system map is checked by composing its compatibility square with the inverses. This proves componentwise exactness rather than assuming it.

Step 2 uses the new node's asserted adjunctions and arrow-indexed free formula. The filtered-colimit node supplies arbitrary small colimits and exact filtered colimits on an arbitrary site. The finite subsets of each Hom set are a small filtered poset, including the empty-Hom case with one empty finite subset. Finite biproducts are exact, inverse images are exact, and taking their filtered union gives exactness of the free sum. The general adjoint lemma lem-exc-rg-right-adjoint-preserves-injectives needs only preservation of monomorphisms, which has been proved. I removed an unnecessary use of the general theorem that left adjoints are right exact, so no uncited adjoint-exactness fact remains.

Step 3 uses the enough-injectives clause of the site lemma to choose u_i, and the NEW node's cofree Hom formula to produce compatible maps into R_i A_i. The same adjoint injectivity lemma applies since evaluation was proved exact in Step 1. The sheafification-exact node explicitly states that arbitrary limits of abelian sheaves are sectionwise, so all products needed here exist. The system product construction is written by its projections; its compatibility follows by projection cancellation, and its universal property follows from the same test. The product-injectives node concerns products in ANY abelian category, so it applies to S, not just to an individual fibre. The identity factor really recovers u_j, which proves monicity without exact products. This is the point that would have failed if I had cited merely the stagewise injectivity assertion of 0EXZ.

Step 4 uses exactly clause (3) of the existing complex-injective-resolution-mono statement: the prescribed SAME integer lower bound, degreewise monicity and a quasi-isomorphism into termwise injectives. There is no extra Grothendieck, filteredness or nonempty-index hypothesis. Exact-functor-preserves-homology states the homology comparison used to get each component quasi-isomorphism. Component injectivity uses Step 2, not an unproved property of arbitrary injective resolutions.

Small cases: empty I gives the zero category, empty factor sets give zero sheaves, a discrete category gives independent sheaves and identity adjoints, and one nonidentity arrow gives free (A,f* A) and cofree (f_* B,B) in the appropriate direction. For a one-object category with many endomorphisms, the free and cofree constructions retain every arrow, so restriction to the identity and extension by the action still give the usual free/cofree action adjunctions; no preorder hypothesis was smuggled in. Arbitrarily large Hom sets are sets in the fixed size convention. A zero complex remains eligible for every bound b. These checks found no need to alter the statement.

I checked B--E with the files open: the one new node introduces every site, category, functor and compatibility law, cites size and site definitions, contains only a statement with empty proof/dependencies, and has actual logged Mathlib searches. It is neither a fixed-category evaluation specialization nor the existing simplicial restriction theorem (the index category is arbitrary, and both adjoints are asserted). Proof citations use node statements, not their proofs. All quotes in citations.json were checked as literal substrings. No proof step exceeds 2000 characters, no new node is a clause of the item, and no SGA source is used. Off-unit generic tools are identified in split_report.tool_uses where needed; no tool_uses maintainer field was written.

## Not duplicates

lem-per-varying-site-evaluation-adjoints vs lem-per-finite-cover-derived-sections-continuity: the existing theorem is a derived sections continuity isomorphism under cofiltered finite-cover hypotheses, and depends on this item; the new underived adjunction node assumes no colimit site and creates no dependency back to continuity.

lem-per-varying-site-evaluation-adjoints vs lem-per-varying-site-system-injective-resolutions: the existing item concludes abelianness, enough injectives and resolutions; the auxiliary instead supplies the two explicit evaluation adjunctions that the proof uses, and asserts none of those conclusions.

lem-per-varying-site-evaluation-adjoints vs def-weil-pbc-etale-coefficient-injective-target: the existing statement concerns outgoing-arrow product injective target for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-arrow-product-compatible-transitions: the existing statement constructs or verifies combined arrow-product transitions for a fixed strict diagram; it does not state the free evaluation functor or the cofree evaluation Hom adjunction for arbitrary coherent systems.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-arrow-product-transitions-cocycle-law: the existing statement constructs or verifies combined arrow-product transitions for a fixed strict diagram; it does not state the free evaluation functor or the cofree evaluation Hom adjunction for arbitrary coherent systems.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-arrow-product-transitions-cocycle: the existing statement constructs or verifies combined arrow-product transitions for a fixed strict diagram; it does not state the free evaluation functor or the cofree evaluation Hom adjunction for arbitrary coherent systems.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-arrow-product-transitions-existence: the existing statement constructs or verifies combined arrow-product transitions for a fixed strict diagram; it does not state the free evaluation functor or the cofree evaluation Hom adjunction for arbitrary coherent systems.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-cohomology-colimit-of-sites: the existing statement concerns cohomology on a colimit of sites in a colimit-site/cohomology construction; neither its conclusion nor its hypotheses give the two underived evaluation adjunctions for an arbitrary coherent small site diagram.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-colimit-of-sites-injective-system: the existing statement concerns embedding a system of abelian sheaves on an inverse system of sites into a system of injectives in a colimit-site/cohomology construction; neither its conclusion nor its hypotheses give the two underived evaluation adjunctions for an arbitrary coherent small site diagram.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-colimit-sites-acyclic-replacement: the existing statement concerns acyclic replacement and pointwise boundaries for a colimit-site coefficient system in a colimit-site/cohomology construction; neither its conclusion nor its hypotheses give the two underived evaluation adjunctions for an arbitrary coherent small site diagram.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-colimit-sites-boundary-diagrams: the existing statement concerns boundary diagrams of normalized compatible short exact systems in a colimit-site/cohomology construction; neither its conclusion nor its hypotheses give the two underived evaluation adjunctions for an arbitrary coherent small site diagram.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-colimit-sites-cohomology-diagram: the existing statement concerns cohomology diagram and comparison cocone for a unital-in-degree coefficient system in a colimit-site/cohomology construction; neither its conclusion nor its hypotheses give the two underived evaluation adjunctions for an arbitrary coherent small site diagram.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-colimit-sites-connecting-ladder: the existing statement concerns lower-degree connecting ladder for colimit-site cohomology in a colimit-site/cohomology construction; neither its conclusion nor its hypotheses give the two underived evaluation adjunctions for an arbitrary coherent small site diagram.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-colimit-sites-exact-ladder: the existing statement concerns exact cohomology ladder before finite-stage correction in a colimit-site/cohomology construction; neither its conclusion nor its hypotheses give the two underived evaluation adjunctions for an arbitrary coherent small site diagram.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-colimit-sites-short-exact-systems: the existing statement concerns normalized compatible short exact coefficient systems in a colimit-site/cohomology construction; neither its conclusion nor its hypotheses give the two underived evaluation adjunctions for an arbitrary coherent small site diagram.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-colimit-system-product-transitions: the existing statement constructs or verifies combined arrow-product transitions for a fixed strict diagram; it does not state the free evaluation functor or the cofree evaluation Hom adjunction for arbitrary coherent systems.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-coefficient-injective-cokernel-system: the existing statement concerns compatible stage cokernels of an injective coefficient replacement for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-coefficient-injective-system-data: the existing statement concerns injectivity of the outgoing-arrow product target for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-coefficient-injective-system-embedding: the existing statement concerns transitions and monomorphic embeddings for the specified product target for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-coefficient-injective-system: the existing statement concerns compatible injective embeddings of étale coefficient systems for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-coefficient-product-composition-component: the existing statement concerns composition calculation at one outgoing-arrow factor for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-coefficient-product-embedding-compatibility: the existing statement concerns compatibility of explicit product embeddings with the coefficient transitions for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-coefficient-product-identity-component: the existing statement concerns identity calculation at one outgoing-arrow factor for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-coefficient-product-transition-laws: the existing statement concerns identity and composition laws for explicitly constructed outgoing-arrow product transitions for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-limit-acyclic-replacement: the existing statement concerns etalelimitacyclicreplacement for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-limit-cohomology-connecting-ladder: the existing statement concerns successor-degree connecting ladder for etale inverse-limit cohomology for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-limit-cohomology-degree-zero-descent: the existing statement concerns degree-zero representatives for etale inverse-limit cohomology for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-limit-compatible-exact-systems: the existing statement concerns etalelimitcompatibleexactsystems for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-limit-replacement-exact-systems: the existing statement concerns etalelimitreplacementexactsystems for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-replacement-stage-diagram: the existing statement concerns the stage diagram of a compatible étale injective replacement for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-etale-system-cone-functor: the existing statement concerns pullback of a compatible étale system to an arbitrary cone for scheme-indexed etale coefficients (typically a directed preorder); it does not give both evaluation adjunctions for arbitrary coherent small diagrams of sites.

lem-per-varying-site-evaluation-adjoints vs lem-weil-pbc-transition-identity-defect: the existing statement concerns identity transition defect vanishes in a colimit-site/cohomology construction; neither its conclusion nor its hypotheses give the two underived evaluation adjunctions for an arbitrary coherent small site diagram.

lem-per-varying-site-evaluation-adjoints vs lem-trf-total-site-component-restriction: the existing theorem is restricted to simplicial sites and only supplies the free adjoint; the new node treats arbitrary small index categories and also the cofree adjoint with explicit Hom formulas.

lem-per-varying-site-evaluation-adjoints vs lem-trf-total-site-derived-components: the existing theorem compares derived direct images of simplicial diagrams; the new node is an underived pair of adjunctions for arbitrary index categories, with no map between diagrams.

