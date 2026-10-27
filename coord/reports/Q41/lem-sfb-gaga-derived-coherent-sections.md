# Worker report: Q41

1. Files written: the item `lem-sfb-gaga-derived-coherent-sections` is split in ten steps with its statement unchanged. Four new statement-only nodes, all searched and unsplit, no Mathlib leaves:
   - `lem-sfb-analytic-pullback-exact`: analytic flat pullback preserves exact sequences of module sheaves.
   - `lem-sfb-analytic-closed-direct-image`: analytic tensor pullback commutes with a closed direct image, with its coefficient map.
   - `lem-sfb-analytic-projective-structure-cohomology`: holomorphic functions on complex projective space are constants and positive structure-sheaf cohomology vanishes.
   - `lem-sfb-projective-coherent-finite-twist-resolution`: finite resolution of an arbitrary coherent sheaf on P^n over a field by finite sums of twists.
   All node JSON files are under `dag/nodes/sec-six-functors-basics/`. `citations.json` records a verbatim statement quotation for every proof citation. `searches.jsonl` preserves the executed search results.
2. Attachments: none. Searching the item tag, GAGA and analytification in `lean/WeilConjectures/` found no finished project declaration. The existing projective resolution and graded syzygy declarations are about P^1/two variables, not arbitrary P^n.
3. WANTED: `literature/serre-gaga.pdf`, Serre, *Géométrie algébrique et géométrie analytique*, §9 Proposition 10, §10 Proposition 11, §11, §12 Theorem 1 and §13 Lemmas 4–5, printed pp.16–22, for the item and the three analytic nodes. I read the original online at https://www.numdam.org/article/AIF_1956__6__1_0.pdf without downloading it. Since it is absent locally, the item's `proof_origin.by` is `agent`.
4. No imported statement dispute. The statement is Serre's canonical coherent-cohomology comparison, restricted to finite locally free coefficients and expressed as the actual derived arrow. The proof now supplies the missing argument. I retained the statement, old searches and inherited blueprint chain. The source's downward induction using analytic cohomological dimension is replaced by a finite twist resolution over a field; this is an agent-written variant of the same hyperplane/presentation proof, not an appeal to GAGA for a larger class.
5. No unresolved mathematical step is left in the item. Supporting new nodes remain statement-only as required for a one-level split. The requested server dry run and delivery validate the packaged DAG separately; no Lean file or compiler is used.

## Proof route and searches

Serre §11 constructs the canonical cohomology maps and says that they commute with connecting maps. §13 first treats O on projective space, then uses the hyperplane sequence to move between consecutive twists, then presentations to reach arbitrary coherent sheaves. The item carries those arguments rather than citing a new GAGA theorem. Its last step applies the existing bounded-below cohomology criterion to the specified arrow in D^+(Vect_C).

For finite resolution I read local Stacks `algebra.tex`, Tag 00OQ, label `proposition-finite-gl-dim-polynomial-ring`; `constructions.tex`, Tag 03GM, label `lemma-quasi-coherent-projective-space`; and `coherent.tex`, Tag 01YS, label `lemma-coherent-projective`. These tags are ingredients, not a claim that 00OQ alone states the sheaf theorem. A finite section-tail module representing G exists by 01YS and 03GM. Its homogeneous generators give a graded free resolution with finite homogeneous kernels. Global dimension n+1 over k[z_0,...,z_n] bounds its projective dimension. A finitely generated graded projective module over this positively graded polynomial ring is graded free: choose a homogeneous basis modulo the irrelevant ideal, lift it, split the resulting surjection in the graded category, and use bounded-below graded Nakayama on the complementary kernel. Exact localization and taking degree-zero parts sheafify the resulting finite graded free resolution to the stated sequence of twists. This explanation belongs in the report; the new node itself contains only its statement.

Whole-DAG statement and source searches for GAGA, analytification, analytic exactness, closed analytic direct image, projective structure cohomology, twist resolutions, syzygy, and tags 00OQ/03GM/01YS preceded creation. The only analytic neighbours are the smooth analytification node, the Dolbeault resolution node, and the parent algebraic/Dolbeault comparison. None says the new exactness, closed-image, or projective vanishing fact. The Dolbeault resolution does not calculate the global Dolbeault cohomology of projective space. The P^1 resolution and its graded syzygy children do not state arbitrary-dimensional resolutions. The blueprint reference searches (GAGA, analytification, holomorphic, analytic, finite resolution, resolution by twists, graded syzygy, resolution, and 03GM) found no blueprint equivalent of the new statements. `blueprint_refs.py ancestor` reports null for this imported prerequisite chain, matching the item's existing null ancestor; I retained its via chain and placed the new nodes immediately below this item, with the direct-images proof (3) and the supporting GAGA subargument specified.

For each new node I ran two differently phrased LeanFinder searches, a LeanSearch query, Loogle and a Mathlib grep with msearch.py, and read the hits. Analytic searches returned scheme pushforward/flatness, analytic sets, or projective-spectrum definitions, not algebraic-to-holomorphic comparisons. Resolution searches returned abstract projective resolutions and sheaf finite presentation, not finite sums of twists. The exact queries and actual hit lists are in each node; I copied their results from the command's JSONL log. The item retains Q20's older searches as well as the new executed searches. No Mathlib match or unavailable-service claim has been invented.

## Review by Q41

I read Serre's original §§9–13 online, including the local-ring flatness reference, the closed-embedding stalk computation, the section formula in §11 and the whole projective-space proof. The exactness node is Proposition 10(a), valid for arbitrary module sheaves, not just coherent ones. The closed-image node is Proposition 11(i); its tensor formula is compatible with sections. During review I corrected its typing: the algebraic map to compare with a_(i_*F) is i_*a_F, after pi_Y direct image, not an ill-typed analytic pushforward of an algebraic map. The projective analytic calculation is the analytic part of Lemma 4, without importing its algebraic/analytic comparison conclusion. Its native statement is a vanishing/function calculation, not a per-degree substitute for a derived comparison. The finite-resolution node is the graded-syzygy consequence of the three Stacks sources explained above; I added 0 <= ell <= n+1 explicitly and removed a proof sketch from its statement. Each new node introduces its own spaces, coefficients, indices and hypotheses.

Step 1 uses exactly the embedding clause of the projective definition; the coordinate-Euler node supplies properness, Noetherianity and coherent O for both X and P. The proper-morphism definition supplies separated finite type. Finite local freeness supplies local finite free presentations and thus quasi-coherence and finite type; the locally Noetherian coherence equivalence then gives coherence. The closed-immersion coherent-cohomology node supplies coherence of i_*F. I did not infer smoothness from projectivity: I checked the affine charts and applied affine-space smoothness and locality. The smooth analytification theorem then supplies the actual closed holomorphic embedding. All those cited statements were opened.

Step 2 uses enough injectives on arbitrary ringed spaces, not a scheme-only version. Derived evaluation identifies O-module and constant-C-module cohomology with abelian cohomology on the terminal open. Naturality makes the identification C-linear. The single-object identification states the comparison with R^q explicitly. The injective lifting theorem requires a degreewise monic quasi-isomorphism; inverse image of the augmented injective resolution has both properties because inverse image is exact. The ringed acyclic-resolution theorem identifies precisely the coefficient-map-derived arrow with sections of its augmentation-preserving comparison. Injective C-module terms are abelian-global-acyclic by derived evaluation, so that hypothesis is verified, not assumed from forgetfulness preserving injectivity. Smallness is satisfied by the set of open subsets in an enlarged common universe. The arrow equality is checked after forgetting C-linearity, which is faithful on the induced cohomology maps.

Step 3 uses the delta-pullback theorem's explicit connecting-map equality and its morphism-of-short-exact-sequences clause. The analytic exactness node ensures that the lower row really is short exact; the coefficient maps make the morphism from the inverse-image row. The long-exact theorem applies because sections are additive and left exact, checked sectionwise, and injectives were established in Step 2. This avoids the scheme-only module-cohomology pullback theorem, which would not apply to an analytic ringed-space map.

Step 4 uses the closed-embedding cohomology statement on both topological spaces, together with derived evaluation for coefficient conventions. The new closed-image statement explicitly identifies coefficient maps, not just objects. The acyclic-resolution map theorem ensures that the sectionwise square is the square of the canonical higher maps. The closed analytic embedding hypothesis comes from Step 1 (and from the same chart argument for the hyperplane). Thus no unspecified choice of cohomology isomorphism is substituted for the required map.

Step 5 writes out the finite exact-sequence diagram chase. It is elementary linear algebra and introduces no new lemma node. The three positions of the unknown comparison are handled by choosing the corresponding five consecutive terms; at q=0 the missing groups are zero.

Step 6 uses the algebraic projective-twist calculation exactly at d=0, including its separate n=0 clause. The analytic node supplies constants and positive-degree vanishing. Smooth analytification identifies O^an with O by multiplication. The degree-zero map is literally c -> 1 tensor c -> c, so it is the identity and all other maps are between zero groups. The n=0 twist assertion follows from its single chart frame, not a positive-dimensional formula.

Step 7 checks every hypothesis of the fixed-hyperplane statement: n>=1; coherent E=O and G=O_H; coordinate section nonzero; multiplication injective in polynomial charts and their localizations. The transition functions identify the restricted twists, and H is the smooth projective (n-1)-space. The induction hypothesis is all twists and all degrees in dimension n-1. With the base comparison for d=0, the two-of-three argument propagates both upwards and downwards in the integer d. The exact hyperplane-sequence node states the short exact sequence actually used; none of its additional surjectivity conclusions is needed.

Step 8 checks finite sums by their injections and projections and writes the inverse blockwise. This is an elementary finite-biproduct argument, including an empty sum. Step 9 uses the new resolution node over the field C and coherent G, defines its successive kernels, and checks the last kernel is the last resolution term. Analytic exactness was deliberately stated for all modules, so no unproved coherence assertion about intermediate kernels is needed. Backwards induction transfers comparison along every short exact sequence. Step 10 uses the existing criterion for D^+ of an arbitrary abelian category on the actual g_F: positive cohomology was computed in Steps 2–9, negative cohomology vanishes from nonnegative injective resolutions. It proves exactly the canonical derived isomorphism in the item.

I tested the new statements and argument at n=0, rank zero, zero modules, the empty X, a closed point in projective space, negative twists, and P^1 at d=-1 and -2 (where top cohomology first becomes nonzero). The hyperplane sequence includes its H^0 boundary and therefore does not assert false analytic vanishing for all twists. Finite resolution is asserted on P^n itself, not on an arbitrary possibly singular projective X. Closed direct image is restricted to closed embeddings; no assertion for open extension by zero is used. Varying ranks and component dimensions require no uniform rank assumption. No source or imported-statement error was found.

Against delivery-errors B–E: every new node is statement-only and self-contained, with source places and executed searches; the item carries the induction and assembly rather than restating itself through a new GAGA node. The explicit source-tag overlap comparisons below distinguish the Stacks ingredients from the new finite-resolution assertion. Every proof citation has a verbatim statement quote in citations.json. All non-elementary uses have cited statements; the two elementary steps include their actual argument. I checked the step lengths (all below 2000 characters), the absence of a hidden general comparison assertion in a long step, and the required edge cases. Generic off-unit cohomology and projective-space tools are declared in split_report.tool_uses, rather than silently changing the unit route. The item statement and its coefficient conventions were not weakened. These are my own checks for this direct delivery, not a claimed second-reader review.

## Not duplicates

lem-sfb-projective-coherent-finite-twist-resolution vs lem-trf-polynomial-strict-local-coordinate-dimension: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-proj-serre-h1-vanishing: the existing statement is a cohomological bound, finiteness or eventual-vanishing assertion; it has no finite twist-resolution conclusion.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-pc-j4-closed-immersion-twist-cohomology-bound: the existing statement is a cohomological bound, finiteness or eventual-vanishing assertion; it has no finite twist-resolution conclusion.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-pc-j4-closed-immersion-twist-vanishing-step: the existing statement is a cohomological bound, finiteness or eventual-vanishing assertion; it has no finite twist-resolution conclusion.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-polynomial-dimension-one: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-twisted-section-finite-coordinates: the existing statement concerns finite-dimensional sections or scalar coordinates/actions on P^1, not exact resolutions by twists on arbitrary P^n.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-pc-d2-nonnegative-projective-twist-vanishing: the existing statement is a cohomological bound, finiteness or eventual-vanishing assertion; it has no finite twist-resolution conclusion.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-section-module-construction: the existing statement constructs or controls graded sections on P^1; it does not give a finite sheaf resolution on arbitrary P^n.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-section-coordinate-surjective: the existing statement constructs or controls graded sections on P^1; it does not give a finite sheaf resolution on arbitrary P^n.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-section-module-component-finite: the existing statement constructs or controls graded sections on P^1; it does not give a finite sheaf resolution on arbitrary P^n.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-section-action-laws: the existing statement constructs or controls graded sections on P^1; it does not give a finite sheaf resolution on arbitrary P^n.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-pc-c2-closed-immersion-fixed-degree-vanishing: the existing statement is a cohomological bound, finiteness or eventual-vanishing assertion; it has no finite twist-resolution conclusion.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-pc-d2-closed-immersion-twist-acyclic-presentation: the existing statement gives one coherent presentation with a finite/eventually acyclic cohomology source; it does not give a finite exact resolution ending in a sum of twists.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-twisted-sections-finite-dimensional: the existing statement concerns finite-dimensional sections or scalar coordinates/actions on P^1, not exact resolutions by twists on arbitrary P^n.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-twisted-sections-constant-action: the existing statement concerns finite-dimensional sections or scalar coordinates/actions on P^1, not exact resolutions by twists on arbitrary P^n.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-pc-u3-projective-finite-cohomology-presentation: the existing statement gives one coherent presentation with a finite/eventually acyclic cohomology source; it does not give a finite exact resolution ending in a sum of twists.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-section-module-tail-finite: the existing statement constructs or controls graded sections on P^1; it does not give a finite sheaf resolution on arbitrary P^n.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-pc-p2-projective-finite-source-cohomology-segment: the existing statement gives an exact cohomology segment with a finite source; it does not give a finite exact resolution of sheaves by twists.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-polynomial-regular: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-pc-m1-projective-affine-finite-cohomology-independent: the existing statement is a cohomological bound, finiteness or eventual-vanishing assertion; it has no finite twist-resolution conclusion.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sfb-projective-twist-euler-section-uniqueness: the existing statement gives twisted cohomology finiteness, Euler polynomials or coordinate-ring dimensions; it does not give a finite twist resolution.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sfb-standard-proj-coherent-section-finiteness: the existing statement gives finite generation of a section-tail module on general standard Proj; the new statement needs a finite free graded resolution over a polynomial ring and its exact sheafification.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sfb-projective-coordinate-ring-euler-polynomial: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sfb-compatible-regular-local-field-presentations: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-weil-pbc-closed-immersion-serre-vanishing: the existing statement is a cohomological bound, finiteness or eventual-vanishing assertion; it has no finite twist-resolution conclusion.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-weil-pbc-field-regular-ring: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-weil-pbc-polynomial-ring-maximal-chain-height-difference: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-weil-pbc-global-complete-intersection-local-regular-sequence: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-weil-pbc-finite-type-domain-dimension-local-ring: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-weil-pbc-polynomial-ring-field-regular-ring: the existing statement concerns regularity, dimension, prime chains or local algebraic presentations; it does not construct a coherent-sheaf resolution on projective space.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-graded-resolution: the existing resolution is for P^1 only; the new theorem covers every n>=0 and is needed before the dimension-independent GAGA argument.

lem-sfb-projective-coherent-finite-twist-resolution vs lem-sc-p1-graded-syzygy: the existing graded free resolution is over k[x_0,x_1] only; the new statement resolves coherent sheaves on arbitrary P^n.
