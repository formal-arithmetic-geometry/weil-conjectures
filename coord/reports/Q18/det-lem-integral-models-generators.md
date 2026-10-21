# Worker report: det-lem-integral-models-generators

## Files written

- dag/nodes/sec-six-functors-basics/det-lem-integral-models-generators.json: repaired stage-1 split, with its statement and Lean record unchanged. Six assembly steps, 2326 proof-text characters in total (previously 8408).
- dag/nodes/sec-six-functors-basics/lem-sfb-lattice-subquotient-filtration.json: statement-only supporting lemma, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-locally-free-derived-scalars.json: statement-only supporting lemma, unsplit, no Mathlib match.
- citations.json: every citation in every assembly step, backed by the verbatim statement of the cited node.
- searches.jsonl: real msearch.py searches, retained without rewriting; prepare.py: sandbox-local JSON preparation script.

## Attachments

None. A search of lean/WeilConjectures for the exact item id, integral_models_generators, integral generators and integral-lattice filtration terminology found no exact closed project declaration. The existing Sheaf theorem WeilConjectures.SixFunctors.integral_models_generators starts at lean/Sheaf/SixFunctors/IntegralModelsGenerators.lean:433 and contains sorry at line 459. It is not an attachment. No Lean was written or compiled.

## WANTED

None. The blueprint statement/proof and the Stacks sources used are present in literature/.

## What was wrong and what changed

This is the dedicated repair in coord/returns/Q18.md, headed det-lem-integral-models-generators, head 100b8fa832869045abf34c00f31fca7b56574dfe. Its sole numbered substance is the human's 2026-10-21 decision: the 8408-character proof was too coarse; retain the statement, expose its supporting arguments and leave a short assembly well below 3000 characters. The older stage-1 acceptance of 2026-10-17 does not supersede that later explicit return.

Initially I noticed the older acceptance first and preserved the existing node. The first dry run rejected that unchanged node. I then read the dedicated repair entry and carried out the finer split. No mathematical error in the item statement was found and no hypothesis or conclusion was changed. Existing source, import metadata and Lean record were preserved.

The filtration lemma records a finite filtration and its integral-lattice witnesses, not finite-cone generation of arbitrary derived objects. The locally free lemma is a general ringed-site flatness and derived-scalar comparison with no assumption that the new coefficient ring is flat. Neither restates a clause of the item. The main proof still performs the cone induction, finite descent and the construction/classical comparison of reductions.

The brief requires new nodes to be statement-only, status unsplit. Their complete proofs in words are therefore written below in this report, rather than putting forbidden proof steps in new node JSON. Each proof is under 3000 characters and uses existing nodes; neither moves the whole item into a new lemma. No gate or launcher script was altered.

## Proof of lem-sfb-lattice-subquotient-filtration

The standing schemes are Noetherian by pqf-lem-locnoeth-lft and finite type over the field. Apply sk-lem-stratified-lattice on S to L. Refine its finite lattice stratification to an ordered stratification using det-lem-coefficient-heart-common-stratification (1). On a refined piece restrict the lattice from the old piece. A local finite-free trivialization restricts, and exact monoidal inverse image with Cartesian coefficients (sk-prop-sfb-cartesian-coefficients) preserves its inclusion and localization identity. Thus the refined pieces still have lattices. They are locally closed in X: composing closed-in-open factorizations produces a closed immersion into an open subscheme, by lifting the second open and composing the affine quotient maps.

The lisse sheaf L is constructible by sk-def-sfb-constructible with one stratum. Apply det-lem-coefficient-heart-filtration on S. Push each short exact sequence through the exact a_! of lem-sfb-locally-closed-extension-coherence. The same coherence statement identifies a_!b_! with (ab)_!. Hence the quotients are a_{b!}(L|_{S_b}).

For each lattice M=L_{0,b}, operations (4) of det-lem-integral-models-operations gives
E_X tensor^L a_{b!}M = a_{b!}(E_{S_b} tensor^L M),
using sk-prop-sfb-cartesian-coefficients. By det-prop-sfb-qlbar-colimit-x-invert-ell, E_X and E_{S_b} are flat over their integral rings, so their tensor functors are exact. The exact-functor clause of sk-def-sfb-derived-categories identifies these derived tensors with ordinary tensors. Exactness of a_{b!} leaves the result in degree zero. The lattice identity now identifies the quotient with E_X tensor a_{b!}L_{0,b}. The pushed filtration starts at zero and ends at a_!L. All choices were finite and over the original E. This proves the statement, including rank zero and an empty filtration when S is empty.

Source: blueprint main-20261015, sk-lem-integral-models-generators.proof.md, paragraph (1). It is an agent-written proof; the new JSON has no proof_origin because it is an unsplit child, and its source points to precisely this paragraph.

## Proof of lem-sfb-locally-free-derived-scalars

On each trivializing slice, tensoring with M is the finite direct sum functor N mapsto N^{r_U}. It preserves kernels and cokernels. Tensor of sheaves is the sheafification of sectionwise tensor, and slice restriction commutes with it. A kernel or cokernel vanishes if it vanishes on a covering: each of its local sections vanishes on a further covering, hence is zero by the sheaf condition. Consequently exactness of tensoring with M holds on the whole site. This is the local sheafification argument of Stacks Tag 0GN1, sites-modules.tex, lemma-flatness-sheafification-refined; no assertion about all sections of M being free is used.

For every acyclic cochain complex C, the exact functor M tensor_R - preserves the kernel/image description of cohomology, so M tensor_R C is acyclic. Its terms are the total tensor of M[0] and C. Thus M[0] is K-flat by def-pc-kflat-complex; alternatively apply lem-pc-bounded-above-flat-kflat-site (Stacks Tag 06YQ) to this flat degree-zero complex. In computing left-derived extension of scalars, M[0] itself is an allowed K-flat resolution. Applying B tensor_R - gives exactly (B tensor_R M)[0] with its actual B-action. Independence of the chosen K-flat resolution and its natural comparison are the K-flat computation of sk-def-sfb-derived-categories (and lem-sfb-extend-scalars-kflat). Therefore the canonical comparison, not just an unspecified underlying R-module isomorphism, is invertible in D(Mod(B)) and natural in M. Finally a trivialization restricts its tensor to B|_U^{r_U}, using b tensor (x_i) mapsto (bx_i); the inverse sends (b_i) to sum b_i tensor e_i. This proves local finite freeness over B without requiring B flat over R.

Sources read: sites-modules.tex Tag 0GN1, lemma-flatness-sheafification-refined, and sites-cohomology.tex Tag 06YQ, lemma-bounded-flat-K-flat. The first proves local flatness; the already existing DAG node for the second gives K-flatness. The comparison is the direct K-flat-resolution computation. This general comparison is extracted from the flatness/reduction argument of blueprint paragraph (3), and is also useful in paragraph (1).

## Mathlib searches and blueprint search

For the filtration node I ran LeanFinder with two semantic phrasings, LeanSearch, Loogle with "Sheaf", "filtration", and a Mathlib-wide grep for integral/lisse/lattice filtrations. Hits were local-generator finiteness, algebraic ideal filtrations and ordered Hahn strata; none gives a stratified E-adic sheaf filtration with rationalized integral-lattice quotients. Source declarations SheafOfModules.IsFiniteType and SheafOfModules.free do not state this result.

For the locally free node I ran two semantic LeanFinder phrasings, LeanSearch, Loogle and two greps. The first Loogle query reported unknown identifier SheafOfModules.Flat; this is recorded as a failed name query, not as evidence that the theorem is absent. The second query returned SheafOfModules.IsLocallyFree and its constructors/instances. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean in full: it constructs local free data and quasicoherence, with no flatness or derived-scalar theorem. The semantic hits for mapFree/mapFreeIso in Free.lean are ordinary coproduct comparisons, not the claimed derived comparison. The grep in Algebra/Category/ModuleCat/Sheaf for IsFlat, isFlat, KFlat, kFlat returned no hits. The other grep's RingTheory/Flat/LocallyFree.lean hit concerns ordinary modules over rings and constant stalk rank, not module sheaves. None is an exact match or a one-line specialization of the new statement. The exact queries and actual hit summaries are recorded in the nodes and searches.jsonl; no search was invented and no service was represented as down when it returned successfully.

Before creating either node I searched the whole DAG and all imported blueprint statements via tools/blueprint_refs.py search for lattice, lattice filtration, lattice subquotients, finite filtration, locally free, locally finite free, derived extension of scalars, flat scalar and 0GN1. I also searched the live project Lean. No exact existing node was found. The blueprint ancestor command gives det-lem-integral-models-generators, so both children have that from.node, no intermediate via node, precise paragraph places and same_as []. The item is the imported node itself, so its from is correctly null. No unit realization field is changed: this item is not its unit's key statement.

## Not duplicates

lem-sfb-lattice-subquotient-filtration vs det-lem-coefficient-heart-filtration: the existing lemma starts with an adapted stratification and has lisse rational subquotients; it neither supplies integral lattices nor identifies the quotients with rationalized integral extensions.
lem-sfb-lattice-subquotient-filtration vs sk-lem-stratified-lattice: that node supplies lattices on strata, without a filtration after extension to X or its quotient identifications.
lem-sfb-lattice-subquotient-filtration vs sk-lem-coefficient-heart: that node provides filtrations by rational lisse extensions, not integral-lattice witnesses in their quotient identifications.
lem-sfb-lattice-subquotient-filtration vs det-sf-flat-model-generation: that node uses finite rings and flat constructible sheaves and includes retract closure; the new lemma is about lisse E-adic sheaves and integral-lattice quotients, with no retract closure.
lem-sfb-lattice-subquotient-filtration vs lem-sfb-coefficient-heart-sheaf-cone-witness: that node gives finite cone witnesses for shifted constructible sheaves, without integral lattices or sheaf filtrations with these quotient identifications.
lem-sfb-locally-free-derived-scalars vs lem-pc-bounded-above-flat-kflat-site: that node assumes termwise flatness and concludes K-flatness; it does not prove local finite-free flatness or the scalar comparison in D(Mod(B)). It is reused in the proof above, not duplicated.
lem-sfb-locally-free-derived-scalars vs lem-sfb-local-model-tor-bound-descent: that node assumes flat models on a finite cover of a scheme and gives local tensor/cohomology bounds; it does not handle arbitrary ringed sites and arbitrary nonflat target ring sheaves with the natural B-linear comparison.
lem-sfb-locally-free-derived-scalars vs lem-sf-integral-line-tensor-comparison-representative: that node has integral rank-one coefficients and K-flat complex tensor representatives; the new lemma permits arbitrary ring sheaves and locally varying finite ranks with arbitrary scalar maps.
lem-sfb-locally-free-derived-scalars vs lem-pur-finite-locally-free-etale-flat: that node treats finite constant coefficients on an etale scheme and has no general derived scalar comparison.

No existing source field has Tag 0GN1; there are no mandatory same-tag pairs for the new node. Existing uses of 06YQ were searched; its bounded-above-flat statement is already present and has not been recreated.

## Review by Q18

I read the three-level setting in SETUP.md, GOAL.md, the standing brief, worker role, stage-1 contract, delivery-errors B through E (including the merged copy), the current six-functors chapter/unit, the exact main-20261015 item statement/proof, the dedicated return and the current statement of every cited node. For the new filtration node I read blueprint paragraph (1) and the separate stratified-lattice, ordered-refinement, filtration, coherence, Cartesian-coefficient, localization-flatness and projection-formula statements. For the general locally free node I read Stacks 0GN1 and 06YQ, not only their titles. The proof paragraphs above state explicitly which part each source supplies; each is well below 3000 characters. Both children remain statement-only as required for delivery.

Assembly step 1 checks the hypotheses rather than treating a standing scheme as automatically proper or normal: finite type over a field gives local Noetherianity by pqf-lem-locnoeth-lft, and a finite affine cover gives quasi-compactness. def-weil-constructible-subset explicitly supplies the Noetherian constructibility facts. lem-sfb-locally-closed-extension-coherence explicitly supplies exactness, factorization independence and transitivity. sk-prop-sfb-cartesian-coefficients supplies the pulled-back ring identification, including exact inverse image. The same reasoning applies on every locally closed S.

Step 2 uses the new filtration's actual quotient statement, not a cone-generation conclusion hidden in its proof. det-cor-coefficient-heart-ii-generation states precisely generation by rational lisse extensions on Noetherian X. lem-sf-derived-ses-triangle supplies triangles for the filtration sequences. Starting at zero and successively adjoining a quotient is a finite induction; replacing finitely many lisse pieces in the original finite construction remains finite. This is the argument of clause (1), retained in the parent rather than restated as a new theorem.

Step 3 uses det-lem-coefficient-finite-descent-objects to choose one finite E and one K_E. sk-def-sfb-change-of-scalars supplies the left-adjoint/right-exact assertion, lem-sfb-qlbar-flat supplies left exactness, sk-def-sfb-derived-categories identifies the derived coefficient functor with its termwise exact functor, and lem-sf-exact-functor-derived-triangulated supplies shifts/triangles. The displayed forward/inverse pure-tensor maps obey the balancing relations and give the generator identity. They do not replace the condensed Qbar ring by the discrete algebraic closure.

Step 4 applies sk-def-sfb-constructible directly to the finite free constant local models, sk-def-sfb-bounded-constructible to the degree-zero complex, and operations (3) to a locally closed immersion between Noetherian schemes. The finite constant models satisfy the general bounded-constructibility condition as well; no new derived-completeness assumption is silently imposed. This retains the accepted source convention and statement.

Step 5 takes the quotient-ring identification specifically from constant-coefficients clause (1), the derived projection formula from operations (4), and the restriction of the coefficient ring from Cartesian coefficients. The new locally free theorem applies to the ring sheaf on S and B=(A_n)_S without asserting that B is flat. Its comparison is in the B-module derived category, so this is genuinely a derived reduction, not exactness of quotienting all integral sheaves.

Step 6 uses the ringed open/closed statement's restriction/vanishing identities. The three-piece stratification has constructible locally closed pieces on Noetherian X. sk-def-sfb-constructible and the bounded definition give the degree-zero constructibility, while def-weil-l-adic-coefficient-extension (4) supplies finiteness of A_n for n at least 1. A finite discrete ring is Noetherian because every ideal has finitely many elements. det-pe-constructible-comparison-classical assumes exactly a discrete Noetherian ring, qcqs X and locally constant finite-type restrictions on a constructible partition: these hypotheses have all been verified. Its conclusion is exactly that this sheaf is classical. It is declared as a generic off-unit tool, as it was already used by the unit's own comparison route.

I tested empty X and S, empty strata, rank zero and changing ranks, n=1, identity/open/closed immersions, and a nonnormal nodal scheme with monodromy multiplying a rank-one E-local system by ell. The last shows that a global lattice cannot replace the stratified lattices. For the new scalar lemma, B=R, B=R/I with I nonzero, the zero ring, and rank zero all give the correct formulas; no flatness of a quotient ring is required. The parent assembly is 2326 characters in six steps, the longest 494, and the two child arguments are written separately above. I checked C1/C4 by opening each cited statement; citations.json uses verbatim text. New ids were checked absent before creation, source/tag searches and conceptual duplicate comparisons are recorded above, new nodes have no proof steps, all changes stay in the sandbox, and there is no SGA citation. No target statement, Lean record, chapter route or unit route was changed.

## What remains

The two new statement-only nodes join the stage-1 queue under the normal one-level-split contract; their complete proofs above make them independently reviewable. No unfinished argument is hidden in the parent. Mechanical verification and delivery are recorded below after the required tool exits.

## Mechanical verification

The first substantive dry run found missing chapter/unit labels on the two new nodes. I added sec-six-functors-basics and sk-lem-integral-models to both; their statements and proofs in this report did not change. The existing classical-comparison off-unit citation is explicitly declared as a generic tool in split_report.tool_uses.

## Final reconciliation and verification

A concurrent sandbox update retained a six-step version of the same repair, with lem-sfb-lattice-subquotient-filtration and lem-sfb-locally-free-derived-scalars as the two new nodes. I read that version and restored the matching report rather than leaving the seven-step report for different helper names. The complete earlier attempt and alternate helper files are preserved outside dag/nodes/. The actual main proof is 2326 characters; it contains neither an extra scalar-six dependency nor a change to the statement. I independently read Bhatt–Scholze Lemma 6.8.13 (printed p. 61), including the stratification and filtration sentences, confirming the lattice route. I checked the local-flatness argument in Tag 0GN1, the K-flat definition and Tag 06YQ, and the statement of lem-pur-derived-change-of-rings, whose K-flat computation verifies the target-ring-linear comparison. I checked the main citations against the six actual steps. The two complete child arguments above are each under 3000 characters.

The first full dry run completed with OK (not pushed), at adeda564f55. This report reconciliation is followed by a fresh complete dry run before the push. No launcher script was edited, no compiler was run and no write was made to the shared read clone.
