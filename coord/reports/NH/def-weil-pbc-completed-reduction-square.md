# Stage-1 report: def-weil-pbc-completed-reduction-square

## Files written

- dag/nodes/sec-proper-base-change/def-weil-pbc-completed-reduction-square.json: definition, split; no Mathlib match. The statement now names all its input notions and comparison isomorphisms.
- citations.json: empty list, since the item is a definition and has no proof steps.
- report.md: this report. Searches are logged by msearch.py in searches.jsonl.

## New nodes

None. No Mathlib leaves created.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint id, completed-reduction terminology, completion/reduction terminology and candidate base-change names. ProEtale/Adic/BaseChange.lean defines adicBaseChangeMap and adicDerivedBaseChangeIso, but these concern weakly etale/open pullback and adic sheaves, not the specified completed integral reduction square. Its statements do not give sigma_n, tau_n, alpha_n and delta_n. The master reference search for the exact id likewise gave no attachment; master declarations would not certify finished proofs.

## WANTED

None. The actual assembly is in the available master blueprint node. The relevant underlying Stacks entries and dependency nodes are available locally.

## Corrections and scope

The imported definition introduced neither the coefficient datum nor the square, K, the four corners, or h_n and h'_n. Its sole dependency on the completed exchange did not define those names. I added explicit references and stated the inherited hypotheses of the corner/arrow construction: proper f, derived complete K, finite perfect quotients, and specified etale-origin witnesses for the reductions. These are the existing construction's context, not an extra assumption intended to obtain the target theorem. I retained all original displayed definitions and map directions.

The description of tau_n suppressed the factors of its completion/direct-image comparison. I made them explicit without creating a new lemma: chi is the derived limit of the perfect projection-formula maps followed by the inverse of the direct-image/limit comparison. Tau is rho after tensoring chi inverse. This is exactly the ordered comparison in the original definition, rather than an arbitrary isomorphism between these objects.

No claim about commutativity of the completed reduction square has been introduced. That is the distinct statement lemma-weil-pbc-completed-map-reduction, which depends on this definition and must not be cited here. All import and audit fields are preserved; the definition retains empty proof and proof_deps and null proof_origin. The unit's key theorem is not this item, so its realization record is untouched.

## Mathlib and duplicate searches

All Mathlib queries were run with /home/ubuntu/weil-launcher-nt/msearch.py and recorded with their exact query strings. LeanFinder was tried with two different phrasings. The first returned ordinary perfectoid, Witt-vector and affine-scheme pullback facts; the second returned ordinary adic completion evaluation and functoriality facts. Loogle's completion/tensor query returned AdicCompletion.ofTensorProduct and its finite-Noetherian equivalence; I read the construction in Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean. It is a linear map for ordinary modules, not derived completed pullback and ringed-topos direct image. The DerivedCategory/baseChange query had no hits. The precise grep had no hits; the second grep in CategoryTheory/Abelian returned stability of mono/epi maps under base change and preradical material, none matching the definition. LeanSearch returned Internal Server Error and is recorded as unavailable, not as absence.

Whole-DAG keyword searches found the existing corner/arrow, completion, reconstruction and direct-image nodes used here. Whole-blueprint searches 'completed reduction', 'reduction square', 'four edges', and 'completion direct' found no other node defining this same datum: completed-map-reduction is a commutativity theorem, and level-map-arrows concerns the uncompleted exchange. same_as is therefore empty. The item's imported blueprint.is is retained with from null as prescribed for imported nodes. There are no new-node duplicate pairs to distinguish.

## Unfinished work

None within this one-level definition split. The dependencies remain separate work items where not already finished; this report does not claim their proofs are finished.

## Review by NH

I read the chapter record, the sk-thm-properbasechange unit record and its three-step torsion route, and the master blueprint source of this definition. I also read the master sources for four-corners and four-arrows. They establish precisely the coefficient categories and names used here; this item supplies the completed comparison datum below the unit, not a replacement for the unit's torsion proof. There is no Stacks entry defining this assembled square. I read proetale.tex, lemma-naive-completion (099M) and lemma-pushforward-Noetherian-case (099N): the former identifies completion with the quotient-tower limit, and the latter states that direct image preserves completeness, completed pullback is pullback followed by completion, and direct image commutes with completion. I have not attributed finite-level reduction or this ordered four-edge assembly to those tags.

This item has no proof steps because it is a definition. In lieu of a vacuous step checklist I checked each part of its construction against every dependency statement. def-weil-pbc-adic-coefficient-datum supplies Noetherian A, I, finite perfect P_n, coefficient sheaves and strict reduction towers. def-weil-pbc-cartesian-square supplies the schemes and directions f,f',g,g'. def-weil-pbc-etale-origin-witness supplies the chosen etale antecedents needed by the completed exchange definition. def-weil-pbc-four-corners supplies A_n,B_n,C_n,D_n and E=Lg'^*K; def-weil-pbc-four-arrows supplies h_n:A_n to B_n and h'_n:C_n to D_n. These are statement dependencies, not citations of their proof internals.

For sigma, prop-weil-pbc-direct-image-limits explicitly says Rf_* takes complete K to a complete object. Thus lemma-weil-pbc-completed-pullback-reduction is applicable to Rf_*K, with codomain Lg_n^*((Rf_*K) tensor P_n)=A_n. I read both statements rather than relying on a definition of completeness alone.

For tau, E need not itself be complete. The generic perfect-complex assertion of lemma-weil-pbc-perfect-projection-formula applies to E with each perfect P_m, so pi_{f',E,P_m} is an isomorphism. Their functoriality gives a morphism of the reduction towers. prop-weil-pbc-direct-image-limits explicitly supplies lambda_E for every tower, without a completeness restriction on E. Taking the derived limit of pi and then lambda_E inverse gives chi from completed Rf'_*E to Rf'_*completed E. The quotient-tower model from def-weil-pbc-intrinsic-completion identifies the source; def-weil-pbc-completed-pullback identifies completed E with completed pullback of K. This is a composition of the supplied isomorphisms, not an uncited commutation theorem or a new node restating the item. For rho, lem-weil-pbc-finite-reduction-reconstruction explicitly gives finite reduction of the limit of the strict reduction tower of M=Rf'_*E. It does not require M already complete; it reduces its completion. I checked the inversion: chi inverse has source T and target completed M, so tensoring it has target completed M tensor P_n, exactly the source of rho. The order reversed would be ill-typed.

Finally alpha_n=h_n sigma_n has target B_n, delta_n=h'_n tau_n has target D_n, and tensoring the completed exchange of def-weil-pbc-completed-base-change-map has source S tensor P_n and target T tensor P_n. This uses the specified map, with no identification with a condensed-ring target from master. The lower edge is v'_n from four-arrows. All maps are morphisms in the finite coefficient category indicated by four-corners. I tested the construction when K is zero, for n=1, and for the identity square: compositions have the same sources and targets, and the comparison uses the same canonical reduction and projection maps. Neither normalization at n=0 nor completeness of uncompleted E was assumed. No additional statement node, hidden well-definedness axiom, cycle through completed-map-reduction, or unsupported proof step remains. I checked delivery-errors B through E against these exact statements and corrected the missing context and the suppressed ordered comparison.

## Dry-run verification

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py NH def-weil-pbc-completed-reduction-square --no-push` was rerun after the earlier transient preflight rejection and completed successfully: `OK (not pushed) deliver/NH/def-weil-pbc-completed-reduction-square at 0c2e66071d: preflight passed`. No files outside this sandbox were changed and nothing was pushed.

## Earlier second reading (a previous round; superseded)

- Item/context (no proof steps): compared every displayed map with the source blueprint def-weil-pbc-completed-reduction-square, order 1341, and the hypotheses with adic-coefficient-datum, cartesian-square, four-corners and four-arrows; PASS. The full datum includes torsion A/I, finite perfect P_n and positive indices; the specified etale antecedents are bounded below as required by etale-origin-witness. These are inherited input data, not additional target hypotheses.
- Construction S,T: checked completed-pullback and direct-image-limits against Stacks proetale.tex, Tag 099N, label lemma-pushforward-Noetherian-case; PASS. Completeness of Rf_*K is available; completeness of E is not assumed.
- Construction sigma_n: checked completed-pullback-reduction on the complete input Rf_*K and the literal A_n of four-corners; PASS, including sources and finite coefficient category.
- Construction chi: checked perfect-projection-formula for the possibly incomplete E, projection-formula-map and direct-image-limits for the strict E reduction tower; PASS after adding the map-definition citation. For a quotient q:P_{m+1} to P_m, the two adjoints are both the counit tensored with Lf'^*q; thus Rf'_*(1_E tensor q) pi_{m+1} = pi_m (1_M tensor q). This supplies the actual tower morphism, without an uncited compatibility theorem. The derived limit of its isomorphism and lambda_E inverse has exactly the specified direction.
- Construction completion/rho: read intrinsic-completion and koszul-reconstruction and compared proetale.tex, Tag 099M, label lemma-naive-completion; FIX. Intrinsic-completion defines a Koszul limit, not literally the quotient limit: now the quotient limit is written as a construction and its identification cites koszul-reconstruction. finite-reduction-reconstruction applies to the strict reduction tower of M=Rf'_*E, not to an arbitrary tower and not only to an already complete M.
- Construction tau_n: checked rho and chi inverse against their actual sources; PASS. Tensoring chi inverse takes T tensor P_n to completed M tensor P_n, then rho takes it to C_n. No inversion or ordering change was made.
- Construction alpha_n,delta_n,overline xi_n and lower edge: checked four-arrows and the specified ordered exchange in completed-base-change-map against the original source; PASS. Explicitly named v'_n as the lower edge. The definition does not assert the separate commutativity theorem completed-map-reduction, and does not cite it circularly. Projection-formula input was also checked against sites-cohomology.tex Tag 0944, label lemma-projection-formula, and Tag 0B56, label equation-projection-formula-map.
- New nodes: none; B1--B7 and the new-node deletion/Mathlib-leaf tests are vacuous. Independent whole-DAG and whole-blueprint searches for completed reduction, reduction square and four edges found only this definition and compatibility theorems, not another definition. Independent Mathlib searches used a sheaves-of-modules phrasing and a CategoryTheory grep; eight semantic hits concern ordinary sheafification/pullback and zero grep hits match derived completion. No Mathlib leaf or attachment found. Reading slopmaster2 Adic/BaseChange.lean lines 45--66 confirms the weakly etale adic-sheaf map is a different construction; no master sorry declaration is treated as closed.
- Edge cases: K=0 and empty X give zero sources/targets throughout; n=1 uses the same projection and inverse in the same order; n=0 is outside the datum. A finite field with I=0 gives P_n=A and a constant reduction tower, so completion and its comparisons reduce to the unit identifications. A finite field with I=A gives P_n=0 and only K=0 can be complete. The identity square uses the specified counits and projections without choosing a different comparison. PASS.

Changes: added the existing Koszul/quotient reconstruction dependency to repair a definition/theorem mismatch; added the projection-formula-map dependency to ground the tower compatibility in its adjunction construction; wrote the quotient-limit construction and the lower edge explicitly. No new node, target change, proof step, or Lean edit. The first worker's Review by NH remains above. citations.json remains [] because there are no proof-step citations.

Second-reader dry run: deliver.py NH def-weil-pbc-completed-reduction-square --no-push returned OK at 277d4f651e, preflight passed.


## Repair after mechanical landing refusal

The return for head cc85e6cafd records an independent PASS and no mathematical correction, but asks for repair against the current side tip. It gives no numbered fault or diagnostic for the landing refusal. I reread the current imported item and all fourteen dependency statements, the chapter and sk-thm-properbasechange unit, the master blueprint definition, Stacks proetale.tex labels lemma-naive-completion (099M) and lemma-pushforward-Noetherian-case (099N), and sites-cohomology.tex labels equation-projection-formula-map (0B56) and lemma-projection-formula (0944). The current completed-base-change-map specifies the ordered tower-limit exchange and confirms that limits are taken after restriction to ambient A coefficients. Upstream master Proper.lean instead states the condensed E and algebraic-closure targets with sorry; slopmaster2 Adic/BaseChange.lean defines weakly etale/open adic-sheaf comparisons. Neither is an attachment for this integral reduction datum.

This is a substantive clarification of the node, not an unchanged re-push: the construction now writes the quotient-transition naturality equation for pi, with the elementary argument that both adjoints are the same counit tensored with Lf'^*q_m. This previously appeared only in the second-reader report. It makes explicit why the indicated derived limit is applied to a tower morphism. I also specified the ambient A category for the limits and the finite P_n category for the reduced edges. No hypothesis, map, or dependency was changed, and no new node was needed.

## Review by NH

For this repair I checked C1/C4 at the only expanded construction: projection-formula-map defines pi by that exact counit adjunction, so the equality follows by functoriality of tensoring and adjunction, rather than from an uncited compatibility theorem. Perfect-projection-formula supplies the isomorphism for each P_m with no completeness hypothesis on E; direct-image-limits supplies lambda for every tower. Thus chi still goes from completed M to T, and rho after chi inverse still goes from T tensor P_n to C_n. Completed-pullback-reduction applies to Rf_*K because direct-image-limits supplies its completeness. Koszul-reconstruction identifies the quotient-limit model; finite-reduction-reconstruction applies to the strict reduction tower of M. The four-corners/four-arrows definitions give the endpoints of sigma, h, h', and v', and completed-base-change-map gives the specified upper edge. There are no proof steps, so citations.json remains [] and the B/D new-node checks are vacuous. For q an identity, successive quotient composites, K=0, I=0, and n=1 the new equality has the same adjoint on both sides. E need not be complete. I preserved the original blueprint route and the distinction between integral and condensed coefficients. All writes were confined to the sandbox; no Lean was written, compiled, or built.

## Second reading by NH

- Item definition: checked the coefficient, cartesian-square, etale-origin, corner, arrow, completion, and exchange hypotheses against the imported blueprint record and dependency statements; PASS, with all objects and map directions explicit.
- Construction of $S,T$: checked completed pullback and direct-image notation against the cited completion and direct-image nodes; PASS.
- Construction of $\sigma_n$: checked its complete input and finite reduction target against `lemma-weil-pbc-completed-pullback-reduction` and `prop-weil-pbc-direct-image-limits`; PASS.
- Construction of $\chi$ and $\tau_n$: checked the projection-formula tower, ambient coefficient category, inverse order, and finite reduction against the projection-formula, direct-image-limits, intrinsic-completion, Koszul-reconstruction, completed-pullback, and finite-reduction nodes; PASS.
- Construction of $\alpha_n$, $\delta_n$, and $\overline\xi_n$: checked endpoints and directions against four-corners, four-arrows, and completed-base-change-map; PASS; no commutativity assertion is added.
- New nodes: none; B1--B7, duplicate checks, and Mathlib-leaf checks are vacuous. Existing-node and Mathlib searches are recorded above and found no matching declaration.
- Edge cases: checked zero $K$, identity square, $n=1$, and constant/zero quotient towers; sources and targets remain well typed. No $n=0$ case is assumed.

Changes in this second reading: removed the explanatory adjunction proof from the statement while retaining the compatible-family equation needed to specify the tower morphism; this restores statement-only form under B1. No hypotheses, maps, dependencies, or target claims changed.
