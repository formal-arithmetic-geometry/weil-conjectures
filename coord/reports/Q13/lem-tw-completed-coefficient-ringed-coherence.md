## Files written

- dag/nodes/sec-purity-real-sheaves/lem-tw-completed-coefficient-ringed-coherence.json: statement, split, no Mathlib match for the complete item.
- citations.json: a verified verbatim excerpt for every cited node in every proof step.
- No new nodes and no Mathlib leaves created. The item's statement, statement dependencies, creation metadata and blueprint ancestry are unchanged.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint id and by completed coefficient, completedIntegralSheaf, structural composition and localization terminology. CompletedIntegral.lean constructs the limit and its reduction compatibility, but does not state both the composition and arbitrary weakly etale slice clauses. Its finished elementary declarations do not attach this item. Other completed-exchange results concern different derived operations.

## WANTED

None.

## Problems and corrections

The item was statement-only, not an interrupted saved split: the sandbox initially contained only dispatcher marker files, with no nodes, report or searches. No delivery or search process for this item remained active. No imported statement error was found. An arbitrary scheme inverse image need not preserve countable limits: Step 1 instead maps into the target coefficient limit, using the cone of the finite coefficient maps. Slice restriction does preserve these limits, because the relevant sections are literally the same. These are different arguments.

The source note mentions Bhatt--Scholze Proposition 6.6.11 and Remark 6.8.15. I read them on printed pp. 54 and 62 respectively. They motivate the stratified-model and ordinary ringed-operation application but do not themselves state this coefficient-coherence lemma. The proof is explicitly agent-written, using the generic Stacks localization construction and the existing finite constant-ring composition node. No noetherian, invertibility-of-ell, flatness, or coefficient-isomorphism hypothesis from those applications is imported into this generic statement.

## Unfinished work

None in this split. Existing dependency nodes retain their own work. No Lean file was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes. The existing finite constant-ring composition, ringed-site localization, weakly etale site-localization and sectionwise-limit nodes are cited directly, rather than creating duplicates or moving a clause of this item to another node.

## Review by Q13

I read delivery-errors B--E in both copies, the unit and chapter, the current blueprint proof of lem-tw-dual-negation, and the actual statements of all seven distinct nodes cited in this proof. The ancestry leads through the ordinary integral pullback and stratified-model branch to the blueprint's dual-stalk claim. The three generic off-unit theorem uses are declared in split_report.tool_uses: finite constant-ring composition, weakly etale localization, and localization of arbitrary ringed-site morphisms. They support the inherited route and replace no unit argument. There is no new-node relabelling or hidden standalone lemma.

For Step 1 I checked def-weil-proetale-inverse-image's precise constant-presheaf extension and adjunction, and def-pur-sheaf-inverse-limit's limit universal property and ring-sheaf clause. Naturality in reduction is justified by the two maps extending the same scalar quotient map. The compatible cone is on the target site, so its universal property gives existence as well as uniqueness of c_g without assuming inverse image commutes with infinite limits. This also explains that no unspecified ring-sheaf map is chosen.

For Step 2 I read lem-pur-proetale-constant-ring-composition, which states the exact finite-ring equation for the specified geometric inverse-image compositor, and def-weil-l-adic-coefficient-extension, which supplies finite R/t^n for every positive n. The displayed calculation uses naturality at pi_Z,n with the correct source (kh)^-1 B_Z and target C_n,T. Joint uniqueness is from the ring limit, not from a claim that any finite projection is injective. Step 3 uses the same compositor's definition via the direct-image fibre-product comparison. Iterating the formula is elementary: the canonical fibre-product maps have the same projections, and their inverse-image mates are the specified comparison. Thus equal composites give equality of every finite projection and then of maps into B_T. No abstract coherence theorem is assumed without this calculation.

For Step 4 I read all of lem-weil-proetale-weakly-etale-localization, especially clauses (1) and (2). It gives the site equivalence for any site object, not just an open immersion, and the constant-ring comparison is identity on constants. def-weil-proetale-inverse-image supplies well-defined base change of site objects, so V is eligible even when U or V is not noetherian. def-pur-localized-ringed-site gives sectionwise restriction, and def-pur-sheaf-inverse-limit explicitly gives sectionwise ring limits. These statements justify the written sectionwise calculation, including the ring operations, transitions and coordinate projections. No identification with a discrete constant R-sheaf is made.

For Step 5 I read Stacks Tag 04J0, sites-modules.tex lemma-localize-morphism-ringed-sites, including its entire proof, and the existing node lem-weil-pbc-localize-ringed-site-morphism. That node states the exact inverse-image square and the structural map obtained by restricting c_g; it imposes no invertibility on it. The induced site functor at H over U is identified explicitly by T times_W H = V times_U H. The finite constant-map adjunct is specified on the same constants over that fibre product as the adjunct defining c^v. Uniqueness of the presheaf-to-sheaf extension proves the finite-map comparison. Naturality with pi and the earlier sectionwise limit identification then yield the displayed projection equation for the restricted completed map; limit uniqueness identifies it with c_v. This argument uses the cited statements, not data hidden in their proofs.

For the sectionwise facts I read Stacks Tags 03CO and 03DB in sites-modules.tex (lemma-limits-colimits-abelian-sheaves and lemma-limits-colimits), including the limits argument. Ring operations on the sectionwise limit are coordinatewise; the existing definition explicitly includes ring sheaves. I also read the proetale.tex small-site definition and the functoriality/localization discussion. The item source is accurately marked as an agent extraction, not falsely attributed verbatim to Bhatt--Scholze.

I tested identity maps, empty schemes and empty U, the first quotient n=1, and R=Z_l. The argument permits the zero ring of sections on the empty object. There is no connectedness assumption in the constant-section comparisons, and no argument assumes all sections of a constant sheaf are globally constant: equality is checked on the constant presheaf using the defining sheafification extension property. All five proof steps are elementary relative to their cited interfaces; each is below 2000 characters. None hides a comparison theorem beyond those interfaces. Every citations.json entry was verified as a literal substring of the live cited statement.

The Mathlib searches actually ran through msearch.py and are recorded in searches.jsonl. I read the returned signatures, the constantCommuteCompose source in CategoryTheory/Sites/ConstantSheaf.lean, the continuous abelian ellAdicSheaf in AlgebraicGeometry/Sites/ElladicCohomology.lean, and the live project's CompletedIntegral.lean. The searches find general limit extensionality, constant-coefficient change of target category, topological sheaf restrictions and algebraic etale maps; none proves the complete projection-normalized composition and slice-ringed statement. A second semantic phrasing and a targeted grep were run. No new nodes require separate searches.
