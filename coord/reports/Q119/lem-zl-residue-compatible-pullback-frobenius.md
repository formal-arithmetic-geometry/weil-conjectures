## Worker report

Files written: `dag/nodes/sec-deligne-laumon-general/lem-zl-residue-compatible-pullback-frobenius.json` (the assigned statement, now split), `citations.json`, this report, and the search command's `searches.jsonl`. The item statement and statement dependencies are unchanged. Eleven proof steps replace the empty proof. No Lean was written and no compiler, Lake, build, or local preflight command was run.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. Existing nodes supply every substantive input; the remaining work is an explicit induction and pasting of their naturality/associativity equations.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, residue/Frobenius terminology, Weil pullback, and localFrobenius. `WeilSheaf/StalkUpperStarCharpoly.lean` proves a characteristic-polynomial assertion for ordinary Weil sheaves, and `UpperStarPointwise.lean` proves purity consequences. Neither states the derived three-factor intertwining, common-stage inverse-equation descent, and semilinear t-exactness required here. They cannot attach this item. The absence of a tag alone was not treated as evidence of absence.

## WANTED

None. The source documents used are present locally.

## Findings and changes

The item is a Q37 auxiliary assertion making precise the Restriction paragraph of `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-l-dl-general-excision/lem-zl-morphism-open-closed-reduction.proof.md`. I read that paragraph, the unit and chapter records, and the current versions of all cited statements. The source says that restriction preserves the stalk and its local Frobenius; the item's stronger explicit formulation requires writing the point transport, the return comparison, and the Weil map separately. The delivered proof does so. There is no statement dispute or correction, and the unit route is unchanged.

Two tempting shortcuts were rejected during self-check. The pullback t-exactness theorem for k-morphisms cannot be applied to semilinear geometric Frobenius; Step 1 instead uses the theorem for arbitrary scheme isomorphisms and the exact inverse-image equivalence. Also closedness in an open subscheme does not generally imply ambient closedness; Step 9 instead uses the finite residue-field criterion in both directions. I checked the types in the return-compositor calculation and rewrote its cancellation as a whiskered compositor `d_{z,g_W^r} P_f`, with its actual source and target.

The formal steps are not new nodes: the alpha cocycle is the cited associativity equation applied twice, the iterate assertion is a displayed induction, and the return square is three displayed instances of the same associativity equation with inverse cancellation. Making those specializations separate nodes would create elementary nodes rather than useful lemmas. The scalar/composition compatibility is a genuine theorem and is cited as the existing `lem-pod-pullback-identities-scalar-extension`, rather than inferred from unrelated existence isomorphisms.

## Searches and reuse

The four new searches were run using the required msearch.py command, whose exact queries and actual results are in searches.jsonl and appended to the item's mathlib_searches. LeanFinder's phrasing concerned local Frobenius for derived Weil pullback; LeanSearch's second phrasing concerned naturality on derived stalks. Loogle and grep found `TopCat.Presheaf.stalkPullbackIso` (Mathlib/Topology/Sheaves/Stalks.lean:335), whose source I read. It is for topological presheaves, with no completed coefficient category or Weil structure. LeanSearch also returned ordinary scheme-module and sheaf-module pullback compositors; I read the scheme-module declaration around line 241. These supply ingredients in other settings, not a one-line specialization to the entire item. All services answered; none was recorded as unavailable.

I searched the whole DAG by point-transport, residue/immersion, scalar/compositor, finite-stage, and isomorphism/pullback terms, and searched blueprint_refs.py for `Frobenius pullback`, `point transport`, `coefficient extension`, `pullback composition`, `Weil pullback`, `residue-compatible`, and `iterated Weil`. I read the returned statements relevant to this item, including the stronger scalar-composition realization node. No blueprint node states this full assertion. No new node is proposed, so no repeated-tag pair needs disambiguation.

## Not duplicates

No new nodes. In particular I reuse the existing integral compositor, its scalar identity, the arbitrary-isomorphism pullback theorem, the point-transport naturality theorem, the constructible t-exactness theorem, and the closed-immersion residue-field theorem.

## Review by Q119

I read delivery-errors B through E whole and checked the delivered node, its cited statements, and the sources together. The source check includes Deligne, Weil II (1.1.3), (1.1.7)-(1.1.11), printed pp. 150-152, read from the local PDF: coefficient stages, transport of structure, the degree change for a residue-field extension, and Weil pairs. I read Stacks Tag 0D6D (`sites-cohomology.tex`, lemma-derived-pullback-composition) for the K-flat-normalized compositor, Tag 099N (`proetale.tex`, lemma-pushforward-Noetherian-case), parts (2) and (5), for completed pullback, and Tag 01QO (`morphisms.tex`, lemma-closed-immersion) for affine quotients. I also read Bhatt-Scholze Definition 6.8.10, Proposition 6.8.11(3), Proposition 6.8.14(2), and Remark 6.8.15 for the integral/rational constructible categories behind the t-exactness input. None of these references is presented as a verbatim source for the entire derived coherence refinement; proof_origin is agent.

Step 1 uses the actual statement of `lem-weil-isomorphism-derived-pullback`, which permits every scheme isomorphism and identifies integral pullback with termwise inverse image. `lem-weil-proetale-isomorphism-inverse-image` gives exactness and the inverse equivalence. The standard-pair, raw-rationalization, and common-stage definitions give the isomorphism closures and triangle descriptions used to pass this property up the coefficient stages. No unproved assertion about arbitrary completed pullback t-exactness is substituted. Both g and its inverse satisfy the hypotheses, and ell is invertible because ell differs from the characteristic.

Step 2 uses the affine/base-change description in `def-weil-frobenius-detailed` for the commuting scheme maps, the natural specified isomorphisms in `lem-pod-integral-pullback-composition`, the rational/common-stage action of the derived-pullback definition, and the exact arrow equation in the Weil-pair definition. The two displayed equalities prove arrow equivariance rather than merely asserting functoriality. Step 3 uses that same compositor's associativity equation and the local-Frobenius definition's precise recurrence for theta^[m]. I checked the base m=1 and the naturality square at theta:G_XK -> K in the induction. The order of factors agrees with the recurrence; no reversal or unproved cocycle is hidden.

Step 4 uses `lem-kun-closed-point-field` only to get finite positive residue degrees, the local-Frobenius definition for the return of a compatible geometric point, and the compositor plus point-fibre definition for the specified c. The actual residue map is assumed to be an isomorphism here; merely abstractly isomorphic finite fields would not identify the embeddings. In Step 5, clause (2) of `lem-weil-frobenius-point-transport-natural` really states naturality for every derived arrow, not only chain maps. Applying its displayed equation r times, then compositor naturality, proves the first-factor equation.

Step 6 cites only the integral-composition theorem because its content is precisely a substitution into its associativity identity, with every inverse cancellation written. I checked the domains H P_z P_f K and P_x G_X^r K at both ends of the equation. The three triples of scheme maps are composable. The semilinear return is g_T^r t = t g_s^r; I never replace it by g_T^r t = t. Step 7 uses naturality of the same compositor at theta^[r], the iterate identity proved in Step 3, and the exact three-factor formula in the local-Frobenius definition. Its displayed chain proves derived equality before taking cohomology.

Step 8 applies a cohomology functor to an equality of derived arrows, which is elementary functoriality. `lem-a1-constructible-pullback-t-exact` explicitly supplies preservation of the heart and the point-fibre/cohomology identification used here, under hypotheses satisfied by f and the chosen geometric points. It is not used for g_T. Step 9 uses the precise actual-residue-homomorphism assertion of `lem-weil-pbc-closed-immersion-residue-field-iso`. The open-immersion definition gives its local-ring isomorphism directly, and the closed-point-field criterion applies to X_0 and W_0 because both are of finite type over k_0. Counting coordinates of a residue-field basis gives q^r without any geometric extra lemma.

Step 10 invokes clause (1) of `lem-pod-pullback-identities-scalar-extension`, which actually states compatibility of the specified compositors with scalar extension. The point-sections lemma specifies the sections/tensor comparison and its tower law; point-transport naturality clause (2) explicitly includes the corresponding scalar compatibility, and integral-operations-scalar-extension gives natural pullback/scalar isomorphisms. Thus every scalar square used is supplied by a statement, not borrowed from its proof. Step 11 uses only the displayed directed-Hom-colimit construction, including eventual equality, and the Weil-pair definition. Taking finitely many upper bounds makes all inverse and equivariance equations hold at once. I do not assume injectivity on transition Hom groups or a Frobenius-stable lattice.

Small cases checked: f=id makes alpha and c the canonical identity comparisons; r=1 reduces the calculation to one point transport; r>1 uses the explicit induction without a rational-point assumption. Zero complexes and zero sheaves give the same equalities. Empty schemes make all closed-point assertions vacuous while their equivalences remain defined. Nonreduced closed immersions still have the same residue fields, as the affine quotient calculation confirms. The empty finite diagram has the declared Q_ell stage. The rank-one Weil map given by multiplication by ell has no invariant integral lattice with invertible Weil map, illustrating why the proof only descends rational inverse equations. No node is new, no source is replaced by an excluded route, and no step exceeds 2000 characters.

I generated 37 entries in citations.json, one for every cited-node occurrence, and checked each quote against the current statement, not its proof. The existing external-unit statements are declared as generic tool uses in split_report, with their specific roles; the delivery does not set the maintainer's tool_uses field. I checked that those tools have no dependency path back to the item. The statement was preserved verbatim.

## Unfinished work

None in the mathematical split. The required server dry run and direct push are performed after this report is written; their result is reported by the final delivery command.
