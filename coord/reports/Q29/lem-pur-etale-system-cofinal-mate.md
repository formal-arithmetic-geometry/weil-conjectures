## Files written

- dag/nodes/sec-smooth-purity/lem-pur-etale-system-cofinal-mate.json: the item, split in seven steps; statement unchanged.
- dag/nodes/sec-smooth-purity/lem-pur-system-block-repetition.json: statement-only generic lemma, unsplit; no Mathlib match. It concerns exact reindexing and derived ordinary direct image, not the exceptional right adjoint or coefficient projection.
- citations.json: one verbatim statement excerpt for each node used by each item step.

One new node; zero Mathlib leaves. No Lean written or compiled. No repository or launcher file changed.

## Attachments

None. Searched the complete WeilConjectures tree by the item's blueprint tag and by cofinal, subsequence and left-extension terminology. The relevant cofinal theorem in Sheaf/Paper/EtaleCoefficientSystemAdjoint.lean is not a project declaration under WeilConjectures and is not a finished proof. It is not used as an attachment.

## WANTED

None. The sources used are present locally.

## What needed repair

The imported item has an empty proof. Its assertion about actual derived-system maps needs more than checking the level projection squares. I factored its left extension through exact block repetition, so the projection theorem for a compatible ring-sequence map constructs h before evaluation. The new node exposes the nontrivial derived-image comparison needed by this factorization. It is a general diagram lemma, rather than a restatement of any item clause.

The Hom chain in the statement combines its last two adjunctions into one arrow. Step 4 expands that interpretation. Step 5 writes the precise composite-counit equation rather than invoking an unspecified 'preserves counits' assertion. No statement correction or mathematical dispute was needed.

## Not duplicates

lem-pur-system-block-repetition vs lem-pur-system-level-left-extension: the existing node constructs derived tensor left extension along a subsequence; the new node concerns exact repetition into a different, repeated ring sequence and its compatibility with a geometric derived direct image. It asserts no tensor left extension.

lem-pur-system-block-repetition vs lem-pur-system-derived-subsequence: restriction along a strictly increasing map selects entries; repetition along a nondecreasing surjection repeats entries. Their coefficient sequences, endpoint adjunctions and derived-image assertions differ.

lem-pur-system-block-repetition vs lem-pur-system-ordinary-selected-extension: that is ordinary left extension with scalar tensor and selected-transition formula, not repetition with identity rings within blocks or unbounded derived direct image.

lem-pur-system-block-repetition vs lem-coef-semilinear-derived-sections: the existing node gives evaluation/direct-image comparisons, not the whole-system repetition comparison or its endpoint adjunction. Evaluations are not used to detect equality of arbitrary derived morphisms here.

lem-pur-system-block-repetition vs lem-weil-pbc-kinjective-exact-square-comparison: the generic existing node assumes that its exact source functor preserves K-injectives. The new lemma supplies the concrete exact adjunction proving that hypothesis for repetition and states the resulting geometric normalization.

No existing node with the new source's Stacks tag is present because the source here is Zheng, not an unidentified Stacks section. Whole-DAG searches for repetition, first endpoint, block repetition, reindexing/direct image, and subsequence were read. Whole-blueprint searches for cofinal, mate, repetition, reindex, sequence direct image, cofinal restriction and restriction of systems found no equivalent blueprint statement. Existing unrelated repetition and Cech nodes do not state this lemma. Its nearest blueprint ancestor and via chain were obtained with blueprint_refs.py ancestor and checked against the item.

## Source and argument for the new node

I read Zheng, arXiv:1006.3810, Construction 4.1 (printed p.21), the paragraph immediately before Lemma 4.10 and Lemma 4.10 (printed p.23), and Lemma 5.22 (printed p.36). Construction 4.1 describes modules on the sequence topos and evaluation left adjoints. The paragraph before 4.10 constructs the levelwise geometric morphism; 4.10 is the evaluation/direct-image comparison. Lemma 5.22 uses adjunction to obtain the exceptional comparison. Zheng does not state arbitrary finite-block repetition in this form: both the new statement and its argument are agent extractions serving that route, and the item's proof_origin is agent, not document.

The new node's proof to be carried out when it is split is as follows. For block i with first endpoint a_i, a map E_t(P) to M determines P_m -> P_a_i -> M_i throughout the block. Conversely restriction to the first endpoints recovers the map, since internal block transitions in R_t(M) are identities. At a block boundary the compatibility equation is exactly the equation for the composite transition P_a_(i+1) -> P_a_i. This proves E_t left adjoint to R_t, including its actual transpose formula. Both functors are exact by componentwise exactness, and have the right coefficient rings at the endpoints. A chain map A -> R_t(I) transposes degreewise to E_t(A) -> I, and chain homotopies transpose by the same formula. If A is acyclic, E_t(A) is acyclic, so I K-injective implies R_t(I) K-injective. Resolve a B^X-system by a K-injective system I. Both sides of kappa are then the identical complex (u_* I_t(m))_m. The canonical right-derived comparison is therefore invertible and natural, normalized by this strict identity; the existing normalized exact-square comparison gives independence of the K-injective replacement. The derived inverse-image unit and direct-image counit compare through the strict ordinary adjunction identities on these same representatives, giving the stated unit/counit compatibility. Composite repetitions use the same repeated K-injective I, so their normalized comparisons compose identically. The open-extension equation is a strict termwise identity. No evaluated K-injective preservation is assumed.

The recorded semantic, Loogle and grep searches were run with msearch.py; I read all returned hits. Whiskering, sheafification and sheaf adjunction hits are ingredients only. In particular localCohomology.diagramComp concerns a different diagram and is not this statement for varying ring-sheaf systems. The search log is retained unchanged. There are two semantic phrasings for repetition and further searches for the full item. No search is invented or recorded as unavailable when it actually ran.

## Review by Q29

I read delivery-errors B through E in full, the standing worker brief, stage-1 rules, the three levels in SETUP, GOAL, and the chapter/unit records. I then reviewed the item against the source and each cited node's statement. The unit's adic-stage construction of compatible exceptional functors is retained; no SGA source is used and no chapter or unit file is changed.

Step 1 uses the new block-repetition comparison for p_f and its strict j_! identity. All its sites can be chosen small as required; the ring sequences and geometric inverse images match. I read the componentwise K-flat resolution, ordinary selected extension and derived selected extension statements. They give precisely the resolving representatives and actual universal derived functor used here. Repetition repeats the same K-flat complexes. I added the semilinear-system calculus citation explicitly: since tensor and acyclicity are componentwise, the repeated complex is K-flat as a system. Thus total scalar extension computes the asserted composite; this justification is included in the step. No comparison of unrelated evaluated objects is substituted for a system map.

Step 2 uses the coefficient-projection theorem for the compatible map D_m=C_r(t(m)) -> C_m. D and C are finite ell-primary sequences, and the theorem explicitly allows arbitrary unbounded inputs and nonflat coefficient maps. Its statement gives actual system maps, single-ring evaluation, identity maps, and coefficient composition. The block lemma supplies the other system map, and the left-extension statement supplies the specified transition. At t(m)=t(m+1) the selected transition is identity; at a boundary it is the actual N transition. I checked both cases rather than claiming naturality without specifying the relevant arrow.

Step 3 first checks that repetition preserves q by the scalar-unit transpose: repetition preserves tensor units and restrictions literally, and the new lemma preserves the geometric units and counits. Since scalar transposition is a bijection, this is equality of actual system transformations. It then uses those same composition equations. The equality t_(r o s)(m)=t_s(t_r(m)) follows directly from strict increase of r; it is not an extra cofinality theorem. Tensor associators and canonical composition of the left-extension adjunctions are clauses of the existing left-extension statement. The scalar projection and repetition composition identities identify the two h maps before evaluation.

Step 4 reads exactly the composite-adjunction definition and the counit-compatible right-adjoint uniqueness statement. There are two adjunctions on the same common left functor after transport by h. No claim that a general square's mate is invertible is used. The last Hom arrow expands first L_r^Y adjunction and then F_Cr adjunction. Its naturality includes all map action.

Step 5 obtains lambda and mu from the composite counit formulas, whose statement I opened, and applies the uniqueness theorem's counit equation. I type-checked the equation: h has source F_C L_X U_X G_C M; after L_Y F_Cr(rho) its target is L_Y F_Cr G_Cr U_Y M, where mu applies. This is the correct meaning of the restriction-counit normalization without assuming a bare U F isomorphism that has not been constructed. Resolution independence uses the actual factors specified in the block and projection statements, not equality detected by evaluations.

Step 6 expands the two Hom bijections, uses the h identity of step 3 and the composite-adjunction statement, and applies counit uniqueness. The order is rho_s U_r after U_s rho_r, since restriction along s follows restriction along r. The explicit t computation identifies the chosen left extensions. No extra mate-pasting lemma is hidden here.

Step 7 uses lem-pur-local-field-coefficient-stages with the identity field extension to supply the finite ell-primary rings, and not merely a definition of a finite coefficient ring. I corrected this citation during self-review. Equality of the ideal powers is immediate from equality of the two principal ideals. Canonical quotient maps send the same representative x to the same class, which checks transition compatibility and removes any dependence on a unit relating s and v^e. The derived scalar-adjunction node explicitly fixes x -> x tensor 1; the projection node fixes q by this unit transpose. Thus the transported maps agree, not only their objects. e>=1 is used for strict increase and unboundedness.

For the new node I tested t=id, a first block of length greater than one, an interior block boundary, constant and zero systems, the zero ring, and arbitrary nonflat coefficient transitions. The endpoint needed for E left adjoint to R is the FIRST endpoint, a_i, not the last; the explicit Hom formula checks its direction. No surjectivity or flatness of the ring transitions is assumed. For the item I checked r=id, r(n)=n+1, r(n)=2n, f=id, empty X, nonflat reduction Z/ell^2 -> Z/ell, and non-separated Y. Repetition has finite nonempty blocks for every allowed r, including the initial block 1 through r(1). The proof never needs Y separated. The only new node is neither elementary nor an item clause: its K-injective comparison is a reusable derived-image lemma. Elementary index and quotient computations stay in proof steps. Every step is shorter than 2000 characters. The new node has empty proof, empty proof_deps and null proof_origin; its planned argument is in this report only.

The generic strict-system lemma from the biduality unit and the identity-field coefficient-stage lemma from the purity-transport unit are declared as tool uses in split_report, with their purposes. All other tools are in the same unit or Mathlib leaves. citations.json was checked against exact current statements.

## Unfinished work

The new generic repetition lemma is intentionally statement-only, as required for a one-level stage-1 split. No part of the item's argument is left implicit beyond that cited lemma and existing nodes. Delivery checks and push follow this review.

## Delivery checks

The initial full dry run passed at bb0a87f0802. A subsequent C1 review added an explicit componentwise-tensor citation and the scalar-transpose justification for repeating q; the final dry run is rerun for those changes before push.
