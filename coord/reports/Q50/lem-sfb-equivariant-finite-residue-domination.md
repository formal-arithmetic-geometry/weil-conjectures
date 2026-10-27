## Worker report

Repaired the returned re-split for Q50. The sandbox initially contained only dispatcher marker files, not the retained delivery described in the brief. I copied the live reviewed item as the baseline. Its 14-step proof has 10202 characters. The item statement and all maintainer-owned fields are unchanged; the delivery tool rebases owned fields on current main. There was no earlier sandbox report/search log to reuse. Existing item Mathlib searches and their actual results are retained in its JSON.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-finite-residue-domination.json: unchanged statement; short five-step assembly.
- dag/nodes/sec-six-functors-basics/lem-sfb-local-etale-residue-polynomial-lifts.json: statement, unsplit; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-galois-polynomial-envelope.json: statement, unsplit; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-normalization-finite-model.json: statement, unsplit; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-roots-residue-splitting.json: statement, unsplit; no exact Mathlib match.

Attachments: none. The source search by the exact blueprint tag and by equivariant/residue/splitting notions found no exact upstream declaration. The local Sheaf theorem `AlgebraicGeometry.exists_equivariant_finite_residue_domination` (line 239) ends in `sorry`; it is not an attachment.

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, Situation 5.3 and Lemma 5.6, for the item and all four extractions. The local PDF is absent; I read the publisher PDF at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf, printed pp.613--614. Lemma 5.6 asserts residue-field containment at every point above each prescribed point, with a finite generically etale Galois alteration, and supplies no argument. The detailed proof is agent-written, as already recorded by the parent. No SGA source is used.

## Repair of the return

The return has one substantive demand: spread all 10202 characters of the previous proof across at least three comparable statement-only work items, retaining the parent statement and reducing its proof to at most 3000 characters. Four nodes are added. They carry old steps 1--4, 5--8, 9--12 and 13--14, respectively; their old argument sizes are about 2530, 2730, 2820 and 2120 characters. The empty-list identity construction stays in the parent. No extracted node restates the item: one is local polynomial preparation without groups, one is field theory without schemes or residues, one takes the extension and field action as inputs and contains no prescribed residue assertion, and one takes the normalizing field and split lifted polynomials as inputs and has no group or projectivity assertion. Each new node has proof=[], proof_deps=[], proof_origin=null and status=unsplit. Complete previous arguments are preserved below, without shortening or blurring; future workers can use the source, intermediate statement and corresponding report section independently. No Lean file was written and no compiler, Lake or build was run.

## Searches

Before creating the nodes I searched the whole DAG by residue/polynomial/splitting, compatible pairs/Galois actions, semilinear normalization, and integral roots; I opened the plausible existing statements. I ran blueprint_refs search for residue, Galois, normalization, residue polynomial, Galois extension, integral roots and finite residue domination. The broad blueprint searches supply definitions and ingredients, not any of these four extracted statements. blueprint_refs ancestor returns None; the parent's inherited null ancestor and via chain are retained, prepending the item on new nodes. The key unit and chapter were read; these are auxiliaries of direct-image finiteness, not a replacement for a unit route.

For each new node, the five queries in search-plan.json were executed through the required msearch.py, with the actual output preserved in the node and searches.jsonl. These include two different LeanFinder phrasings, Loogle and Mathlib grep. All four LeanSearch calls were rate-limited and are recorded unavailable, never as no match. LeanFinder, Loogle and grep succeeded. I read all hits. Etale.iff_exists_algEquiv_prod, the universal factorization neighbourhood theorem, fixedField_top, restrictNormalHom, relative normalization and galRestrict are ingredients, not a one-line proof of any full extracted statement. The node records do not claim Mathlib leaves. The field/product and normalization candidates were checked against their local source, including Etale/Field.lean, Galois/Basic.lean, AlgebraicGeometry/Normalization.lean and IntegralClosure/IntegralRestrict.lean. No new node has an upstream exact finished declaration.

## Review by Q50

I read de Jong Situation 5.3 and Lemma 5.6 in the publisher PDF. The original statement's finite-type-over-field hypothesis supports finite normalization; projectivity is global over Spec k, an affine Noetherian base. Its all-point residue assertion, nonfaithful actions, possibly empty residue schemes and empty list remain unchanged. None of the four extracted statements silently asserts the entire source lemma.

For local preparation I read Stacks Algebra 00U3 (lemma-etale-over-field), 00UD (lemma-make-etale-map-prescribed-residue-field) and Morphisms 02GM (lemma-etale-flat-etale-fibres). The local closed-fibre-to-total-space passage uses the stronger pointwise fibre-neighbourhood node, not the all-fibres statement alone: the finite image of its bad closed complement misses the local closed point and is empty. This is a genuine argument, retained in old steps 3--4 below. No henselian hypothesis is used or needed. The new statement allows a general integral finite-type S, and explicitly retains the nonempty generic product and degree >=1.

For the field envelope I read Fields 09I3 (lemma-galois-over-fixed-field), 0BME (lemma-lift-maps) and 09HN (lemma-normal-goes-up). Faithfulness is used only after taking the image H_0. Common F-embeddings must be corrected to K-embeddings; the new statement explicitly requires K-linearity, while old step 6 retains the correction. The pair group retains every element of a nonfaithful H. No division by the group order occurs. Complete splitting is included explicitly, so the last lemma need not recover it from an unstated construction.

For the normalization model I read Morphisms 035H (definition-normalization-X-in-Y), 035I (lemma-characterize-normalization), 035L (lemma-normal-normalization), 0AVK (lemma-nagata-normalization-finite-general), and Limits 01ZM (lemma-descend-finite-presentation). Integral-closure charts and normality require that the source is Spec M, a field, not an arbitrary relative normalization. Projectivity follows over Spec k, not an arbitrary nonaffine base. Finite type gives Noetherian affine charts, so both models in the generic-isomorphism spreading step are finitely presented. The new statement keeps this dense-open etaleness conclusion and the exact inverse convention for the geometric action. The map from Spec M identifies the generic fibre and the field action, so applying M^N=K later is legitimate.

For residue splitting I reread Algebra 00U3 and the minimal-polynomial/evaluation CRT statements. It requires a full splitting of the monic lift, not one chosen root or one chosen prime. Each integral root lies in the local integral closure and reduces at every w; the resulting root of the irreducible q gives a unital field embedding L into kappa(w). Normality of L/F then splits all component minimal polynomials; separability supplies distinct roots. The new statement exposes the all-root reduction, the field embedding, every component tensor product, and the final degree/count formula. It does not require M/K Galois or S Noetherian; neither is used by this argument. This is not a duplicate of etale-neighbourhood residue realization, which only chooses one point in a different scheme.

In the new parent: step 1 is the identity construction, elementary. Step 2 cites the local preparation statement for every piece of the polynomial data and the finite separable generic decomposition. Step 3 cites the envelope for the common K-field, the complete factorizations, the pair group, surjectivity and kernel fixed field. Step 4 cites the normalization statement for precisely its finite, projective, surjective, normal, field-identification, scalar-action and dense-open-etale clauses; it also cites the envelope fixed-field equality, which is not asserted by the normalization statement. Step 5 cites the residue lemma for every-w splitting, the local lemma for L_i/q_i/f_i/D_i and the envelope for full factorization; all its hypotheses are already available. The citations.json quotes are verbatim excerpts of these statements. Each non-elementary fact in this assembly is a cited conclusion, not a reference to a proof. All original cited node statements were opened; they are retained below with their uses and source locations, but are no longer direct proof dependencies of the parent.

Edge cases checked: r=0 uses identities; E empty uses zero ring, L=F, q=f=T and n=0; s generic has R=K and the same argument; degree-one extensions give the identity field; trivial H and a nontrivial group acting trivially both work (the pair group still surjects); characteristic dividing |H| is allowed; on P^1_Q at a rational point with E=Spec Q(i), the lifted quadratic and its Galois normalization give residue Q(i) and two rational points after base change. Local closed-fibre etaleness does not imply arbitrary maps are etale: here finiteness and finite freeness supply the needed hypotheses. All-point reduction uses integral-closure localization, not a claim that any point of an arbitrary finite cover receives a chosen residue extension.

B1--B10: new files are self-contained TeX statements only; every specialized notion is defined inline or has its actual definition in stmt_deps; no new definition duplicates a library definition; sources include exact tags/labels; Mathlib candidates were not mislabeled leaves; blueprint provenance is filled. C1--C8: no hidden non-elementary assembly step, no use of another node's proof, no false citation, no added cycles; generic off-unit tools now belong to the future extracted proofs rather than the parent's assembly. D1--D5: four separate arguments of comparable size, no one-node transfer of the entire item. E1--E7: hypotheses and small cases checked as above; no statement dispute or source correction was needed. The repair changes only decomposition, not the parent's mathematical statement. The old step 3's irrelevant 04GG pointer is retained only in the verbatim history below, not used as a source for a new claim.

## Not duplicates

lem-sfb-local-etale-residue-polynomial-lifts vs lem-pc-polynomial-quotient-distinct-linear-crt: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Quotient by distinct linear factors is a product of the coefficient field).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-pc-crt-principal-ideal-product: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Infimum of principal polynomial ideals is the principal ideal of the product).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-pc-crt-linear-evaluation: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Evaluation identifies a linear polynomial quotient with the coefficient field).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-pc-separable-polynomial-alg-closed-quotient-product: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (A separable polynomial quotient over an algebraically closed field is a product of copies of the field).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-pc-separable-polynomial-distinct-roots-alg-closed: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (A separable polynomial splits into distinct linear factors over an algebraically closed field).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-pc-crt-ideal-quotient-product: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Chinese remainder quotient product for pairwise coprime ideals).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-pc-crt-pairwise-linear-ideals: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Distinct linear factors are pairwise coprime).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-a1-finite-reduced-perfect-algebra-etale: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (A finite reduced algebra over a perfect field is etale).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-per-finite-algebra-etale-near-field-or-dvr: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Etale base neighbourhood from a field or DVR stalk).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-etale-ring-map-prescribed-residue-field: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (An etale ring map realizes a prescribed finite separable residue field extension at a prime).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-standard-etale-monic-derivative: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (The standard etale algebra of a monic polynomial localized at its derivative).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-etale-ring-map-quasi-finite: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (An etale ring map is quasi-finite at every prime (Stacks 00U5)).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-etale-residue-polynomial-lift: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Clearing denominators in a residue-field minimal polynomial).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-finite-separable-extension-etale: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (A finite separable field extension is etale).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-etale-fibre-discrete-separable-points: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (The fibres of an etale morphism are disjoint unions of spectra of finite separable field extensions).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-etale-neighbourhood-prescribed-residue-field: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Etale neighbourhoods realize finite separable residue field extensions).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-unramified-algebra-over-field-product: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (An unramified algebra over a field is a finite product of finite separable extensions).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-henselian-finite-etale-equivalence: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Finite etale algebras over a henselian local ring and over its residue field).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-etale-algebra-residue-field-separable: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Residue field extensions of an etale algebra are finite separable).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-weil-pbc-etale-algebra-over-field-product: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (An etale algebra over a field is a finite product of finite separable extensions).

lem-sfb-local-etale-residue-polynomial-lifts vs lem-sc-etale-units-stalk-evaluation-overfield-bijective: The new node constructs a finite free etale algebra over the local domain with a specified Galois closed fibre AND nonempty separable generic decomposition; the existing statement only supplies its narrower ingredient (Bijectivity of units-stalk evaluation in an algebraically closed overfield).

lem-sfb-equivariant-galois-polynomial-envelope vs lem-wf-finite-field-action-fixed-degree: The new node simultaneously constructs a common splitting field, K-linear embeddings, and the compatible-pair finite group for a possibly nonfaithful H; the existing statement supplies a field-action or automorphism-extension ingredient (Degree and Galois property over the fixed field of a finite faithful field action).

lem-sfb-equivariant-galois-polynomial-envelope vs lem-sfb-invariant-separating-parameters: The new node simultaneously constructs a common splitting field, K-linear embeddings, and the compatible-pair finite group for a possibly nonfaithful H; the existing statement supplies a field-action or automorphism-extension ingredient (Invariant separating parameters for a semilinear finite action).

lem-sfb-equivariant-galois-polynomial-envelope vs lem-sfb-normal-intermediate-isomorphism-lifts: The new node simultaneously constructs a common splitting field, K-linear embeddings, and the compatible-pair finite group for a possibly nonfaithful H; the existing statement supplies a field-action or automorphism-extension ingredient (An isomorphism of intermediate fields lifts through a normal extension).

lem-sfb-equivariant-galois-polynomial-envelope vs lem-dl-a1-normal-finite-aut-separable-subfield: The new node simultaneously constructs a common splitting field, K-linear embeddings, and the compatible-pair finite group for a possibly nonfaithful H; the existing statement supplies a field-action or automorphism-extension ingredient (Finite separable subfield of a normal extension with finite automorphism group).

lem-sfb-equivariant-galois-polynomial-envelope vs lem-weil-pbc-distinct-linear-factors-separable: The new node simultaneously constructs a common splitting field, K-linear embeddings, and the compatible-pair finite group for a possibly nonfaithful H; the existing statement supplies a field-action or automorphism-extension ingredient (A polynomial splitting into distinct linear factors is separable, and so are its divisors (Stacks 09H3)).

lem-sfb-equivariant-galois-polynomial-envelope vs lem-weil-pbc-normal-extension-conjugate-by-automorphism: The new node simultaneously constructs a common splitting field, K-linear embeddings, and the compatible-pair finite group for a possibly nonfaithful H; the existing statement supplies a field-action or automorphism-extension ingredient (In a normal extension, the roots of a minimal polynomial are conjugate under automorphisms (Stacks 0BME (2))).

lem-sfb-equivariant-galois-polynomial-envelope vs lem-weil-pbc-normal-subextension-automorphism-extends: The new node simultaneously constructs a common splitting field, K-linear embeddings, and the compatible-pair finite group for a possibly nonfaithful H; the existing statement supplies a field-action or automorphism-extension ingredient (Automorphisms of a normal subextension extend to the normal extension).

lem-sfb-semilinear-normalization-finite-model vs lem-per-generic-finite-normal-trivialization: The new node starts with a prescribed separable M and a prescribed semilinear J-action and realizes both on its finite global normalization with dense-open etaleness; the existing statement concerns a different construction (Generic trivialization of a finite-coefficient sheaf by a finite normal cover).

lem-sfb-integral-roots-residue-splitting vs lem-pc-polynomial-quotient-distinct-linear-crt: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (Quotient by distinct linear factors is a product of the coefficient field).

lem-sfb-integral-roots-residue-splitting vs lem-pc-crt-principal-ideal-product: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (Infimum of principal polynomial ideals is the principal ideal of the product).

lem-sfb-integral-roots-residue-splitting vs lem-pc-crt-linear-evaluation: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (Evaluation identifies a linear polynomial quotient with the coefficient field).

lem-sfb-integral-roots-residue-splitting vs lem-pc-separable-polynomial-alg-closed-quotient-product: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (A separable polynomial quotient over an algebraically closed field is a product of copies of the field).

lem-sfb-integral-roots-residue-splitting vs lem-pc-separable-polynomial-distinct-roots-alg-closed: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (A separable polynomial splits into distinct linear factors over an algebraically closed field).

lem-sfb-integral-roots-residue-splitting vs lem-pc-crt-ideal-quotient-product: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (Chinese remainder quotient product for pairwise coprime ideals).

lem-sfb-integral-roots-residue-splitting vs lem-pc-crt-pairwise-linear-ideals: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (Distinct linear factors are pairwise coprime).

lem-sfb-integral-roots-residue-splitting vs lem-a1-finite-reduced-perfect-algebra-etale: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (A finite reduced algebra over a perfect field is etale).

lem-sfb-integral-roots-residue-splitting vs lem-per-finite-algebra-etale-near-field-or-dvr: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (Etale base neighbourhood from a field or DVR stalk).

lem-sfb-integral-roots-residue-splitting vs lem-weil-pbc-etale-ring-map-quasi-finite: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (An etale ring map is quasi-finite at every prime (Stacks 00U5)).

lem-sfb-integral-roots-residue-splitting vs lem-weil-pbc-finite-separable-extension-etale: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (A finite separable field extension is etale).

lem-sfb-integral-roots-residue-splitting vs lem-weil-pbc-etale-fibre-discrete-separable-points: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (The fibres of an etale morphism are disjoint unions of spectra of finite separable field extensions).

lem-sfb-integral-roots-residue-splitting vs lem-weil-pbc-unramified-algebra-over-field-product: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (An unramified algebra over a field is a finite product of finite separable extensions).

lem-sfb-integral-roots-residue-splitting vs lem-weil-pbc-etale-algebra-residue-field-separable: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (Residue field extensions of an etale algebra are finite separable).

lem-sfb-integral-roots-residue-splitting vs lem-weil-pbc-etale-algebra-over-field-product: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (An etale algebra over a field is a finite product of finite separable extensions).

lem-sfb-integral-roots-residue-splitting vs lem-sc-etale-units-stalk-evaluation-overfield-bijective: The new node reduces all roots at every point of a prescribed normalization and then splits the entire residue algebra; the existing statement is a field/polynomial/etale ingredient without this all-point normalization conclusion (Bijectivity of units-stalk evaluation in an algebraically closed overfield).

lem-sfb-semilinear-normalization-finite-model vs lem-sfb-semilinear-galois-alteration-domination: the existing lemma constructs an alteration dominating an arbitrary T, not necessarily finite, with only an existential field extension; the extraction realizes a prescribed M and its prescribed field action on the finite normalization itself. Its statement does not give this special model or its dense-open etaleness.

lem-sfb-semilinear-normalization-finite-model vs lem-per-projective-galois-alteration-envelope: the existing envelope chooses a new L and dominates V with a map only finite over a dense open; it does not realize a prescribed semilinear action over nontrivial H on the finite normalization in a prescribed M.

lem-sfb-integral-roots-residue-splitting vs lem-dl-a1-integral-finite-residue-model: the existing lemma selects an intermediate algebra inside an already integral extension with separable residue subfields already given; the new lemma proves those embeddings from completely split lifted monic polynomials, at every normalization point.

lem-sfb-local-etale-residue-polynomial-lifts vs lem-sbc-etale-generic-residue-field-model: that node spreads a generic etale field extension to some etale morphism and selected generic point; this one realizes a Galois closed residue fibre by a finite free algebra over the whole local spectrum.

## Preserved proof arguments and work allocation

The following are copied verbatim from the live reviewed fourteen-step proof. They are guidance in this report, not proof steps of any new node and not claimed as completed proofs of those unsplit nodes. Every original argument remains available for the next workers. The old citation lists are candidate ingredients for those future splits; those workers must still audit and search them. Grouping follows the four comparable independent tasks rather than simply restating the parent's conclusion.

### lem-sfb-local-etale-residue-polynomial-lifts

Old step 1: If the point list is empty, take $W=S$, $J=H$, $\rho=\mathrm{id}$ and $a=\mathrm{id}$; all assertions follow directly, including $N=1$ and $k(W)^N=k(S)$. Hence assume the list is nonempty. Put $K=k(S)$ and $F_i=\kappa(s_i)$. A field is Noetherian, since its only ideals are zero and the whole field. Finite type over $k$ therefore makes $S$ Noetherian. If $s_i$ corresponds to $\mathfrak p_i$ on an affine chart $\operatorname{Spec}A_i$, then $R_i=\mathcal O_{S,s_i}=(A_i)_{\mathfrak p_i}$ is a Noetherian local domain with fraction field $K$ and residue field $F_i$.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-localization-noetherian, def-sc-function-field.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "01T6 (lemma-finite-type-noetherian); Algebra 00FN (lemma-Noetherian-permanence); function field 01RW"}.

Old step 2: Since $E_i\to\operatorname{Spec}F_i$ is finite it is affine, say $E_i=\operatorname{Spec}D_i$. The etale field-algebra decomposition writes $D_i=\prod_j F_{ij}$ with each $F_{ij}/F_i$ finite separable. Choose a finite Galois extension $L_i/F_i$ receiving all these fields. Choose a primitive element $\alpha_i$ of $L_i/F_i$, with monic separable minimal polynomial $q_i$. If $E_i$ is empty, the product is empty and we can choose $L_i=F_i$, $\alpha_i=0$, $q_i=T$. The minimal-polynomial quotient identifies $F_i[T]/(q_i)$ with $L_i$.

Uses: def-weil-finite-integral-morphism, lem-weil-pbc-etale-algebra-over-field-product, lem-weil-pbc-finite-galois-receiving-separable-extensions, lem-weil-pbc-finite-separable-extension-primitive-element, lem-weil-pbc-minimal-polynomial-quotient-field-iso.

Source: {"document": "literature/stacks-project/algebra.tex", "place": "00U3 (lemma-etale-over-field); Fields 030N (lemma-primitive-element), 09G1 (lemma-field-extension-generated-by-one-element), 0EXM (lemma-normal-closure-galois)"}.

Old step 3: Lift the finitely many nonleading coefficients of $q_i$ through the surjection $R_i\to F_i$, keeping leading coefficient $1$, to obtain $f_i\in R_i[T]$. Set $C_i=R_i[T]/(f_i)$ and $u_i:\operatorname{Spec}C_i\to\operatorname{Spec}R_i$. The monic quotient theorem gives a finite free $R_i$-basis $1,T,\ldots,T^{d_i-1}$, where $d_i=\deg q_i\ge1$, and identifies its closed fibre with $\operatorname{Spec}L_i$. Finite free modules are flat, and the affine flatness criterion makes $u_i$ flat. It is finite and, since $R_i$ is Noetherian, finitely presented. Its closed fibre is etale, because $L_i/F_i$ is finite separable.

Uses: lem-weil-pbc-monic-quotient-free, lem-sc-affine-standard-cover-finite-free-local-fp-flat, lem-weil-pbc-flat-ring-map-iff-flat-affine, pqf-lem-finite-fp-locnoeth, lem-weil-pbc-finite-separable-extension-etale.

Source: {"document": "literature/stacks-project/algebra.tex", "place": "monic division and 04GG (lemma-characterize-henselian); 00NX (lemma-finite-projective); Morphisms 01U5 (lemma-flat-characterize), 02GL (lemma-etale-over-field)"}.

Old step 4: Apply the flat, locally finitely presented fibre criterion at the closed point of $\operatorname{Spec}R_i$. Every point of the closed fibre has an open neighbourhood on which $u_i$ is etale. Let $V_i$ be the union of these neighbourhoods and $Z_i=\operatorname{Spec}C_i\setminus V_i$. The finite-map closedness theorem makes $u_i(Z_i)$ closed. It misses the closed point of the local spectrum, and hence is empty: every nonempty closed subset $V(I)$ of a local spectrum contains its maximal ideal. Thus $Z_i=\varnothing$, and etaleness local on the source shows that $u_i$ is etale everywhere. Base change to $K$ and the etale field-algebra decomposition now give $K[T]/(f_i)=C_i\otimes_{R_i}K\cong\prod_j K_{ij}$, with $K_{ij}/K$ finite separable. The product is nonempty, since its $K$-dimension is $d_i\ge1$.

Uses: lem-sbc-flat-fibre-etale-neighbourhoods, lem-weil-pbc-finite-closed-map-finite-fibres, lem-weil-pbc-etale-local-on-source, lem-weil-pbc-etale-ring-base-change, lem-weil-pbc-etale-algebra-over-field-product.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "02GM (lemma-etale-flat-etale-fibres), pointwise smooth-fibre criterion; 01WN (lemma-finite-proper); 02GJ (lemma-etale-characterize); Algebra 00U2, 00U3"}.

### lem-sfb-equivariant-galois-polynomial-envelope

Old step 5: Write $A_h=(h^{-1})^*$ for the induced left field action of $H$ on $K$, let $H_0$ be its image in $\operatorname{Aut}(K)$ and put $F=K^{H_0}$. Apply the finite faithful field-action theorem to $H_0$, giving $K/F$ finite Galois. Each $K_{ij}/F$ is finite separable: separability follows by the tower theorem, and products of finite spanning sets span the composite tower. Apply the finite-Galois-receiving theorem over $F$ to the finite family consisting of $K$ and all $K_{ij}$. Obtain a finite Galois field $M/F$ and identify $K$ with its chosen embedded copy; view each $K_{ij}$ as a $K$-subfield using its compatible embedding from the theorem applied to their $F$-extensions, after the adjustment in the next step.

Uses: lem-wf-finite-field-action-fixed-degree, lem-zl-separable-permanence, lem-weil-pbc-finite-galois-receiving-separable-extensions.

Source: {"document": "literature/stacks-project/fields.tex", "place": "09I3 (lemma-galois-over-fixed-field); 09HB (lemma-separable-permanence); 0EXM (lemma-normal-closure-galois)"}.

Old step 6: The embeddings into $M$ obtained in Step 5 initially need only be $F$-linear. For each $K_{ij}$ its restriction on $K$ is an $F$-embedding whose image is $K$: $K/F$ is normal, so every conjugate of an element of $K$ is still in $K$, and injectivity plus finite dimension makes the restricted map onto $K$. Lift the inverse of this restriction to an $F$-automorphism of $M$ by normal-intermediate-isomorphism lifting, and compose. This gives the promised $K$-embedding $K_{ij}\hookrightarrow M$. The extension $M/K$ is normal by normality over an intermediate field, finite because an $F$-spanning set also spans over $K$, and separable because every minimal polynomial over $K$ divides the separable minimal polynomial over $F$.

Uses: lem-sfb-normal-intermediate-isomorphism-lifts, lem-weil-pbc-normal-extension-normal-over-intermediate.

Source: {"document": "literature/stacks-project/fields.tex", "place": "0BME (lemma-lift-maps), (2); 09HN (lemma-normal-goes-up)"}.

Old step 7: Every $f_i$ splits in $M[T]$. Indeed, let $g\in K[T]$ be a monic irreducible factor of $f_i$. The quotient field $K[T]/(g)$ is a field quotient of $K[T]/(f_i)=\prod_jK_{ij}$. A map from a finite product to a field sends exactly one coordinate idempotent to $1$ and all others to $0$, so this quotient is isomorphic to some $K_{ij}$. Its class of $T$ is consequently a root of $g$ in $M$. Normality of $M/K$ says precisely that the minimal polynomial $g$ of this root splits in $M$. Factoring $f_i$ into irreducibles over the field $K$ then shows that $f_i=\prod_{\nu=1}^{d_i}(T-\beta_{i\nu})$ for elements $\beta_{i\nu}\in M$.

Uses: lem-weil-pbc-normal-extension-normal-over-intermediate.

Source: {"document": "literature/stacks-project/fields.tex", "place": "09HN (lemma-normal-goes-up); normality definition 09HN and elementary polynomial factorization over a field"}.

Old step 8: Define $J=\{(h,\sigma)\in H\times\operatorname{Aut}_F(M):\sigma|_K=A_h\}$ with componentwise multiplication, and $\rho(h,\sigma)=h$. The restriction condition is closed under multiplication and inverse. The finite Galois fixed-field theorem makes $\operatorname{Aut}_F(M)$ finite, so $J$ is finite. For each $h$, normal-intermediate-isomorphism lifting extends $A_h:K\to K$ to an $F$-automorphism of $M$, proving that $\rho$ is onto. Its kernel is exactly $\{(1,\sigma):\sigma\in\operatorname{Aut}_K(M)\}$. Since $M/K$ is finite Galois, the same fixed-field theorem gives $M^{\ker\rho}=K$. Keeping pairs retains the original, possibly nonfaithful, group $H$.

Uses: lem-weil-pbc-finite-galois-fixed-field, lem-sfb-normal-intermediate-isomorphism-lifts.

Source: {"document": "literature/stacks-project/fields.tex", "place": "09I1 (lemma-finite-Galois), 09DW (theorem-galois-theory), 0BME (lemma-lift-maps)"}.

### lem-sfb-semilinear-normalization-finite-model

Old step 9: Let $a:W\to S$ be the normalization of $S$ in $M$. Apply normalization in a finite extension of a residue field to the generic point of $S$. It gives that $W$ is normal integral and has function field $M$. Since $S$ is integral of finite type over the field $k$ and $M/K$ is finite, finiteness of normalization makes $a$ finite. On every nonempty affine chart $\operatorname{Spec}A\subset S$, write its inverse image as $\operatorname{Spec}B$, where $B$ is the integral closure of $A$ in $M$. Localizing at $A\setminus\{0\}$ gives the integral closure of $K$ in the algebraic extension $M$, which is $M$ itself; thus $W_K=\operatorname{Spec}M$.

Uses: def-fin-normalization-extension, lem-weil-pbc-normalization-in-residue-field-extension, lem-fin-normalization-extension-finite.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "035H (definition-normalization-X-in-Y), 035I (lemma-characterize-normalization), 035L (lemma-normal-normalization); 0359 (Nagata schemes)"}.

Old step 10: The finite-over-projective theorem applies to $W\to S\to\operatorname{Spec}k$: the base $\operatorname{Spec}k$ is affine Noetherian. Hence $W$ is projective in the required global closed-embedding convention. Projective implies proper, and proper includes finite type, so $W$ is finite type over $k$. The finite-map closedness theorem says that $a(W)$ is closed in $S$; it contains the generic point by Step 9 and therefore is all of integral $S$. Thus $a$ is surjective.

Uses: lem-fin-finite-over-projective, lem-kun-projective-implies-proper, def-weil-proper-morphism, lem-weil-pbc-finite-closed-map-finite-fibres.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "01WC (projective implies proper), 01WN (lemma-finite-proper); finite-over-projective over the affine Noetherian base Spec k"}.

Old step 11: For $j=(h,\sigma)\in J$ the generic geometric action is $\operatorname{Spec}(\sigma^{-1})$, covering the given geometric action of $h$ on $S$. It extends to $W$ on the integral-closure charts of Step 9. An isomorphism of base charts together with $\sigma^{-1}$ carries integral elements to integral elements, since it sends a monic equation to a monic equation. Applying the inverse shows that it is an isomorphism of their integral closures. These maps commute with localization and hence glue. Their composites are the prescribed composites on the subrings of $M$, proving the group law. This produces a $J$-action and $a\circ j=\rho(j)\circ a$. Its scalar action on $k$ is exactly the original action through $\rho$. The generic field action has image $\operatorname{Aut}_K(M)$ on $N$, so Step 8 proves $k(W)^N=k(S)$.

Uses: def-fin-normalization-extension.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "035H (definition-normalization-X-in-Y), integral-closure charts; explicit functoriality under isomorphisms"}.

Old step 12: To verify generically etale in the scheme-theoretic sense, choose a nonempty affine $U=\operatorname{Spec}A\subset S$. The finite separable extension $M/K$ spreads to a finite etale domain algebra $A'$ over $A[c^{-1}]$ for some nonzero $c\in A$, with fraction field $M$. The affine schemes $W\times_SU_c$ and $\operatorname{Spec}A'$ have the same generic fibre $\operatorname{Spec}M$. Both are finitely presented over $U_c$: the former by finite-over-locally-Noetherian finite presentation, the latter by etaleness and finiteness (or that same finite-presentation theorem). Generic-fibre isomorphism spreading therefore supplies an isomorphism over a smaller nonempty open $V\subset U_c$. The restriction of $a$ over $V$ is etale, since its isomorphic model is etale and etaleness is preserved by base change. Integral $S$ makes $V$ dense. Thus $a$ is etale over a dense open of $S$.

Uses: lem-weil-pbc-spread-finite-separable-extension, pqf-lem-finite-fp-locnoeth, lem-sbc-generic-fibre-iso-spread-base-open, lem-weil-pbc-etale-scheme-base-change.

Source: {"document": "literature/stacks-project/limits.tex", "place": "01ZM (lemma-descend-finite-presentation), (2) and (3); Morphisms 02GO (lemma-base-change-etale); spread-finite-separable-extension, finite-algebra calculation"}.

### lem-sfb-integral-roots-residue-splitting

Old step 13: Fix $i$ and any $w\in W$ above $s_i$. The integral closure of $R_i=\mathcal O_{S,s_i}$ in $M$ is obtained by localizing the integral-closure chart $B$ at $A\setminus\mathfrak p_i$, by the localization clause of normalization. Every $\beta_{i\nu}$ of Step 7 belongs to this ring, because it satisfies the monic equation $f_i(\beta_{i\nu})=0$. Map this ring to $\mathcal O_{W,w}$ and then to $\kappa(w)$. The factorization in Step 7 reduces to $q_i(T)=\prod_{\nu=1}^{d_i}(T-\overline\beta_{i\nu})$ in $\kappa(w)[T]$. In particular $q_i$ has a root in $\kappa(w)$. Evaluation at it and $F_i[T]/(q_i)\cong L_i$ yield an $F_i$-embedding $L_i\hookrightarrow\kappa(w)$: the unital map from the field $L_i$ is injective. This argument uses no selection of a distinguished $w$ and proves the assertion for every point above $s_i$.

Uses: def-fin-normalization-extension, def-weil-residue-field, lem-weil-pbc-minimal-polynomial-quotient-field-iso.

Source: {"document": "literature/stacks-project/algebra.tex", "place": "00UD (lemma-make-etale-map-prescribed-residue-field), lifted polynomial construction, with the explicit all-root reduction argument; Morphisms 035H"}.

Old step 14: For each component field $F_{ij}$ of $D_i$, choose a primitive element with monic separable minimal polynomial $p_{ij}$ over $F_i$. Its chosen embedding into the normal extension $L_i/F_i$ makes $p_{ij}$ split there; normality here applies directly to the minimal polynomial of that embedded element. Under the embedding of Step 13 it also splits in $\kappa(w)$. Its roots are distinct: the Bezout identity between $p_{ij}$ and $p_{ij}'$ remains an identity after coefficient extension, and rules out a repeated root. The minimal-polynomial quotient and evaluation Chinese remainder isomorphism give $F_{ij}\otimes_{F_i}\kappa(w)\cong\kappa(w)[T]/(p_{ij})\cong\prod_{\deg p_{ij}}\kappa(w)$. The first isomorphism sends $\theta\otimes1$ to the class of $T$ and $1\otimes t$ to $t$; its inverse sends $T$ to $\theta\otimes1$ and scalars to $1\otimes t$. The sole relation $p_{ij}(\theta)=0$ makes both maps well-defined, and they are inverse on their algebra generators. Tensoring the finite product $D_i=\prod_jF_{ij}$ distributes over it (send $(x_j)\otimes t$ to $(x_j\otimes t)$, with inverse the sum of the coordinate inclusions). Taking spectra gives the required finite disjoint union of rational points. The empty product gives the empty scheme. Together with Steps 8--12 this proves every clause.

Uses: lem-weil-pbc-finite-separable-extension-primitive-element, lem-weil-pbc-minimal-polynomial-quotient-field-iso, lem-pc-polynomial-quotient-distinct-linear-crt.

Source: {"document": "literature/stacks-project/algebra.tex", "place": "00U3 (lemma-etale-over-field), split separable polynomial case; Fields 030N, 09G1; explicit evaluation Chinese remainder argument"}.

## Original ingredient statements read

### def-fin-normalization-extension

Let $X$ be an
integral scheme
with function field $K$, and let $L/K$ be finite.
The normalization of $X$ in $L$ is the relative
spectrum of the integral closure of $\mathcal O_X$ in
$L$, with its canonical map to $X$. On an
affine open
$\operatorname{Spec}B$, this is
$\operatorname{Spec}\overline B^{,L}$.
Integral closure commutes with localization, so these
affine constructions glue. For $L=K$, this is exactly
[def-sc-normalization]; finiteness is not included in
the definition.

Source: {"document": "literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd-affine/def-fin-normalization-extension.md", "place": "node def-fin-normalization-extension, order 1014"}

### def-sc-function-field

Let $C$ be a curve over $k$ [def-sc-curves], let $C_1,\dots,C_n$ be the irreducible components of $C$ [def-weil-irreducible-components], and let $\eta_i\in C_i$ be the generic point of $C_i$ [def-sc-generic-point], which exists and is unique by [lem-sc-scheme-sober]. (There are finitely many components: $\operatorname{Spec}k$ is a Noetherian scheme, so $C$, of finite type over it, is Noetherian [lem-weil-pbc-finite-type-over-noetherian] and has finitely many irreducible components [lem-weil-pbc-noetherian-finite-components].) The
*function field* of $C$ is the product of the stalks of the
structure sheaf [def-weil-pbc-module-stalk] at these generic points,
$$k(C):=\mathcal O_{C,\eta_1}\times\cdots\times\mathcal O_{C,\eta_n}.$$
Equivalently it is the ring $R(C)$ of rational functions on $C$ [def-sc-rational-functions]: the germ map $R(C)\to k(C)$, $[(U,f)]\mapsto(f_{\eta_1},\dots,f_{\eta_n})$, is a ring isomorphism by [lem-sc-rational-functions-generic-stalks], and $k(C)$ is identified with $R(C)$ through it. For
an integral curve $C$ [def-pc-integral-scheme] there is one component, $C$ itself, with generic point $\eta$, and $k(C)=\mathcal O_{C,\eta}$ is a field [lem-sc-rational-functions-generic-stalks]; for any nonempty affine open $U\subseteq C$ the germ map $\mathcal O_C(U)\to k(C)$ makes $k(C)$ the field of fractions of
$\mathcal O_C(U)$ [lem-sc-integral-function-field-affine-fraction]. More generally, for any integral scheme $X$ with generic point $\eta$ one writes $k(X):=\mathcal O_{X,\eta}$, the function field of $X$ (Stacks Definition 01RW), with the same two properties by the same two nodes.

Source: {"document": "literature/blueprint/master/blueprint/sec-abelian-varieties/sk-def-av-pic/def-sc-function-field.md", "place": "node def-sc-function-field, order 441"}

### def-weil-finite-integral-morphism

Let $f:X\to Y$ be a morphism of schemes [def-pc-scheme]. The morphism $f$ is *integral* if it is affine [pqf-def-affine-morphism] and for every affine open $V=\operatorname{Spec}R\subseteq Y$ [def-weil-affine-spectrum], with (affine) inverse image $f^{-1}(V)=\operatorname{Spec}A$, the ring map $R\to A$ is integral (every element of $A$ satisfies a monic polynomial with coefficients in the image of $R$). It is *finite* if it is affine and for every such $V$ the ring map $R\to A$ is finite ($A$ is a finitely generated $R$-module). Since a quasi-coherent module $\widetilde M$ on $\operatorname{Spec}R$ is of finite type exactly when $M$ is a finite $R$-module (Stacks Lemma 01PB), $f$ is finite exactly when it is affine and $f_*\mathcal O_X$ is a finite (finite type, quasi-coherent) $\mathcal O_Y$-algebra; in the same sense, $f$ is integral when it is affine and $f_*\mathcal O_X$ is integral over $\mathcal O_Y$ on every affine open.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "Stacks Project, Morphisms, Definition with Tag 01WH; finite type modules on affines: Properties, Lemma with Tag 01PB"}

### def-weil-proper-morphism

Let $f:X\to S$ be a morphism of schemes. $f$ is *separated* if its diagonal $\Delta_f:X\to X\times_SX$ (the morphism to the fibre product [def-pc-base-change] with both components the identity) is a closed immersion, i.e. identifies $X$ with a closed subscheme of $X\times_SX$. $f$ is *universally closed* if for every morphism $S'\to S$ the base change $X\times_SS'\to S'$ is a closed map of the underlying topological spaces. $f$ is *proper* if it is separated, of finite type [def-weil-finite-type-morphism], and universally closed. A scheme over a field $K$ is *proper over $K$* if its structure morphism to $\operatorname{Spec}K$ is proper.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "Definition 29.41.1, tag 01W1 (definition-proper); separated: schemes.tex Definition 26.21.3, tag 01KK; universally closed: morphisms.tex definition-universally-closed, Section 29.41"}

### def-weil-residue-field

Let $X$ be a scheme and $x\in X$ a point, with local ring $\mathcal O_{X,x}$ (the stalk of the structure sheaf at $x$) and maximal ideal $\mathfrak m_x$. The *residue field* of $X$ at $x$ is the field

$$
 \kappa(x)=\mathcal O_{X,x}/\mathfrak m_x .
$$

A morphism of schemes $f:X\to Y$ induces, for every $x\in X$, a homomorphism of fields $\kappa(f(x))\to\kappa(x)$, the map induced on residue fields by the local homomorphism $\mathcal O_{Y,f(x)}\to\mathcal O_{X,x}$. For $Y=\operatorname{Spec}K$ with $K$ a field, $\kappa(f(x))=K$, so $\kappa(x)$ is a field extension of $K$ through $f$.

Source: {"document": "literature/milne-lectures-on-etale-cohomology_LEC.pdf", "place": "§27 (Integrality), p. 157: \"The residue field $\\kappa(x)=\\mathcal O_{X_0,x}/\\mathfrak m_x$\"; also Deligne, Weil I, (1.1), p. 273 (\"le corps résiduel $k(x)$ de $X$ en $x$\")"}

### lem-fin-finite-over-projective

Let $S$ be a Noetherian scheme (quasi-compact and locally Noetherian [pqf-def-locnoeth]), let $p:T\to S$ be projective in the global closed-embedding convention of [def-pc-projective-morphism], and let $h:Y\to T$ be finite [def-weil-finite-integral-morphism]. Then $p\circ h$ is locally projective in the following explicit sense: for every affine open $U\subseteq S$, with $T_U=p^{-1}(U)$ and $Y_U=(p\circ h)^{-1}(U)$, there exist $N\geq0$ and a closed immersion $Y_U\hookrightarrow\mathbf P^N_U$ over $U$. Thus $Y_U\to U$ is projective in the convention of [def-pc-projective-morphism]. In particular, if $S$ is affine, $Y\to S$ is projective. No global projective-space embedding is asserted when $S$ is arbitrary.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-fin-finite-over-projective.md", "place": "node lem-fin-finite-over-projective, order 1601"}

### lem-fin-normalization-extension-finite

For an integral scheme $X$ of finite type over a field
and a finite extension of its function field, the map of
[def-fin-normalization-extension] is
finite.

Source: {"document": "literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-cd-affine/lem-fin-normalization-extension-finite.md", "place": "node lem-fin-normalization-extension-finite, order 1015", "external": [{"document": "Stacks Project", "place": "Tag 0359"}]}

### lem-kun-projective-implies-proper

Every projective morphism is
proper (the structural
morphism $\mathbf P^N_Y\to Y$ is proper, and closed immersions are
proper; the class of proper morphisms is closed under composition).

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-projective-implies-proper.md", "place": "node lem-kun-projective-implies-proper, order 1708", "external": [{"document": "Stacks Project", "place": "Tag 01WC"}]}

### lem-pc-polynomial-quotient-distinct-linear-crt

Let $\Omega$ be a field [def-weil-field] and let $\rho_1,\ldots,\rho_n\in\Omega$ be pairwise distinct. Put $Q=\prod_{i=1}^n(T-\rho_i)\in\Omega[T]$. Evaluation induces an $\Omega$-algebra isomorphism $\Omega[T]/(Q)\cong\prod_{i=1}^n\Omega$.

Source: {"document": "literature/stacks-project/algebra.tex", "place": "Algebra, Lemma Tag 00U3 (lemma-etale-over-field), separable polynomial case; Chinese-remainder decomposition into linear factors"}

### lem-sbc-flat-fibre-etale-neighbourhoods

Let $f:X\to Y$ be a flat [def-weil-flat-morphism] morphism of schemes [def-weil-pbc-scheme-conventions], locally of finite presentation [def-sbc-locally-finite-presentation], and let $y\in Y$. The scheme-theoretic fibre [def-pc-scheme-fibre] $X_y\to\operatorname{Spec}\kappa(y)$ [def-weil-residue-field] is etale [def-weil-etale-morphism] if and only if for every $x\in X$ with $f(x)=y$ there is an open neighbourhood $V$ of $x$ such that $V\to Y$ is etale. No finite-morphism or Noetherian hypothesis is assumed; an empty fibre is allowed.

Source: {"document": "Stacks Project", "place": "Tag 02GM, lemma-etale-flat-etale-fibres; pointwise smooth fibre criterion and smooth relative-dimension-zero criterion (02GK)"}

### lem-sbc-generic-fibre-iso-spread-base-open

Let X,Y,S be affine schemes [def-weil-affine-spectrum], S integral [def-pc-integral-scheme], and f:X -> S and g:Y -> S locally finitely presented [def-sbc-locally-finite-presentation]. Let eta be a generic point and e:X_eta -> Y_eta an isomorphism of fibres [def-pc-scheme-fibre] over Spec kappa(eta). There exists an open U of S containing eta and an isomorphism f^{-1}(U) -> g^{-1}(U) commuting with their structure maps to S. The fibres may be empty.

Source: {"document": "Stacks Project", "place": "Tag 01ZM, lemma-descend-finite-presentation, parts (2) and (3); Tag 0GWT, local-ring spectrum limit."}

### lem-sc-affine-standard-cover-finite-free-local-fp-flat

Let $A$ be a commutative ring and $P$ an $A$-module that is free [def-weil-pbc-free-module] with a finite basis. Then $P$ is finitely presented [def-sc-finitely-presented-module] and flat as an $A$-module [def-weil-pbc-flat-ring-map].

Source: {"document": "literature/stacks-project/algebra.tex", "place": "Algebra, Lemma Tag 00NX (lemma-finite-projective), the implications (7) => (4) and (7) => (5), using Lemma Tag 00EO (lemma-cover) and Lemma Tag 00HT (lemma-flat-localization)"}

### lem-sfb-normal-intermediate-isomorphism-lifts

Let $k\subseteq L$ be an algebraic normal field extension [def-pc-field-extension], where normal means that the minimal polynomial over $k$ of each element of $L$ splits into linear factors in $L[T]$. Let $M_1,M_2$ be subfields of $L$ containing $k$, and let $\tau:M_1\xrightarrow{\sim}M_2$ be a field isomorphism fixing $k$. Then there is a field automorphism $\sigma:L\xrightarrow{\sim}L$ fixing $k$ such that $\sigma(m)=\tau(m)$ for every $m\in M_1$. Neither $M_1/k$ nor $M_2/k$ is assumed normal, and no separability or finite-degree assumption is imposed.

Source: {"document": "literature/stacks-project/fields.tex", "place": "Tag 0BME, lemma-lift-maps (2); statement and proof read in fields.tex."}

### lem-weil-pbc-etale-algebra-over-field-product

Let $k$ be a field and $C$ a commutative $k$-algebra such that $\operatorname{Spec}C\to\operatorname{Spec}k$ is etale [def-weil-etale-morphism], [def-weil-affine-spectrum] (equivalently, by [lem-weil-pbc-etale-ring-map-iff-etale-affine], $k\to C$ is an etale ring map in the sense of Stacks, Algebra, Definition 00U1). Then there are an integer $n\ge0$, fields $L_1,\dots,L_n$, each a field extension of $k$ [def-pc-field-extension] which is finite ($\dim_kL_j<\infty$) and separable algebraic [def-weil-pbc-separable-algebraic-extension], and an isomorphism of $k$-algebras $C\cong L_1\times\cdots\times L_n$ (for $n=0$ the zero ring).

Source: {"document": "literature/stacks-project/algebra.tex", "place": "Lemma Tag 00U3 (algebra-lemma-etale-over-field, line 39394), direction 'etale implies finite product of finite separable extensions'"}

### lem-weil-pbc-etale-local-on-source

Let $f:X\to Y$ be a morphism of schemes [def-pc-scheme] and let $(U_b)_{b\in J}$ be a family of open subschemes of $X$ with $X=\bigcup_{b\in J}U_b$, with inclusions $j_b:U_b\to X$. Then $f$ is etale [def-weil-etale-morphism] if and only if $f\circ j_b:U_b\to Y$ is etale for every $b\in J$ (Stacks Morphisms, Lemma 02GJ, (1)$\Leftrightarrow$(3) with the covering $Y=Y$ of the target).

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "Lemma Tag 02GJ (lemma-etale-characterize, line 8090), equivalence of (1) and (3) for the trivial covering of the target, and its 'Moreover' clause"}

### lem-weil-pbc-etale-ring-base-change

Let $R\to A$ and $R\to S$ be homomorphisms of commutative rings such that $\operatorname{Spec}A\to\operatorname{Spec}R$ is etale [def-weil-etale-morphism]. Then $\operatorname{Spec}(S\otimes_RA)\to\operatorname{Spec}S$, induced by $s\mapsto s\otimes1$, is etale.

Source: {"document": "literature/stacks-project/algebra.tex", "place": "Lemma Tag 00U2 (lemma-etale), item (2) (base change of an etale ring map is etale), used in the proof of Lemma Tag 08HQ (lemma-map-into-henselian)"}

### lem-weil-pbc-etale-scheme-base-change

Let $f:X\to S$ be an etale morphism of schemes [def-weil-etale-morphism] and $g:S'\to S$ any morphism of schemes [def-pc-scheme]. Then the base change $X\times_SS'\to S'$ (second projection of the fibre product [def-pc-fibre-product]) is etale. (Stacks Project, Morphisms, Lemma Tag 02GO.)

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "Morphisms, Lemma Tag 02GO (lemma-base-change-etale), line 8136"}

### lem-weil-pbc-finite-closed-map-finite-fibres

Let $f:X\to Y$ be a finite morphism of schemes [def-weil-finite-integral-morphism]. Then (1) $f$ is separated and universally closed [def-weil-proper-morphism] (indeed proper); in particular $f$ is a closed map: $f(Z)$ is closed in $Y$ for every closed subset $Z\subseteq X$; (2) for every $y\in Y$ the fibre $f^{-1}(\{y\})\subseteq X$ is a finite set.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "Stacks Morphisms, Lemma 01WN (lemma-finite-proper, line 11162: finite iff affine and proper; hence separated and universally closed), Lemma 02NU (lemma-finite-quasi-finite, line 11147: finite => quasi-finite) and Lemma 02NH (lemma-quasi-finite, line 3809: quasi-finite => finite fibres), as used in the proof of Etale Morphisms Lemma 04HJ (etale.tex line 1758: 'the fibre over s is a finite set', 'a finite morphism is separated', 'finite, hence proper')"}

### lem-weil-pbc-finite-galois-fixed-field

Let $M/k$ be a field extension [def-pc-field-extension] with $\dim_kM<\infty$ which is Galois: separable algebraic [def-weil-pbc-separable-algebraic-extension] and normal (for every $\beta\in M$ the minimal polynomial of $\beta$ over $k$ is a product of polynomials of degree one in $M[T]$). Let $G=\operatorname{Aut}(M/k)$ be the group of $k$-algebra automorphisms of $M$. Then $G$ is finite, of order $|G|=\dim_kM$, and its fixed field is $k$: an element $y\in M$ satisfies $\tau(y)=y$ for all $\tau\in G$ if and only if $y$ lies in (the image of) $k$.

Source: {"document": "literature/stacks-project/fields.tex", "place": "Fields, Lemma 09I1 (fields-lemma-finite-Galois, line 2664: $|\\mathrm{Aut}(E/F)|=[E:F]$ for finite Galois $E/F$) and Theorem 09DW (fields-theorem-galois-theory, line 2784: $K=L^G$ for a finite Galois extension $L/K$ with group $G$)"}

### lem-weil-pbc-finite-galois-receiving-separable-extensions

Let $k$ be a field, $n\ge0$, and let $L_1,\dots,L_n$ be field extensions of $k$ [def-pc-field-extension] which are finite ($\dim_kL_i<\infty$) and separable algebraic [def-weil-pbc-separable-algebraic-extension]. Then there are a field extension $L/k$ and homomorphisms of $k$-algebras $\tau_i:L_i\to L$ ($i=1,\dots,n$) such that $L/k$ is finite ($\dim_kL<\infty$), separable algebraic [def-weil-pbc-separable-algebraic-extension], and normal: for every $\beta\in L$ the minimal polynomial of $\beta$ over $k$ (as in [def-weil-pbc-separable-algebraic-extension]) is a product of polynomials of degree one in $L[T]$. (That is, $L/k$ is a finite Galois extension, Stacks, Fields, Definition 09I0, receiving every $L_i$.)

Source: {"document": "literature/stacks-project/fields.tex", "place": "Fields, Lemma 09DT (fields-lemma-normal-closure, line 2086: existence of the normal closure of a finite extension) and Lemma 0EXM (fields-lemma-normal-closure-galois, line 2704: the normal closure of a finite separable extension is Galois); a finite separable extension containing copies of all L_i is obtained from Fields, Lemma 09GU (fields-lemma-map-into-algebraic-closure, line 1023: embed each L_i into an algebraic closure) and Lemma 09HC (fields-lemma-separable-elements, line 1435: the compositum of the images is separable). Used in the proof of More on Morphisms, Lemma 02LM (more-morphisms.tex lines 12064-12066: 'Choose a finite Galois extension L/kappa(s) such that there exist kappa(s)-embeddings L_i -> L')"}

### lem-weil-pbc-finite-separable-extension-etale

Let $k'/k$ be a field extension [def-pc-field-extension] which is finite ($\dim_kk'<\infty$) and separable algebraic [def-weil-pbc-separable-algebraic-extension]. Then the morphism of affine schemes $\operatorname{Spec}k'\to\operatorname{Spec}k$ induced by the inclusion $k\to k'$ [def-weil-affine-spectrum] is etale [def-weil-etale-morphism].

Source: {"document": "literature/stacks-project/algebra.tex", "place": "Lemma Tag 00U3 (lemma-etale-over-field, line 39394), 'if' direction, second paragraph of the proof: $k'=k(\\alpha)\\cong k[x]/(f)$ with $\\gcd(f,f')=1$, so $\\mathrm d:k'\\cdot f\\to k'\\cdot\\mathrm dx$ is an isomorphism and $k\\to k'$ is etale (Definition 00U1). Scheme version: Morphisms, Lemma Tag 02GL (morphisms-lemma-etale-over-field, morphisms.tex line 8175)."}

### lem-weil-pbc-finite-separable-extension-primitive-element

Let $F\subseteq E$ be a finite separable extension of fields [def-pc-field-extension] [def-weil-pbc-separable-algebraic-extension]. Then there is $\alpha\in E$ such that $E=F(\alpha)$.

Source: {"document": "literature/stacks-project/fields.tex", "place": "Fields, Lemma Tag 030N (lemma-primitive-element), the moreover clause for separable finite extensions"}

### lem-weil-pbc-finite-type-over-noetherian

Call a scheme Noetherian if it is locally Noetherian [pqf-def-locnoeth] and quasi-compact (Stacks Properties, Definition 01OV). Let $f:X\to S$ be a morphism of schemes [def-pc-scheme] of finite type [def-weil-finite-type-morphism] with $S$ Noetherian. Then $X$ is Noetherian. In particular $\operatorname{Spec}\mathbf Z$ is Noetherian ($\mathbf Z$ being a Noetherian ring), so every scheme of finite type over $\operatorname{Spec}\mathbf Z$ is Noetherian.

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "Morphisms, Lemma 01T6 (lemma-finite-type-noetherian, line 2765), Noetherian case; definition of a Noetherian scheme: Properties, Definition 01OV (definition-noetherian, properties.tex line 421)"}

### lem-weil-pbc-flat-ring-map-iff-flat-affine

Let $\varphi:R\to A$ be a homomorphism of commutative rings and $\operatorname{Spec}\varphi:\operatorname{Spec}A\to\operatorname{Spec}R$ the induced morphism of affine schemes [def-weil-affine-spectrum]. Then $\operatorname{Spec}\varphi$ is flat [def-weil-flat-morphism] if and only if $\varphi$ is a flat ring map [def-weil-pbc-flat-ring-map].

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "Morphisms, Lemma Tag 01U5 (lemma-flat-characterize, line 4694): (1) => (2) with U = Spec A, V = Spec R, and (4) => (1) with the one-member coverings {Spec R}, {Spec A}"}

### lem-weil-pbc-localization-noetherian

Let $R$ be a Noetherian ring [def-weil-pbc-noetherian-ring] and $S\subseteq R$ a multiplicative subset ($1\in S$, $st\in S$ for $s,t\in S$). Let $\varphi:R\to R'$ be a homomorphism of commutative rings that is a localization of $R$ at $S$: (a) $\varphi(s)$ is a unit of $R'$ for every $s\in S$; (b) every element of $R'$ is $\varphi(r)\varphi(s)^{-1}$ for some $r\in R$, $s\in S$; (c) $\varphi(r)=0$ implies $sr=0$ for some $s\in S$ (for instance $R'=S^{-1}R$, the ring of fractions $r/s$, with $r\mapsto r/1$). Then $R'$ is a Noetherian ring.

Source: {"document": "literature/stacks-project/algebra.tex", "place": "Lemma Tag 00FN (lemma-Noetherian-permanence, line 5991), second sentence 'Any localization of a Noetherian ring is Noetherian', with its proof ('any ideal $J\\subset S^{-1}R$ is of the form $I\\cdot S^{-1}R$')"}

### lem-weil-pbc-minimal-polynomial-quotient-field-iso

Let $F\subseteq\Omega$ be fields [def-pc-field-extension] and $\theta\in\Omega$ algebraic over $F$ [def-weil-algebraic-element], with minimal polynomial $\mu\in F[T]$ [def-weil-pbc-separable-algebraic-extension] (the monic polynomial of least degree with $\mu(\theta)=0$; $F[T]$ the polynomial ring [def-weil-polynomial-ring]). Let $F(\theta)$ be the smallest subfield of $\Omega$ containing $F$ and $\theta$. Then $\deg\mu\ge1$, and the $F$-algebra homomorphism $F[T]\to\Omega$, $T\mapsto\theta$, induces an isomorphism of $F$-algebras $F[T]/(\mu)\xrightarrow{\sim}F(\theta)$ sending the class of $T$ to $\theta$. In particular $F(\theta)=\{g(\theta):g\in F[T]\}$.

Source: {"document": "literature/stacks-project/fields.tex", "place": "Fields, Lemma Tag 09G1 (lemma-field-extension-generated-by-one-element, line 357), proof, algebraic case ('If the kernel is (P) ... k[t]/(P) \\simeq F'), with the proof of Lemma Tag 09GN (lemma-degree-minimal-polynomial, line 870: 'the map k[x]/(P) \\to k(\\alpha), x \\mapsto \\alpha is an isomorphism'); tags verified in stacks-project/tags/tags"}

### lem-weil-pbc-monic-quotient-free

Let $R$ be a commutative ring and $f\in R[T]$ monic of degree $n$. Then $R[T]/(f)$ is a free $R$-module with basis the classes of $1,T,\dots,T^{n-1}$; in particular it is a finite $R$-algebra, and for every ideal $I\subset R$ one has $(R[T]/(f))/I(R[T]/(f))\cong(R/I)[T]/(\overline f)$.

Source: {"document": "literature/stacks-project/algebra.tex", "place": "Lemma Tag 04GG (lemma-characterize-henselian), proof of 10=>1 ('S = R[T]/(f) is a finite R-algebra', 'the finite free R-module S'); Euclidean division by a monic polynomial"}

### lem-weil-pbc-normal-extension-normal-over-intermediate

Let $F\subseteq K\subseteq E$ be fields [def-pc-field-extension] such that $E/F$ is algebraic and normal: every $\alpha\in E$ is algebraic over $F$ [def-weil-algebraic-element] and its minimal polynomial over $F$ [def-weil-pbc-separable-algebraic-extension] is a product of polynomials of degree one in $E[T]$. Then $E/K$ is algebraic and normal: every $\alpha\in E$ is algebraic over $K$ and its minimal polynomial over $K$ is a product of polynomials of degree one in $E[T]$.

Source: {"document": "literature/stacks-project/fields.tex", "place": "Fields, Lemma 09HN (fields-lemma-normal-goes-up, line 1838); tag verified in literature/stacks-project/tags/tags"}

### lem-weil-pbc-normalization-in-residue-field-extension

Let $X$ be a quasi-separated scheme [def-weil-pbc-scheme-conventions], $x\in X$ a point with residue field $\kappa(x)$ [def-weil-residue-field], $K/\kappa(x)$ a finite field extension, and $h:\operatorname{Spec}K\to\operatorname{Spec}\kappa(x)\to X$ the composite of the induced morphism with the canonical morphism [def-weil-affine-spectrum]. Then $h$ is quasi-compact and quasi-separated, and there are a scheme $Y$, an integral morphism $\nu:Y\to X$ [def-weil-finite-integral-morphism] and a morphism $g:\operatorname{Spec}K\to Y$ with $h=\nu\circ g$ such that: (a) $Y$ is an integral scheme [def-pc-integral-scheme] all of whose local rings $\mathcal O_{Y,y}$ are integrally closed domains (Y is normal); (b) $g$ maps the point of $\operatorname{Spec}K$ to the generic point $\eta_Y$ of $Y$ and induces an isomorphism $\kappa(\eta_Y)\xrightarrow{\sim}K$ of fields, i.e. $g$ is the inclusion of the generic point of $Y$ with $K$ as function field. (One may take for $\nu$ the normalization of $X$ in $\operatorname{Spec}K$, Stacks 035H: $Y=\underline{\operatorname{Spec}}_X(\mathcal O')$ with $\mathcal O'$ the integral closure of $\mathcal O_X$ in $h_*\mathcal O_{\operatorname{Spec}K}$; if $Z\subseteq X$ is the reduced closed subscheme on $\overline{\{x\}}$, it is also the normalization of $Z$ in $\operatorname{Spec}K$, by the last clause of Stacks 035I, which is the scheme used in the proof of Stacks 09Z6.)

Source: {"document": "literature/stacks-project/morphisms.tex", "place": "Definition 035H (definition-normalization-X-in-Y, line 13910), Lemma 035I (lemma-characterize-normalization: nu integral, f' dominant), Lemma 035L (lemma-normal-normalization, line 14170: Y normal, Y -> X' dominant and bijective on irreducible components, so X' is normal integral when Y = Spec K); as used in literature/stacks-project/etale-cohomology.tex, proof of Lemma 09Z6, line 12972-12978 ('Let Y -> Z be the normalization of Z in Spec(K) ... Y is a normal integral scheme ... it is clear that K is the function field of Y'; the function-field identification is called clear there)"}

### lem-weil-pbc-spread-finite-separable-extension

Let A be a Noetherian integral domain with fraction field K and let K'/K be a field extension [def-pc-field-extension] that is finite-dimensional as a K-vector space [def-weil-vector-space-dimension] and separable algebraic [def-weil-pbc-separable-algebraic-extension]. There is a nonzero c in A and a finite etale A[c^{-1}]-algebra A' [def-weil-etale-morphism] that is a domain with fraction field K'; consequently Spec(A') to Spec(A[c^{-1}]) is finite etale and surjective.

Source: {"document": "literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-weil-pbc-finite-pushforward-generic-constructible.md", "place": "proof, finite-algebra calculation, spreading out the separable extension"}

### lem-wf-finite-field-action-fixed-degree

Let $L$ be a field [def-pc-field-extension], let $G$ be a finite group, and let $\rho:G\to\operatorname{Aut}(L)$ be an injective group homomorphism, where $\operatorname{Aut}(L)$ consists of field automorphisms. Put $L^G=\{x\in L:\rho(g)(x)=x\text{ for every }g\in G\}$, with its induced field operations. Then $L/L^G$ is finite Galois: it is finite-dimensional, separable algebraic [def-weil-pbc-separable-algebraic-extension], and normal (every element's minimal polynomial over $L^G$ splits over $L$). Moreover $[L:L^G]=|G|$, where the degree denotes vector-space dimension.

Source: {"document": "literature/stacks-project/fields.tex", "place": "Tag 09I3 (lemma-galois-over-fixed-field), finite faithful action, Galois property and degree assertions; lines 2727-2781."}

### lem-zl-separable-permanence

Let $k\subseteq E\subseteq F$ be a tower of field extensions [def-pc-field-extension]. If $E/k$ and $F/E$ are separable algebraic extensions [def-weil-pbc-separable-algebraic-extension], then $F/k$ is a separable algebraic extension.

Source: {"document": "literature/stacks-project/fields.tex", "place": "Fields, Tag 09HB (fields-lemma-separable-permanence), lines 1414--1432"}

### pqf-lem-finite-fp-locnoeth

Let $S$ be a locally Noetherian scheme and
let $p:T\to S$ be a
finite morphism. Then $p$
is of finite presentation.

Source: {"document": "literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-zmt/pqf-lem-finite-fp-locnoeth.md", "place": "node pqf-lem-finite-fp-locnoeth, order 198"}

## Outstanding work

No required part of this repair remains unfinished. The four new nodes intentionally remain statement-only for parallel stage-1 workers. Delivery validation and push results are recorded below after execution.
