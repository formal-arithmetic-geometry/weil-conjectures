## Worker report

Repair by Q03, 2026-10-22, of the work-spreading return for lem-trf-geometrically-reduced-base-change. The sandbox initially contained only dispatcher brief markers, with no node, report or search log. I copied the live node and retained its statement, citations/search records and all pre-existing attribution fields. No previous sandbox argument or report was overwritten. No Lean file was written and no build was run.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-geometrically-reduced-base-change.json: split parent, statement unchanged, three assembly steps.
- dag/nodes/sec-trace-formula/lem-trf-reduced-finite-type-field-product-embedding.json: new statement, unsplit; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-finite-field-product-tensor-detection.json: new statement, unsplit; no exact Mathlib match.
- citations.json: exact statements copied for each citation in the parent's steps.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, geometrically reduced, isReduced_tensorProduct, and finite products of fields. Algebra.isReduced_tensorProduct_of_forall_residueField in WeilConjectures/Mathlib/RingTheory/Nilpotent/GeometricallyReduced.lean:47 is a more general residue-field criterion, not the exact item statement. The existing Sheaf/RingTheory/GeometricallyReducedBaseChange.lean declaration is still sorried; it is not an attachment.

## WANTED

None. All mathematical sources used are local Stacks algebra.tex and the inherited blueprint route.

## What was wrong and repair of the return

The returned parent contained 3769 characters across five proof paragraphs. The requested repair is structural: two independently assignable statement-only nodes, with all arguments preserved, and a parent assembly below 3000 characters. The first new node takes the finite-type algebra embedding (old step 2); the second takes the finite-product tensor isomorphism, factor swaps, coordinatewise reducedness and injective descent (old steps 3 and 4). The parent retains old steps 1 and 5 and assembles the two new lemmas. Neither new statement is the entire parent: the embedding lemma mentions no A or tensor reducedness, while tensor detection assumes a supplied finite field-product embedding and only finitely many reduced field tensors. The first cannot replace the second or conversely.

The original statement is mathematically correct and has not been changed. No statement dispute. No unit or chapter route is replaced. The ancestor remains lem-trf-local-term-locality and the inherited separable-constants chain is kept, with the item prepended to the new nodes' via lists. Read the current main-20261015 locality node and the sk-i-curve-zero unit; this commutative-algebra input supports the inherited geometric preparation chain, not a new local-term route.

## Preserved arguments and ownership

The following paragraphs are copied in full from the returned/live parent, so no calculation disappears behind shortened assembly prose. They are future-worker guidance in this report, not proof steps in the new unsplit nodes.

Original step 1, assigned to parent step 1:

The $k$-module $A$ is flat by [lem-weil-pbc-module-over-field-flat]. Consequently [lem-weil-pbc-flat-tensor-exact], applied to $0\to U\xrightarrow{i}V\to V/i(U)$, shows that $i\otimes1_A:U\otimes_kA\to V\otimes_kA$ is injective for every injective $k$-linear map $i$. For a $k$-algebra inclusion this is also a ring homomorphism: on pure tensors its product formula is $(i(u)\otimes a)(i(v)\otimes b)=i(uv)\otimes ab$, and it sends the unit to the unit. We will use this for subalgebra inclusions and for the embedding into a product of fields.

Original step 2, assigned to lem-trf-reduced-finite-type-field-product-embedding:

Fix a finitely generated $k$-subalgebra $B\subseteq R$. It is reduced: if $b^n=0$ in $B$, its image in $R$ is nilpotent and hence zero, so $b=0$. By [lem-wf-affine-noetherian-components], $B$ is Noetherian. Apply [lem-weil-pbc-reduced-noetherian-total-ring-fractions] to obtain finitely many minimal primes $\mathfrak q_i$, fields $K_i=B_{\mathfrak q_i}$, and the canonical ring isomorphism $Q(B)\cong P:=\prod_{i=1}^tK_i$. The localization map $B\to Q(B)$ is injective: by [def-weil-pbc-module-localization], $b/1=0$ means $sb=0$ for a nonzerodivisor $s$, whence $b=0$. Thus the composite $j:B\hookrightarrow P$ is an injective $k$-algebra map, giving each $K_i$ its induced $k$-algebra structure. Since $K_i$ is a nonzero field, the unital map $k\to K_i$ has zero kernel and is a field extension. If $B=0$, then $B\otimes_kA=0$ directly from bilinearity and there is nothing to prove for this $B$; in the following steps take $B\ne0$.

Original step 3, assigned to lem-trf-finite-field-product-tensor-detection:

For the finite product $P=\prod_iK_i$ of step 2, define $\Phi:P\otimes_kA\to\prod_i(K_i\otimes_kA)$ by $\Phi((x_i)_i\otimes a)=(x_i\otimes a)_i$. The universal property in [def-weil-pbc-module-tensor-product] makes this a linear map, and the multiplication formula makes it a unital ring map. Let $\iota_i:K_i\to P$ insert a coordinate with zeros elsewhere, a $k$-linear map (it need not be unital). Define the additive inverse candidate by $\Psi((z_i)_i)=\sum_i(\iota_i\otimes1_A)(z_i)$. The identities $\pi_j\iota_i=0$ for $i\ne j$, $\pi_i\iota_i=1$, and $\sum_i\iota_i\pi_i=1_P$ give $\Phi\Psi=1$ and $\Psi\Phi=1$ on pure tensors, hence everywhere since pure tensors generate. Thus $\Phi$ is a ring isomorphism. The sum is finite; no assertion about commuting tensor products with an infinite product is used.

Original step 4, assigned to lem-trf-finite-field-product-tensor-detection:

For every $i$, the hypothesis applied to the field extension $K_i/k$ says $A\otimes_kK_i$ is reduced. The swap map $a\otimes x\mapsto x\otimes a$ is a ring isomorphism to $K_i\otimes_kA$, with inverse the same swap, by the tensor universal property [def-weil-pbc-module-tensor-product] and the stated multiplication rule. Hence each $K_i\otimes_kA$ is reduced. A nilpotent tuple in their product has nilpotent, hence zero, coordinates, so that product is reduced; step 3 then makes $P\otimes_kA$ reduced. By step 1, $j\otimes1_A:B\otimes_kA\to P\otimes_kA$ is injective. A nilpotent in $B\otimes_kA$ maps to a nilpotent in the reduced target, hence to zero, and injectivity makes it zero. Therefore $B\otimes_kA$ is reduced for every finitely generated $k$-subalgebra $B\subseteq R$.

Original step 5, assigned to parent step 3:

Let $z\in R\otimes_kA$ satisfy $z^n=0$ for some $n\ge1$. By the generation clause of [def-weil-pbc-module-tensor-product], write $z=\sum_{j=1}^m r_j\otimes a_j$ (scalar coefficients can be absorbed into the $r_j$). Let $B\subseteq R$ be the $k$-subalgebra generated by these finitely many $r_j$, and put $z_B=\sum_j r_j\otimes a_j\in B\otimes_kA$. The map $B\otimes_kA\to R\otimes_kA$ sends $z_B$ to $z$ and is injective by step 1. It sends $z_B^n$ to zero, so $z_B^n=0$. Step 4 gives $z_B=0$, hence $z=0$. This proves reducedness for arbitrary $R$, without a finite-generation assumption on either algebra. Empty sums and the zero algebras give the zero tensor and satisfy the same conclusion.

For the first new statement's zero case use the empty product, whose underlying ring is zero; this makes the zero-algebra handling explicit. For the second node, the injectivity argument retained in parent step 1 supplies the flat-tensor input; its later worker must cite flatness/tensor exactness when splitting that node. Coordinate insertions in the inverse of Phi are linear maps, not unital algebra maps. The identity sum is finite. Swap is verified on pure tensors with inverse the same swap. Nilpotents vanish coordinatewise, and injectivity then descends that vanishing.

## Mathlib and duplicate searches

All new searches ran through the mandated msearch.py command and are in searches.jsonl, with identical tool/query text copied into the new nodes. For each new node I tried two semantic phrasings, Loogle and Mathlib grep, and LeanSearch. One LeanSearch request was rate limited and is recorded unavailable. The embedding hits for exists_finite_inj_algHom_of_fg and exists_integral_inj_algHom_of_fg were read in Mathlib/RingTheory/NoetherNormalization.lean:275-296: their injections point from a polynomial ring into the algebra, so they do not state this node. Minimal-prime finiteness and pi localization injectivity are only constituent facts. For tensor detection I read Mathlib/RingTheory/TensorProduct/Pi.lean:48-59 (piRight), Nilpotent/GeometricallyReduced.lean:51-87 (algebraic extension restriction), Flat/Basic.lean:642-659 (finite-subalgebra criterion), and Localization/Pi.lean:85-113. piRight proves the isomorphism clause only; none states the injective Theta and reducedness descent for the supplied embedding in one specialization. Both complete new nodes therefore remain unsplit, without any proof or proof dependencies.

Whole DAG searches covered 034N, 00I3, finite product of fields, product of field extensions, reduced finite type, embedding and injective product statements. Whole-blueprint searches used blueprint_refs.py ancestor and search with 034N, reduced Noetherian, finite product, product of fields, embedding, tensor product and geometrically reduced. I read the closest total-fraction and finite-type-limit statements. No blueprint node states either new lemma. See the following pairs.

## Not duplicates

lem-trf-reduced-finite-type-field-product-embedding vs lem-trf-geometrically-reduced-base-change: the parent has arbitrary reduced R and all field extensions; the new node constructs a finite embedding for a finite-type B, without any A or tensor conclusion.

lem-trf-finite-field-product-tensor-detection vs lem-trf-geometrically-reduced-base-change: the parent has arbitrary reduced R and all field extensions; the new node assumes a finite field-product embedding, constructs Phi and proves injectivity of Theta, with reducedness tested only on its finitely many factors.

lem-trf-reduced-finite-type-field-product-embedding vs lem-weil-pbc-reduced-noetherian-total-ring-fractions: gives the decomposition of Q(B) as a ring for a reduced Noetherian ring; it does not assert the finite-type algebra embedding, its k-algebra structures, or the zero-algebra embedding convention. This is the explicit work-spreading extraction of old step 2 requested by the return; its later split can reuse these existing components rather than duplicate their proofs.

lem-trf-reduced-finite-type-field-product-embedding vs lem-sc-affine-totalquotient-minimal-product: decomposes a total quotient ring under a weak-associate hypothesis; it neither gives finite type over k nor supplies the injective k-algebra map from B. This is the explicit work-spreading extraction of old step 2 requested by the return; its later split can reuse these existing components rather than duplicate their proofs.

lem-trf-reduced-finite-type-field-product-embedding vs lem-weil-pbc-fraction-ring-pi-bijective-compatible: asserts bijectivity for already specified compatible maps out of FractionRing; the new statement constructs an embedding of B itself into extension fields. This is the explicit work-spreading extraction of old step 2 requested by the return; its later split can reuse these existing components rather than duplicate their proofs.

lem-trf-reduced-finite-type-field-product-embedding vs lem-weil-pbc-total-fraction-fiber-decomposition: gives compatible decompositions after localization over B, without constructing this finite-type k-algebra embedding or tensor detection over the ground field k. This is the explicit work-spreading extraction of old step 2 requested by the return; its later split can reuse these existing components rather than duplicate their proofs.

lem-trf-finite-field-product-tensor-detection vs lem-weil-pbc-tensor-finite-type-limit: that node detects failure on finitely generated subalgebras; the new node proves joint injectivity through finitely many supplied fields and reducedness over them.

## Review by Q03

I read Stacks algebra.tex, Tag 034N, lemma-geometrically-reduced-any-reduced-base-change (10129-10151), including its finite-type reduction, field-product embedding and final definition argument; Tag 00I3, lemma-limit-argument (10109-10127), including its finite tensor expression and the preceding injectivity observation; and the three embedding inputs, lemma-minimal-prime-reduced-ring (00EU, 4543), lemma-Noetherian-irreducible-components (00FR, 6135), and lemma-total-ring-fractions-no-embedded-points (02LX, 4612). The first new lemma makes the source's second sentence a separate task; no perfectness, domain or dimension-zero hypothesis is inserted. The second makes the source's last two sentences a separate task, spelling out the exact comparison map and injectivity that the old proof constructed. Its factorwise hypothesis is all that argument uses. I reviewed the full carried-over paragraphs above against those sources, not just their short replacements.

Parent step 1 cites lem-weil-pbc-module-over-field-flat, whose statement says every k-module is flat, and lem-weil-pbc-flat-tensor-exact, whose final clause explicitly preserves the initial zero of an exact sequence. I opened both statements and checked the hypotheses: k is a field and A is its module, and i is injective; the pure-tensor multiplication check is elementary. Parent step 2 cites the two new statements: B is reduced by its injection into R and finitely generated by its selection; the first statement supplies precisely the finite product and injective unital algebra map required by the second, and hgeom supplies A tensor K_i reduced with the correct order. The second statement explicitly concludes B tensor A reduced, not merely an isomorphism. Parent step 3 cites def-weil-pbc-module-tensor-product, whose generation and functoriality clauses I opened: choose the finitely many r_j, form the subalgebra they generate, lift z to z_B and use step 1 to lift its nilpotence. Step 2 then kills z_B. No new tensor-colimit theorem is being assumed.

Every uses entry has its own exact quote in citations.json, copied from the node statement, not its proof. Definitions used by the new statements are named (field, field extension and tensor), and finite generation, product conventions and reducedness are written inline. Both new nodes have empty proof and proof_deps and null proof_origin. I checked B=0 with empty product, I empty forcing B=0 by injectivity, A=0 with arbitrary B, R=k, and a reducible finite-type example B=k[x,y]/(xy), which embeds into k(x) times k(y). For the second node taking A=K_i an inseparable field extension over imperfect k need not give reduced tensors; this fails its explicit factor hypothesis, rather than falsifying the lemma. There is no use of infinite-product tensor commutation. No smallness, coefficient-category or SGA issue occurs in these commutative algebra statements.

The repair corrects the granularity only: two comparable argument blocks (old step 2, 936 characters; old steps 3+4, 1595 characters) are now assignable separately. The parent retains the original flatness and finite-support arguments; the full 3769-character original plan is preserved above. I checked B--E of delivery-errors against this content: standalone statements and honest searches, exact citation interfaces, no circular use of the parent, and all field/finite/reduced hypotheses accounted for. Nothing in a new node depends on its parent. No proof step in the new parent exceeds 2000 characters and the total stays below 3000.

## What remains

Only the two new nodes are intentionally left unsplit for other workers, as the return expressly requires. Their full carried-over arguments and source places are above. No Lean attachment is claimed and no mathematical part of the old argument has been discarded.

## Dry-run repair

The first preflight rejected the embedding statement because its two definition ids were in one bracket separated by a comma. I changed both new nodes to individual [def-weil-field] and [def-pc-field-extension] references and regenerated the corresponding verbatim citation quotes. Their mathematical statements and dependency ids are unchanged.
