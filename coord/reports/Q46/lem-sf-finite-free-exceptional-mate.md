# Q46 stage-1 report: lem-sf-finite-free-exceptional-mate

## Files written

- dag/nodes/sec-six-functors/lem-sf-finite-free-exceptional-mate.json: statement, split; no exact Mathlib match. Preserved imported metadata and searches, corrected the missing coefficient-action hypothesis, and supplied six proof steps.
- dag/nodes/sec-six-functors/lem-sf-site-finite-free-scalar-coordinates.json: new statement, unsplit; no Mathlib match. Arbitrary-site derived finite-free scalar coordinates, normalized scalar adjunction and conservative restriction. This is the only new node; zero Mathlib leaves.
- citations.json: one verbatim statement quotation per step/node citation.
- searches.jsonl: launcher-generated records, retained unchanged.
- report.md: this report.

## Attachments

None. The exact blueprint tag and the finite-free exceptional-mate concepts were searched in lean/WeilConjectures/. No closed project declaration states every clause under these hypotheses. CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_biproductDesc in CategoryTheory/Adjunction/ProjectionMapMate.lean gives generic machinery with its own extra compatibility hypothesis; it does not supply this derived-sheaf statement or the requested normalized columns. Its existence was checked rather than treated as an attachment. No Lean was written or compiled.

## WANTED

None. The blueprint, Stacks sources and relevant existing node statements were available locally.

## Statement dispute and corrections

STATEMENT-DISPUTED: the original assertion assumes merely additive adjoints but concludes that a specific comparison has columns G_A of the basis inclusions. An additive functor need not preserve coefficient multiplication. This is a defect of the imported generality, rather than a change to the intended coefficient-linear six-functor route.

Here is an explicit counterexample, already on the singleton site. Set A=B=Q(i), with identity coefficient homomorphism, rank r=1, and chosen A-basis b_1=i. Identify scalar extension and restriction with identity functors. Let H be conjugation twist: its underlying groups and maps are unchanged, while a acts on H(V) by conjugate(a). It is exact and additive, H squared is identity, and H is adjoint to itself with identity unit and counit. Use F_A=F_B=G_A=G_B=H, d:UF_B=F_AU the identity, and c=-identity. Under the chosen basis the isomorphism e_P:P -> UTP is multiplication by i. On H(P), e_{H(P)} is underlying multiplication by -i, whereas H(e_P) is underlying multiplication by i. Consequently c e_{H(P)}=H(e_P), exactly the required restriction normalization. The defined mate b and the Hom-chain isomorphism theta are both -identity. Thus theta U(b)=identity, but in the required coordinates its column is

    H(e_M)^(-1) (theta U(b)) e_{H(M)} = i^(-1)(-i) = -identity,

whereas the rank-one finite-sum comparison is identity. All statements persist on complexes and their derived categories. This disproves the original column clause even though b happens to be invertible in this example.

The correction requires G_B(a id_N)=a id_{G_B N} for every a in B and every N; B-linearity suffices. It is precisely the scalar identity needed in step 5 and holds for the intended exceptional coefficient functors. No coefficient linearity of F_A, G_A, or the adjunction Hom bijections is silently used. The original c and its normalization assumption are retained. The corrected argument actually proves the conclusion without needing that additional normalization: the Hom-chain definition of theta and the counit definition of b cancel c on the scalar unit. In particular, no unjustified identification of the left-functor comparison d with the right-functor comparison theta is made. Removed the unused scheme-specific def-weil-pbc-derived-categories statement dependency; the statement already specifies ordinary module-sheaf derived categories on small sites.

## Unfinished work

The item is completely split at stage 1. Its new scalar-coordinate node intentionally remains statement-only for the next split; no proof or Lean implementation of that node is claimed. There are no missing mathematical cases in the assembly argument. Server validation and delivery results are recorded by the delivery tool.

## Search assessment

I searched the whole DAG and current blueprint for finite free, finite-free, finite basis, scalar extension, restriction of scalars, biproduct, change of rings, conservative, Yoneda and adjunction mate, including source tags 03CZ and 03DA. Exact blueprint ancestor is lem-coef-finite-free-extension, paragraph 1 of its proof, and the new node records its intervening item in via. There was no blueprint statement equal to the new arbitrary-site package; same_as is empty.

All Mathlib searches used msearch.py and their actual results were read. The item has natural-language LeanSearch and LeanFinder, name-pattern Loogle, and source grep searches, with a second phrasing. The new node separately has LeanSearch, two differently phrased LeanFinder searches, Loogle and grep. ModuleCat extension/restriction units and counits, tensor-product bases, sheaf free objects and categorical mapBiproduct/mates are relevant infrastructure, but none gives the arbitrary-site derived coordinate package or the corrected exceptional-mate statement in one specialization. No failed service is recorded as a mathematical negative, and no unrun query is recorded.

## Not duplicates

lem-sf-site-finite-free-scalar-coordinates vs def-sf-scalar-reduction-categories-restriction: the existing definition concerns scheme coefficient categories for a completed DVR and its quotient; the new theorem supplies exactness, derived adjunction, conservative restriction and basis coordinates on arbitrary small sites for arbitrary finite-free ring maps.
lem-sf-site-finite-free-scalar-coordinates vs def-coef-compact-support-reduction-maps: the existing definition fixes quotient-tower reduction maps and their units; it does not assert finite-free derived coordinates or conservative restriction.
lem-sf-site-finite-free-scalar-coordinates vs def-trf-singleton-site-operations: the existing node defines singleton-site operations and compatibility predicates, without proving the arbitrary-site finite-free package.
lem-sf-site-finite-free-scalar-coordinates vs def-trf-integral-tower-inverse-image-unit: the existing definition concerns inverse-image units in an integral quotient tower on schemes, not arbitrary-site finite-free scalar coordinates.
lem-sf-site-finite-free-scalar-coordinates vs def-trf-point-restriction-coordinates: the existing node defines coefficient section rings and point/automorphism coordinates; it does not prove the derived scalar-extension basis decomposition.
lem-sf-site-finite-free-scalar-coordinates vs lem-sfb-scalar-hom-chain-evaluation: the existing theorem gives strict Hom-complex scalar evaluation, without exact finite-free scalar extension, conservative derived restriction or the specified UT basis isomorphism.
lem-sf-site-finite-free-scalar-coordinates vs def-sfb-flat-hom-evaluation-roof-data: the existing node defines Hom roof data and predicates, not the finite-free derived scalar theorem.
lem-sf-site-finite-free-scalar-coordinates vs lem-sfb-slice-scalar-hom-chain-adjunction: the existing theorem gives a slice Hom-chain adjunction and tensor normalization, not finite-basis UT coordinates or reflection of derived isomorphisms.
lem-sf-site-finite-free-scalar-coordinates vs lem-sfb-scalar-hom-chain-coefficient-coherence: the existing theorem gives coefficient coherence of Hom-chain squares, not the new finite-free coordinate package.
lem-sf-site-finite-free-scalar-coordinates vs lem-sfb-hom-scalar-chain-identification: the existing theorem identifies product Hom complexes and evaluations, without the finite-basis derived scalar isomorphism or conservative U.
lem-sf-site-finite-free-scalar-coordinates vs lem-sfb-flat-scalar-tower-coherence: the existing theorem concerns reassociation and tower coherence under exactness assumptions; the new theorem proves exactness and specified derived coordinates from a finite basis.
lem-sf-site-finite-free-scalar-coordinates vs lem-weil-pbc-flat-restriction-exact-left-adjoint: the existing theorem supplies the ordinary exact left adjoint for flat sheaf coefficients; it does not give the derived finite-basis isomorphism, its columns, or conservative derived restriction.
lem-sf-site-finite-free-scalar-coordinates vs lem-sf-finite-free-derived-scalar-calculus: the existing theorem requires finite rings and Noetherian scheme etale/proetale sites. Those hypotheses are absent from the present item and cannot be imposed on its arbitrary small sites and rings. The new theorem is a strictly more general infrastructure statement; it does not assert the item's exceptional adjoint comparison.
lem-sf-site-finite-free-scalar-coordinates vs lem-pur-constant-specified-basis: the existing theorem identifies the constant coefficient sheaf itself by a chosen basis, rather than tensoring arbitrary module complexes, descending the scalar adjunction and detecting derived isomorphisms.
lem-sf-site-finite-free-scalar-coordinates vs lem-pur-constant-finite-free-power-iso: the existing theorem gives an underlying abelian-presheaf power isomorphism, without the specified A-linear derived columns and normalized adjunction required here.
lem-sf-site-finite-free-scalar-coordinates vs lem-pur-system-scalar-model: the existing theorem supplies a normalized derived scalar model, without the finite-basis coordinate formulas and conservativity asserted by the new node.

lem-sf-site-finite-free-scalar-coordinates vs lem-weil-pbc-etale-module-ring-iso-tensor: the existing theorem transports ordinary etale module functors across a ring-sheaf isomorphism; a general finite-free map need not be an isomorphism, and the existing statement does not give arbitrary-site derived basis coordinates or conservative restriction.
lem-sf-site-finite-free-scalar-coordinates vs lem-weil-pbc-localization-inverse-image-coherence: the existing theorem compares localization at a section with geometric inverse image, including exact derived transport; it does not concern a chosen finite basis of a coefficient algebra or the finite-sum UT comparison and its columns.
lem-sf-site-finite-free-scalar-coordinates vs lem-pur-system-cochain-tensor-reduction: the existing theorem is a tensor/evaluation coherence identity for ordinary system cochain reductions; it asserts neither finite-free scalar extension coordinates nor conservativity of derived restriction on arbitrary sites.

## Review by Q46

For the item I read the current blueprint lem-coef-finite-free-extension.proof.md, paragraph 1, in literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/, together with the chapter/unit route. This is the finite-free coefficient starting case for the counit-defined closed-exceptional comparison. I retain that route; neither the item nor the new lemma uses SGA. The imported blanket additivity claim fails as shown above; I repaired its exact missing scalar identity instead of concealing it in the proof.

For the new node I read literature/stacks-project/sites-modules.tex at lemma-adjointness-tensor-restrict (Tag 03CZ), including its tensor/Hom construction, and lemma-abelian (Tag 03DA), including kernels and cokernels of sheaf modules. These are the ordinary sheaf foundations, not a claim that Stacks directly states the entire derived package. The finite-basis specialization uses the coefficient functionals of the chosen basis to invert the tensor coordinate map after sheafification. Therefore scalar extension is a finite direct sum on underlying A-modules and is exact; restriction is exact and detects zero cohomology. The actual tensor unit and multiplication counit preserve quasi-isomorphisms, so they descend to ordinary unbounded derived localization; the coordinate isomorphism is also on complexes and hence derived objects. This justifies the scope of the new statement and identifies the non-elementary localization infrastructure left for its next split. No enough-points, scheme, Noetherian or boundedness hypothesis is needed. Its conclusion is not a clause of the exceptional-mate item: it contains neither F nor G nor c nor b.

Step 1 uses exactly the new node's normalized T adjoint U, coefficient inclusions, specified basis isomorphism and reflection of isomorphisms. I checked these conclusions in its statement on both small sites. This is the only non-elementary assembly step.

Step 2 uses lem-galois-yoneda-fully-faithful. I opened it and checked that its statement is the full bijection Hom(A,B) -> Nat(h_A,h_B), with evaluation inverse, not merely a definition or a claim of faithfulness. Thus it represents this natural Hom chain and its inverse. The five displayed arrows consist of four adjunction bijections and the isomorphism c. Naturality and the inverse identities follow by uniqueness. The generic Yoneda tool use is declared off-unit; it does not replace a geometric part of the route.

Step 3 uses def-weil-pbc-adjunction-mate. I read its explicit unit/counit formula and equivalent transpose characterization. It really gives the counit identity used, and naturality follows from the given adjunction bijections. A morphism b in the B-module derived category commutes with multiplication by B. The separate equality G_B(m_a)=m_a on G_B is the added hypothesis, not a consequence of additivity and not something supplied by a definition citation.

Step 4 uses the same transpose characterization and the scalar-unit normalization of the new node. Tracing U(b) eta through the displayed Hom chain gives b, h, T(epsilon), eta epsilon and finally G_A(eta). Each equality is either the definition of b, cancellation of c inverse with c, naturality, or the adjunction triangle identity. This verifies theta U(b) eta=G_A eta without assuming a relation between the distinct comparisons d and theta.

Step 5 uses i_a=U(m_a) eta from the new node, naturality of theta, and the multiplication identity from step 3. This proves each basis column separately. All equalities are derived morphism equalities; I did not assume restriction is faithful on derived Hom sets or choose unsupported complex representatives of a right adjoint. The resulting coordinate comparison is exactly the map in the item's conclusion.

Step 6 writes the inverse explicitly using G_A of the biproduct projections. The two composite identities are finite matrix identities and additivity, with their sums displayed. Only the new node's reflection of isomorphisms is used to return from U(b) to b. Basis independence is uniqueness of the specified transpose for fixed c and counit, so it needs no separate unproved comparison lemma.

I checked rank zero (B the zero algebra, zero derived objects and empty matrices), rank one with the basis 1, rank one with an arbitrary unit basis including the counterexample above, and arbitrary finite rank. The zero-object assertion follows because an additive functor sends the zero identity to zero. For ordinary modules each coordinate is x -> x tensor b_j; derived normalization gives exactly the same formulas used in the argument. Every cited statement was opened, each citation quote is copied verbatim from that statement, proof_deps is the union of uses, and no source-only theorem substitutes for a cited dependency. No step exceeds 2000 characters; no hidden exceptional-mate clause has been moved into the sole new infrastructure node. I corrected double-escaped mathematical notation left by the initial JSON write and removed a sentence promising later use of d, since the actual argument does not use it.
