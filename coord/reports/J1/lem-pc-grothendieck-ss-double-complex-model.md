Files written:

- \`dag/nodes/sec-picard-framework/lem-pc-grothendieck-ss-double-complex-model.json\`, statement node, repaired split.
- \`dag/nodes/sec-picard-framework/lem-sp-cartan-eilenberg-properties.json\`, statement-only unsplit node, no Mathlib match.

Attachments: none.

WANTED: none.

The returned point 1 is repaired by explicitly defining \(C^{p,q}:=I^{q,p}\), identifying the exchanged Cartan--Eilenberg convention, and naming the transposition of differentials, filtrations, spectral sequences, and the \((-1)^{pq}\) total-complex isomorphism. Point 2 is repaired by replacing the false column-resolution claim: the new node states that rows resolve \(K^q\), columns have injective cycles, boundaries, and cohomology, column cohomology commutes with any left exact additive \(G\), and the complexes of column cohomology resolve \(H^q(K)\). Its statement cites [thm-sp-if-e1] and [def-sp-double-complex-total] for the convention and double-complex notions. Point 3 is repaired by citing [def-sp-left-exact-additive] for both \(H^q(F(I^\\bullet))=R^qF(X)\) and \(H^p(G(H^q_{II}(C)))=R^pG(R^qF(X))\), while removing the unsupported use of [thm-sp-if-e1] from that step. Point 4 is repaired by spelling out the single nonzero \(r=0\) row, the induced \(d_1\), \(E_2=E_\\infty\), the convergence identification, and the derived-functor definition.

## Review by J1

I read \`literature/stacks-project/derived.tex\` at Definitions/Lemmas 015H, 015I, 015J, and 015N, and compared the construction clause of [thm-sp-grothendieck] with the exchanged-index convention. I also opened [thm-sp-if-e1], [def-sp-double-complex-total], [def-sp-left-exact-additive], [thm-sp-double-complex-spectral-sequences], [def-sp-composite-acyclicity], and [lem-sp-grothendieck-edge-maps]. Step 1 now cites the construction, the exact row convention, the two filtration definition, and the two-filtration spectral-sequence statement; it explicitly accounts for the transpose and sign isomorphism. Step 2 cites the displayed \(E_1/E_2\) formulas, and the new node's exact claims about injective cycles, boundaries, cohomology, and the injective resolution of \(H^q(K)\); the derived-functor equalities are taken from [def-sp-left-exact-additive]. Step 3 checks the composite acyclicity hypothesis for every \(F(I^s)\), then uses the second-filtration formula to show the only nonzero row is \(r=0\), and cites the convergence and derived-functor definitions for the abutment. Step 4 checks the finite image filtration bounds and uses the exact left-edge-map statement. I tested the indexing on the degree-zero and identity-functor cases and corrected the prior false resolution convention and all four cited-step gaps.

What could not be finished: none; preflight and delivery remain to be run.
