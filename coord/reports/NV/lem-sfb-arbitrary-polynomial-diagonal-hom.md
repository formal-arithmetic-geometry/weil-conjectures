# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-arbitrary-polynomial-diagonal-hom.json: statement, now split in eight steps; not a Mathlib leaf.
- citations.json: one complete verbatim cited statement for every step/node pair (16 entries).
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. All intermediate facts already have nodes. No Lean was written or compiled; no repository or launcher file was changed.

## Attachments

None. Searched the project under lean/WeilConjectures for the exact blueprint tag, polynomial/diagonal derived Hom, graph coinduction, perfect-algebra duality, and coinduction. Existing sheaf coinduction declarations and geometric diagonal calculations do not state this module-derived isomorphism. No finished declaration supplies the item.

## Literature

No WANTED documents. The proof is an agent assembly, not claimed to be a verbatim Stacks theorem. Read more-algebra.tex Tag 0A65 (lemma-internal-hom), 07VI (lemma-dual-perfect-complex), 067J (lemma-flat-finite-presentation-perfect), 068X (lemma-perfect-over-polynomial-ring), and 0A6A (lemma-base-change-RHom); dga.tex Tags 09LN and 09LT, the differential graded bimodule adjunction and its derived form; dualizing.tex Tags 0A70 and 0A71 (coinduction/restriction with the precomposition action), and 0BZE (lemma-RHom-is-tensor-special). The existing graph-coinduction node supplies its ordered Koszul refinement. The current latest blueprint six-functors-basics/sk-thm-sf-ctf-stability direct-images proof (3) and unit _section.md were read, together with the chapter/unit records. The inherited long ancestry is an auxiliary relative-duality branch; this split does not change the unit's direct-image route.

## Corrections and remaining work

The statement is unchanged and is mathematically consistent: no STATEMENT-DISPUTED issue found. The initial statement dependency on def-pc-ring-pseudo-coherent-complex was unused and was removed: T is arbitrary. The initial empty proof is replaced by the assembly below. The old search records are preserved and actual NV searches appended from searches.jsonl. New searches used LeanFinder, LeanSearch, Loogle and grep; a second semantic formulation and a focused grep were also run. The hits concern underived dual base change, cotangent modules, scheme diagonals, ordinary polynomial algebras, and unrelated topology, not this derived reduction. Loogle returned no hits. All services answered successfully.

This is a one-level split. Existing unsplit prerequisites remain their own work; the report makes no claim that the whole transitive proof is finished.

## Not duplicates

No new nodes were created. In particular:

- lem-trf-polynomial-diagonal-rhom-reduction has the same displayed formula but assumes Noetherian rings and a pseudo-coherent T with finite base Tor amplitude. It cannot prove this item. Its generic prerequisites, whose statements have no such restrictions, can and are reused.
- lem-trf-polynomial-diagonal-dual-base-change assumes Noetherian rings, so it is not cited. Its needed arbitrary-ring identifications are obtained from the existing general coinduction exchange and explicit balanced tensor cancellations.
- lem-trf-flat-polynomial-quotient-perfect assumes Noetherian rings. The first conclusion of lem-sfb-arbitrary-polynomial-dual-properties already states the arbitrary-ring perfectness, so no second perfectness node was created.
- lem-trf-perfect-algebra-dual-evaluation, lem-trf-derived-bimodule-tensor-hom, and lem-trf-polynomial-graph-coinduction have precisely the unrestricted statements used here, so no replicas were created.

Whole-DAG keyword/tag searches and blueprint_refs.py searches for polynomial diagonal, diagonal derived, dual evaluation, bimodule, and polynomial graph found no blueprint theorem with this unrestricted statement. blueprint_refs.py ancestor reports None for the existing inherited chain; its existing from.node/via are retained, and its detailed from.place and same_as are filled/preserved. No new ancestry record was invented.

## Review by NV

I read the item against the mixed-ring argument, not just the same-ring Tag 0A65. That tag alone would not justify the B-action or the two different restrictions. The proof uses the existing mixed-ring theorem explicitly. I also opened the full statements of every cited node; citations.json quotes those actual statements rather than their proofs.

Step 1 is elementary notation: q followed by multiplication evaluates x_j at a_j, and qi=p_1, ei=1_A follow on coefficients. The distinction between the two copies is retained throughout.

Step 2 uses only the first conclusion of lem-sfb-arbitrary-polynomial-dual-properties: A[0] is perfect over the chosen polynomial P over arbitrary rings. It does not use that node's stronger semidualizing conclusion or a conclusion about T. The cited flat-tensor-exact statement applies to the R-flat A_1. The displayed balanced isomorphism proves S/P flatness without a hidden Noetherian hypothesis. Tensoring the resolution with S is exact, finite projectives remain direct summands of finite free modules, and the cited bounded-flat K-flat theorem and tensor computation give the required Tor independence. This does not assume A/P flat.

Step 3 applies the full D(B)-valued coinduction exchange, with P, A_2, S substituted for its base, quotient and extension. Step 2 checks both hypotheses: perfectness of A_2/P and Tor independence. M=P[0] is allowed. Its statement gives exactly E as B tensor over A_2 with D, with the action retained. There is no invocation of a Noetherian-only flat-base-change lemma.

Step 4 uses the K-flat-resolution statement, change-of-rings K-flat statement and tensor computation statement for a model G of D. The latter extension is genuinely K-flat over B, so applying the diagonal tensor does not assume the diagonal flat. Both balanced maps are written. The residual S action is multiplication by a_1 times the image of p, exactly the graph action e. This is a short cancellation using the cited general results, not a new lemma hidden in an identification.

Step 5 uses perfect-algebra dual evaluation. Its statement requires exactly the B/S perfectness proved in Step 2; it applies to arbitrary unbounded V and yields a B-linear comparison. The separate coefficient tensor cancellation uses a K-flat A_1-model of T extended to S. Its maps and inverses are displayed, B-linear, and commute with maps of models. Thus the induced coefficient is along p_1 as required.

Step 6 uses the full statement of derived-bimodule-tensor-hom with X=A, E=C_q(S), V as defined. Its compatibility with restriction K→S is explicitly stated, so restriction along i gives the displayed D(A_1)-isomorphism. This is not an inference of an enriched adjunction from a mere Hom-set bijection. No perfectness of X or flatness of multiplication is required.

Step 7 uses polynomial-graph-coinduction for the actual ordered x_j-a_j. Its statement explicitly supplies C_e(V)=T[-n], naturally for arbitrary T, with the original A action, and includes n=0 and the zero ring. The order fixes a choice of graph orientation; no unexplained canonical generator is asserted.

Step 8 uses algebraic-shriek-derived-hom-adjunction, whose statement is in D(S), with ring map e and X=D, Y=V. Restricting along i is legitimate because ei is the identity. The total-Hom definition supplies the shift reindexing RHom(D,T[-n])=RHom(D[n],T), including cochain signs. Composition preserves naturality. The comparison is an isomorphism of derived objects, not merely a family of cohomology isomorphisms.

For E's edge cases I checked A=0 (all objects vanish), n=0 (graph evaluation is identity), R=A with a redundant presentation P=A[x]→A, x↦0 (D=A[-1], C=A), and A=R[x] with its identity presentation (the graph resolution gives T[-1], matching C=A[1]). Finite-dimensional non-Gorenstein algebras over a field need no invertibility of D: the proof uses its perfectness over P and mixed adjunction, never its invertibility over A. The scalar graph cancellation remains valid for non-flat A as a B-module. Unbounded T is allowed at each cited comparison and the only finite complexes used are the polynomial quotient and graph resolutions.

Against delivery-errors B–E: there are no new statement-only nodes or disguised clauses of the item; all hard comparisons are cited with exact hypotheses and statements; there are no uncited tags used as lemmas, no use of another node's proof, no SGA source, and no replacement of the unit's route. Every non-elementary step is under 2000 characters. Existing tools from other units are declared in split_report.tool_uses, with their generic algebra purpose. Their dependency closure is checked by the required server dry run.
