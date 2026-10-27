# Q133 stage-1 delivery

Item: lem-sfb-relative-tensor-faithfully-flat-comparison.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-tensor-faithfully-flat-comparison.json: statement, split into six proof steps; Mathlib verdict is no exact match.
- citations.json: 16 step/node entries, each quote checked as a verbatim substring of the live cited statement.
- report.md: this report.

No new nodes and no new Mathlib leaves. The local write_split.py is a sandbox working script, not a DAG delivery file. searches.jsonl is the search command's own log. The item was absent from the sandbox initially; its current live JSON was used whole, retaining its statement, source, provenance and earlier Mathlib searches, and changing only split-owned fields.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact node id/docstring tag, faithful-flat terminology, relative tensor terminology and Tor-amplitude terminology did not find a finished project declaration stating every clause. The ordinary mixed-total scalar-extension declaration exists, but it only proves a prerequisite, not this item. I read its formula and proof in Algebra/Homology/MixedTotalTensorScalarExtension.lean. I also read the mixed quasi-isomorphism proof and the existing mixed-derived interface (the latter is in lean/Sheaf/Algebra/Homology/MixedTensorPointwiseLeftDerived.lean). No Lean file was written or compiled.

## WANTED

None. The proof uses the obtained Stacks source in literature/stacks-project/.

## Findings and corrections

The statement is unchanged: it is the intended enhancement of Stacks Tag 0DJF, lemma-no-change-tor-amplitude. The source gives the equality of signed direct-sum total complexes, followed by a cohomology calculation. The delivered proof retains that equality as an actual B-linear chain isomorphism and therefore an isomorphism in D(B), and spells out naturality in the two requested variables. It uses an arbitrary R-K-flat resolution instead of requiring a free one; Tag 06Y4 and the mixed tensor lemmas justify this, with no change of route.

The missing proof is supplied. In particular, I did not use a K-flat A-complex as though its restriction to R were K-flat. That implication would require an extra flatness hypothesis. Instead the R-module N is resolved over R, exactly as in 0DJF. Tensoring with B is only assumed exact over A.

The inherited blueprint ancestry has from.node=null; tools/blueprint_refs.py ancestor reports None as well. I retained the maintainer-owned provenance rather than inventing an ancestor. Its existing place traces this algebraic tool through lem-sfb-etale-relative-tor-comparison to the direct-images proof (3). I read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, in addition to the DAG chapter/unit records. This split supplies the inherited algebraic prerequisite and does not change the chapter or unit route. The generic tools filed in other units are declared under split_report.tool_uses.

## Not duplicates

No new-node/existing-node pairs: no nodes are created. I searched the whole DAG for 0DJF, K-flat resolutions, exact-functor cohomology, mixed tensor and faithful-flat vanishing, and searched blueprint_refs for faithfully flat, K-flat and no-change-tor-amplitude. The two DAG records containing 0DJF are the item and its parent; the parent is the site-comparison problem, not the ordinary algebra result here. Existing module resolutions, mixed derived tensor, ordinary scalar-extension total comparison and faithful-flat tensor detection are reused directly.

## Mathlib searches

The six Q133 searches are recorded verbatim from searches.jsonl in the item: LeanFinder twice (unbounded relative tensor/Tor amplitude, and flat coefficient-extension phrasing), LeanSearch, Loogle for "FaithfullyFlat", "Tor", whole-Mathlib grep for faithful-flat/Tor combinations, and Algebra/Homology grep for derived tensor and Tor-amplitude names. All services answered. The first phrasing finds ordinary flatness/descent and exactness of module tensor; the second finds flat scalar extension preserving finite limits and composition of ordinary extension of scalars. The source of the latter candidate, Mathlib/Algebra/Category/ModuleCat/Descent.lean, and the relevant faithfully-flat Basic.lean statements were read. These do not state the unbounded mixed derived comparison or the relative Tor-interval equivalence. The original six search records by the creating group remain present as history; the six new entries are actual Q133 runs.

## Unfinished work

None for this stage-1 item. The reused nodes remain in their existing state; no prerequisite is restated or split in this delivery.

## Review by Q133

I read all of delivery-errors B through E, including the repeated merged copy, against this delivery. For the item I read the whole statement and proof of Tag 0DJF in more-algebra.tex, not only its title. For the K-flat input I read definition-K-flat, lemma-K-flat-resolution (06Y4), lemma-derived-tor-quasi-isomorphism-other-side (064L), and the derived change-of-rings construction and lemma-derived-base-change (06Y6). For exactness/cohomology I read homology.tex lemma-exact-functor (010N). For faithful-flat vanishing I read algebra.tex lemma-ff (00HP). There are no new-node sources to audit.

Step 1 uses the definition of faithful flatness only for exactness of tensor over A; it separately cites lem-weil-pbc-exact-functor-complex-cohomology for the assertion about cohomology and quasi-isomorphisms, avoiding C1's definition-only error. The statement of lem-pc-source-module-kflat-resolution supplies a resolution for every unbounded A-complex. Clause (2) of lem-pc-derived-tensor-second-factor-functor applies with its base ring A, coefficient algebra B and fixed coefficient complex B[0], and states both the derived computation and independence of choices. Its hypotheses include no flatness of B over R. Exactness then compares that resolution with any representative.

Step 2 uses the same resolution statement over R and the same mixed derived statement with the coefficient complex C. I checked that the latter explicitly allows an arbitrary complex of A-modules and outputs an object of D(A), not merely D(R). The statement of lem-pc-mixed-tensor-restriction-comparison says exactly that forgetting the mixed tensor gives the ordinary R-total tensor. The definition def-pc-mixed-total-tensor specifies the A-action and signed differential. Swapping F and C uses the displayed (-1)^{pq} map and keeps the C-action; this is the direct signed tensor identity, not a separate non-elementary lemma. The same hypotheses hold with coefficient algebra B and complex T(C).

Step 3 invokes new-lem-pc-mixed-total-tensor-scalar-extension exactly for the R,A,B tower and arbitrary complexes C,F. I opened its full statement: it gives a B-linear chain isomorphism and the diagonal-generator formula, with no flatness assumptions. The definition of mixed tensor identifies its written M tensor_A (A tensor_R E) with M tensor_R E. The two displayed inverse formulas in the step are its ordinary balancing identifications. Their signed differentials agree since the B factor has degree zero. The resulting map is localized in D(B); the proof does not replace this with a weaker per-degree assertion.

Step 4 checks the actual diagonal formula on variable maps, so it does not merely claim that naturality is clear. The two clauses of lem-pc-mixed-tensor-kflat-quasi-iso explicitly cover quasi-isomorphisms between R-K-flat models and quasi-isomorphisms of arbitrary coefficient complexes with fixed R-K-flat factor. I read those clauses and did not demand that C itself be R-K-flat. The derived-second-factor node supplies canonical comparisons and, in clause (3), naturality for maps of the fixed coefficient complex. The localization-universal-property node explicitly includes natural transformations, their uniqueness and lifting isomorphisms; it is not merely a fully-faithful Yoneda statement. These give the derived natural squares and their independence of representatives. The comparison is an isomorphism on every resolving model, and every input has such a model by step 2, so the descended components are isomorphisms. Naturality in degree-zero R-module maps is the restriction of this naturality.

Step 5 is the short composition of the chain isomorphism from step 3 with the already cited exact-cohomology isomorphism; its only cited node says the whole cohomology assertion and its naturality. Step 6 is the elementary quantification of the resulting vanishing equivalence. The only non-definitional detection input, lem-sc-faithfully-flat-tensor-zero, explicitly states that tensoring a test module with a faithfully flat module reflects the zero module. I checked its application with base A and module B; the cohomology is already an A-module. Tensor of zero is zero by the defining tensor relations, giving the forward implication as well.

I tested the statement and each construction with K=0, N=0, A=B, a=b, arbitrary shifts, and zero rings (faithful flatness then permits B=0 only if A=0). The zero case is vacuous for all Tor intervals. To check that no accidental R-flatness hypothesis entered, take R=Z, A=F_p and B=F_p[t]; A to B is faithfully flat while neither is Z-flat. The resolution F is taken over Z and the same chain formula still works, including negative Tor degrees. For unbounded complexes, all totals are direct-sum totals, as stated by the mixed tensor definition; no product total or spectral-sequence convergence is used. All six steps are below 2000 characters, and I checked that the non-elementary comparisons have cited nodes rather than being concealed in a long step. The proof is acyclic at the level of the proposed edges, contains no new clause-restatement nodes, and citations.json contains the exact used text from each statement.
