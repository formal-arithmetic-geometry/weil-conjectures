# Worker report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-closed-limit-lfp-stabilization.json`: item split; no Mathlib stabilization match.
- `citations.json`: verbatim statements for every citation in all five steps.
- `report.md`: this report.

## New nodes

None. No new Mathlib leaves.

## Attachments

None. Project searches by the exact blueprint tag and by closed-immersion/limit/stabilization notions found no declaration of the whole item. The source library proves Tag 081B(1), not clause (3); it is not an attachment for this item. Master declarations were treated only as references.

## WANTED

None.

## Faults corrected

The item statement agrees with Stacks Tag 081B(3), applied to the identity of the limit, including quasi-compact stages, local finite type over an arbitrary base, closed transitions, and local finite presentation of the limit. It previously had no proof. I initially omitted the reason the kernel of the stage-to-limit quotient is finitely generated; I repaired that gap by citing the existing polynomial-kernel lemma and writing the image-of-generators argument. I also replaced an inappropriate use of the finite-data node for fixed representatives by the precise eventual equality clause of `lem-pc-filtered-colimit-commrings-elementwise`. There is no statement dispute and no change to the statement or unit route.

## Not duplicates

No new nodes. The whole DAG and blueprint searches found no blueprint node stating this stabilization. Existing Tag 081B(1) is a closed-immersion conclusion, whereas this item proves eventual isomorphisms, and so was not mistaken for the item. The finite-presentation kernel and affine-pair lemmas already exist and were reused.

## Review by NO

I read `literature/stacks-project/limits.tex`, Tag 081B, label `lemma-finite-type-eventually-closed`, the entire statement and proof, especially clause (3). I read every cited node statement. The source reduces the assertion to surjective ring transitions with finitely presented limit over the initial chart ring. The split follows that reduction, and expands why finite presentation over the base plus finite type of the initial chart gives a finitely generated quotient kernel.

Step 1 uses the finite-type definition to select affine chart generators and the closed-immersion affine description to obtain quotient rings and surjective transitions. Finite affine covers come from quasi-compactness; no quasi-separatedness or Noetherian hypothesis is used. These chart selections and quotient descriptions are direct uses of the definitions. Step 2 uses `lem-weil-pbc-limit-affine-transition` for restriction to a stage open and the spectrum of the colimit. `lemma-nagata-filtered-colimit-finite-data` supplies representatives; surjective transitions then show the initial map onto the colimit is surjective. `lem-weil-pbc-lfp-affine-opens-finite-presentation` says precisely that each limit affine chart mapping into an affine base chart is finitely presented. I read its source, Morphisms Tag 01TQ, label `lemma-locally-finite-presentation-characterize`, as well as its statement.

Step 3 uses `lem-weil-pbc-finite-presentation-surjection-kernel-fg`, whose statement applies to any polynomial surjection onto the finitely presented algebra, not just a chosen presentation. I read Algebra Tag 00R2, label `lemma-finite-presentation-independent`, and its proof. The chosen polynomial ring surjects onto the initial finite-type chart ring and therefore onto the limit; taking images of its kernel generators gives the required initial-ring kernel generators. Step 4 uses clause (2) of `lem-pc-filtered-colimit-commrings-elementwise` for equality of the fixed representatives to zero; the nonempty directed tail is a filtered small category and finite directed upper bounds combine the witnesses. The kernel inclusions and quotient identification are written explicitly. Step 5 uses the exact existence and uniqueness statements of `lem-weil-pbc-scheme-morphism-gluing`; local inverse agreement and both inverse identities follow by uniqueness and restriction.

I tested the empty scheme/empty affine cover, the zero ring, no polynomial variables, no kernel generators, a constant system, and an arbitrary directed index without a least element. The proof chooses an arbitrary initial index and takes its cofinal tail, so it does not assume a least index. Zero kernels already give stabilization at that chart's initial stage; empty charts are handled in step 5. The finite-type hypothesis is used for a polynomial surjection with finitely many variables, and the locally finite presentation hypothesis is used to finitely generate its kernel. Neither was replaced by finite presentation of the stages. No new statement remains to test.

The two off-unit generic tools, affine-transition limits and finite-data descent, are declared in `split_report.tool_uses`; all other citations are definitions or existing Mathlib leaves. No new-node search records were invented. I ran additional item searches using msearch, read the returned finite-type morphism equality and finite-presentation algebra results, and found no one-line stabilization specialization; LeanSearch reported unavailable. No Lean was written and no compiler or build was run.

## Unfinished work

None for this one-level split. The second reader must review and deliver; this worker runs only the dry run.

## Second reading by NO

Item statement: read Limits Tag 081B, label lemma-finite-type-eventually-closed, clause (3), hypothesis by hypothesis with Y=X and its identity. Quasi-compact stages, local finite type over arbitrary S, closed transitions, and local finite presentation of the limit are exactly retained; verdict: correct. No statement dispute.

Step 1: checked the two cited definition statements and 081B affine reduction; taking charts over an affine cover of S and then a finite subcover uses precisely local finite type and quasi-compactness. Quotient rings and surjective transitions follow directly from the affine closed-immersion definition; verdict: correct after removing needless chart refinements.
Step 2: checked the open-restriction and affine clauses of lem-weil-pbc-limit-affine-transition against Limits labels lemma-directed-inverse-system-has-limit (01YX) and lemma-directed-inverse-system-affine-schemes-has-limit (01YW); checked clause (1) of lem-pc-filtered-colimit-commrings-elementwise and the full affine-pair statement of lem-weil-pbc-lfp-affine-opens-finite-presentation against Morphisms 01TQ, lemma-locally-finite-presentation-characterize. The directed tail is filtered, the initial quotient maps are surjective, and q(V_t) is in W_t; verdict: correct with the smaller existing colimit leaf.
Step 3: checked lem-weil-pbc-finite-presentation-surjection-kernel-fg against Algebra 00R2, lemma-finite-presentation-independent, statement and proof. It permits any polynomial surjection, including n=0; images of its kernel generators generate the initial-chart kernel by lifting each element. Verdict: correct; no stage finite-presentation hypothesis used.
Step 4: read clause (2) of lem-pc-filtered-colimit-commrings-elementwise; equal fixed representatives, not newly chosen lifts, vanish at later stages. In a directed poset the two arrows from the initial stage agree; finite upper bounds combine witnesses. Both kernel inclusions follow from factorization and vanishing. Verdict: correct, including an empty generator list.
Step 5: read existence and uniqueness in lem-weil-pbc-scheme-morphism-gluing. Expanded how inverse maps land in the inverse image of each overlap and coincide there as inverses of one restricted isomorphism. Both identity composites hold on the specified covers. Verdict: correct; no affine-overlap or quasi-separatedness assumption.
New nodes: none; B1–B7 and new-node searches are vacuous. Opened the statements of all seven existing nodes mentioning 081B; none besides this item states clause (3)'s stabilization. Source-repository searches by item id and closed/finite-type/eventual keywords found no exact attachment.

Small cases: for a field or constant system zero kernels give immediate stabilization; n=0 still permits an arbitrary quotient of R and uses 00R2; one kernel generator uses one eventual-zero witness; for the zero ring, the unit in the kernel vanishes at a stage by clause (2); the empty scheme and empty cover give only empty later stages. An arbitrary initial index and its directed cofinal tail avoid a least-element hypothesis. Verdict: all checks pass.

Changes: removed the redundant finite-data tool citation in favor of clause (1) of the already cited Mathlib colimit leaf; simplified chart selection; made overlap agreement explicit; regenerated citations verbatim; removed the worker's split_report.tool_uses approvals (delivery-errors C8). The remaining generic affine-transition limit lemma is an off-unit tool: this unit has no construction/restriction statement for a given scheme limit, and the maintainer must record its acceptance. This supersedes the earlier Review by NO paragraph claiming worker tool-use approvals. Removed unlogged search entries and recorded actual log results, including the invalid Loogle query as invalid rather than evidence of no match.

Independent second-reader Mathlib search: msearch leanfinder, “A filtered colimit of quotient algebras with finitely generated kernel becomes constant at a finite stage”, returned the essential-finite-type equality/descent and finite-presentation coyoneda declarations. Read Algebra/Category/Ring/FinitePresentation.lean:45 and :81–143; these provide equality and factorization, not scheme stabilization or a one-line specialization of the item. The actual result is retained in searches.jsonl. No new Mathlib leaf, Lean writing, or compiler use.
