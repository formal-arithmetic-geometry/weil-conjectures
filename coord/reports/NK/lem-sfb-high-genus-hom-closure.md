# Stage-1 report: lem-sfb-high-genus-hom-closure

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-high-genus-hom-closure.json`: split item; ten proof steps, unchanged mathematical statement, actual Mathlib searches added to the inherited records.
- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-hilbert-polynomial-representability.json`: new statement, unsplit; no Mathlib match. Full projective Hilbert functor, with fixed-polynomial projective pieces.
- `dag/nodes/sec-six-functors-basics/lem-sfb-graphs-open-in-hilbert.json`: new statement, unsplit; no Mathlib match. The graph transformation is representable by open immersions, Stacks 0D1A and 0D1B.
- `dag/nodes/sec-six-functors-basics/lem-sfb-nodal-trait-rational-domination.json`: new statement, unsplit; no Mathlib match. A nodal trait curve is normal, and a projective modification is dominated by a modification with rational connected reduced geometric exceptional fibres.
- `dag/nodes/sec-six-functors-basics/lem-sfb-generic-dvr-properness-criterion.json`: new statement, unsplit; no Mathlib match. The function-field DVR properness test, Stacks 0208.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`, `search-results/`: real msearch query records and saved result text; `write_split.py`: sandbox-only generation script.

All four new nodes have empty proof and proof_deps, null proof_origin and mathlib_match, status unsplit, complete statements and definition references. No Lean was written and no compiler or Lake command was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, Hom/morphism scheme variants, genus, semistable and nodal geometry. There is no project declaration covering the item or one of the four new statements. Incidental occurrences discuss unrelated cohomological counterexamples on nodal curves, not Hom representability or trait extension.

## WANTED

WANTED: de Jong, *Families of curves and alterations* (1997), Sections 3.9--3.12 and Lemma 3.13, printed p.609, for the item and lem-sfb-nodal-trait-rational-domination. The local archival PDF is absent; I read the publisher's primary PDF at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf .

WANTED: Grothendieck, Bourbaki Expose 221, *Les schemas de Hilbert*, Theorems 3.1--3.2, Proposition 3.8 and its Hilbert specialization, printed pp.259--266, for lem-sfb-projective-hilbert-polynomial-representability. The local archival PDF is absent; I read the primary PDF at https://www.numdam.org/article/SB_1960-1961__6__249_0.pdf . The original simplifies to locally Noetherian test schemes; the new statement uses the usual finitely presented functor on arbitrary test schemes. This is explicitly recorded rather than attributing that larger test category verbatim to the original wording.

No literature or coordination file was edited in the read-only repository. The proof is marked agent, with the de Jong source and the precise agent generalization identified. No SGA source is used.

## What was wrong or needed expansion

There is no statement dispute and no weakening. The item is already an agent generalization of de Jong's Lemma 3.13: a projective target with no nonconstant geometric P1 maps replaces a pure curve target whose normalized components have genus at least two. Reading the proof shows exactly where the latter condition was used: contraction of rational exceptional curves. The new split makes that use explicit and does not import either flatness or integrality of the target.

The source leaves the constant-map case to the reader and first replaces a nonconstant target curve by its normalization in the source function field. That replacement cannot be used for an arbitrary target. Here the graph closure and its finite birational projection supply the descent for both constant and nonconstant maps. No new node restates the trait extension conclusion; the argument remains in steps 4--7 of the item.

The blueprint ancestry command returns `blueprint.from.node = None`, consistently with this existing chain of created alteration prerequisites. I preserved the inherited place and via chain and added the exact de Jong substep to each new node. The main-20261015 direct-image node's clause (3), the unit and chapter records were read; their route is not changed. This item is not the unit's statement, so I did not alter realized fields.

The existing Hilbert nodes are for finite locally free subschemes of degree d. Their statements do not give the full Hilbert scheme of graph curves. The new Hilbert node supplies that missing theorem, while a separate graph-open node supplies the smaller representability comparison. The generic-DVR test is also missing from the existing statements: generic valuative tests using all valuation rings are not the restricted test used here.

## Not duplicates

lem-sfb-nodal-trait-rational-domination vs lem-per-regular-point-blowup-domination: the latter assumes regular two-dimensional local rings at finitely many specified points and supplies point-blowup domination; the new node covers a possibly singular nodal trait surface, includes its normality, and asserts the rational geometry of every geometric exceptional fibre.

lem-sfb-nodal-trait-rational-domination vs lem-per-normal-cover-point-blowup-refinement: the latter concerns a finite extension of the function field of an excellent regular local surface and a finite normal covering model; the new node has no covering field extension and treats a nodal curve family and arbitrary projective modifications with rational connected geometric fibres.

lem-sfb-projective-hilbert-polynomial-representability vs lem-pc-hilb-representable: the existing node represents only Hilb^d of finite locally free zero-dimensional subschemes; the new node represents flat finitely presented subschemes in all dimensions and includes projectivity of every fixed-polynomial piece.

lem-sfb-projective-hilbert-polynomial-representability vs thm-pc-hilb-curves: the existing theorem is for degree-d finite subschemes of a smooth proper curve over a field, not graph curves inside a relative product over a general Noetherian base.

lem-sfb-projective-hilbert-polynomial-representability vs sk-thm-picard-hilb-general: the named unit describes the finite-degree Hilbert functor and its construction, not the full projective Hilbert polynomial theorem. No general theorem is obtained merely from a pointer to it in the proof of sk-thm-picard-hilb-curves.

lem-sfb-generic-dvr-properness-criterion vs sk-lem-nagata-sketch-dense-valuative: the existing statement tests every valuation ring and a dense source; the new theorem permits testing only discrete valuation subrings of the function field of the integral source, under a locally Noetherian base hypothesis.

lem-sfb-nodal-trait-rational-domination vs lem-trf-nodal-pair-projective-resolution: that theorem assumes a smooth base over an algebraically closed field with SNC boundary and produces a smooth pair; it neither covers arbitrary DVR bases nor dominates an arbitrary prescribed modification with rational geometric fibres.

No existing node has source Tag 0D1A, 0D1B or 0208. The Tag 0AHI overlaps are distinguished above. I also searched the whole DAG by words and the imported blueprint with blueprint_refs search for Hilbert, Hom scheme, rational curve, nodal, valuative, DVR, Mor_S, graph and birational. I read the candidate statements, including the finite birational normal isomorphism, instead of creating a duplicate of them.

## Mathlib search review

Each of the four new nodes has its own leanfinder, leansearch, loogle and source-grep searches. The semantic queries use two phrasings, with the actual queries and result digests retained. The item also has fresh searches in all four forms and two leanfinder phrasings. All services answered; none was recorded as unavailable or inferred to be absent just from a failed service.

For Hilbert representability, the hits were properties of Proj of a given graded algebra, generic representability, and module projectivity. None represents subschemes. The graph queries found open maps, open-subscheme functors and open-immersion ranges, not a graph-open locus in a Hilbert scheme. The nodal queries found minimal Weierstrass models and smooth base-change results, not resolution of nodal surfaces or rational exceptional fibres. For the DVR criterion I read Mathlib/AlgebraicGeometry/ValuativeCriterion.lean: its future-project paragraph explicitly says that reduction to DVRs remains to be shown; IsProper.of_valuativeCriterion at line 341 requires the full valuative criterion. The generic-DVR node is therefore unsplit, not a false Mathlib specialization. Item searches returned general properness and rational-map representative results, none covering the Hom closure.

## Review by NK

I read delivery-errors B--E in full and checked the statements and proof against them. The item source was de Jong's printed p.609, including the full chain 3.9, Claim 3.10, 3.11, 3.12 and Lemma 3.13. I separately read Grothendieck's Theorems 3.1--3.2 and the Hilbert specialization for the first new node; Stacks quot.tex, lemmas Mor-into-Hilb and Mor-into-Hilb-open, with Tags 0D1A and 0D1B for the second; the rational-singularity and exceptional-curve paragraph of de Jong 3.13 and Stacks resolve.tex point-blowup domination 0AHI for the third; and the full statement (especially clause (4)) and proof of Stacks limits.tex, Noetherian-dvr-valuative-proper 0208 for the fourth. The nodal-domination node is deliberately an isolated geometric input, with no assertion about a target or extension, not the item's conclusion renamed.

Step 1 uses the actual finite-type-over-Noetherian statement, projective base change, H-projective composition, and projective-implies-proper statements. I checked the H-projective conventions in both definition nodes agree and that Spec(k) is Noetherian without assuming k finite. These citations supply precisely the product's projectivity and the properness/separatedness needed later.

Step 2 uses the new full Hilbert theorem and graph-open statement. The graph-open statement requires flatness and finite presentation of the source only; its target needs separatedness. I checked this distinction directly in 0D1A and 0D1B. The universal evaluation comes from the inverse first graph projection, as the cited statement explicitly specifies.

Step 3 uses finite-type-over-Noetherian and birational-isomorphism-dense-open. The point has residue field K, since it is a K-rational point of M_eta. Localizing a reduced closure gives its closure in the generic fibre, and a rational section of a separated K-scheme is closed. This proves R_eta=Spec(K), rather than just generic dominance. R stays within the single open-and-closed Hilbert-polynomial piece; that piece is Noetherian, so its open morphism locus is quasi-compact and finite type. The birational dense-open lemma's separatedness, local finite presentation and finite-component hypotheses all hold. No properness was assumed to prove birationality.

Step 4 invokes the exact function-field DVR criterion, not the all-valuations criterion. The test ring need not be excellent. Nodal-family-geometry applies to the Noetherian base T and preserves every fibre hypothesis; the generic point maps to eta, so the smooth geometrically integral generic fibre is unchanged. The graph closure is taken in C times_T X, and its projection is projective by base change. This is a modification of C, not a modification of the target X.

Step 5 invokes only the new nodal rational-domination statement. It supplies normality of C and a proper surjective dominating map with connected reduced rational geometric fibres. On every P1 component the hypothesis of the item applies over the very same algebraically closed field Omega. Intersecting components force their constant values to agree; connectedness of a finite union gives a chain between components. Nilpotents of a fibre do not affect its underlying image. The proper surjective map remains surjective under field base change (a nonempty residue-field fibre stays nonempty), so the graph projection has singleton geometric fibres. This proves the needed finite-fibre conclusion even if Q is nonreduced or has several components.

Step 6 uses projective-proper, the finite-iff-proper-finite-fibres statement, and the finite-birational-normal isomorphism theorem. I opened all three nodes: the finite-fibres theorem allows any locally Noetherian target C, and the last theorem assumes normality only of the target C of the graph projection, not normality of Q. Thus the graph projection is an isomorphism and gives the extension. This is the actual contraction argument; it is not an appeal to an uncited general descent assertion.

Step 7 uses the DVR criterion again. A lift to M factors through R by vanishing of its defining ideal after injection A to K; a merely set-theoretic factorization would not suffice. Separatedness supplies uniqueness. Step 8 cites proper-to-separated and proper-immersion-closed; both statements were opened and say exactly what is used. The resulting closed immersion into the chosen projective Hilbert piece supplies a finite projective-space embedding without any ambiguous projective-bundle convention.

Steps 9 and 10 are elementary universal-property calculations. I wrote the conjugation formula, its inverse and its composition law. An isomorphism of schemes preserves topological closure and reduced induced structure, so it preserves R even if it changes the chosen Hilbert polynomial embedding. Evaluation is equivariant by its defining action on test points. No geometric group-quotient or faithful-action theorem is hidden here.

I checked empty and constant cases. Empty Hilbert pieces, including the empty subscheme, are harmless; W has nonempty fibres and the supplied generic map gives a genuine graph. A smooth trait family with identity modification has only point exceptional fibres; a node of thickness n has the usual rational exceptional chain, and further point blowups keep rational geometric components. Constant generic maps are handled by exactly the same graph argument. S=Spec(k) makes R the supplied rational point, and the DVR test is vacuous when K has no DVR subrings compatible with S. The counterexample target P1 would permit a nonconstant exceptional image, so the no-rational-maps assumption is used rather than silently dropped. No perfectness, characteristic-zero, normality of Q, target flatness, or excellence of a test DVR is required.

All cited-node quotes in citations.json are exact copies from the statements read. All non-elementary inputs have statement-node citations; all four new statements are self-contained and leave their proofs for later splitting. No proof step exceeds 2000 characters. The new nodes are not elementary rewrites, duplicates, or clauses of the item: the item itself assembles Hilbert representability with an open graph comparison and proves trait extension by rational domination and finite birational descent. Off-unit generic scheme tools are declared only in split_report.tool_uses for maintainer review. The server check_dag and review_split calls passed before this report was written; final deliver.py dry-run and push follow.

## Unfinished work

No part of this one-level split is left unfinished. The four new statement-only nodes are intentionally unsplit, as required by the worker brief. There are no new Mathlib leaves. Independent maintainer review and later splitting of those inputs remain the project workflow.

## Dry-run repair

The first deliver.py dry run found one B2 wording fault in step 5: “the item's hypothesis” was not self-contained. I replaced it with the explicit geometric hypothesis that every morphism P1_Omega to Q_Omega is constant. The mathematical statement, dependencies and argument are unchanged. I regenerated the verbatim citation audit after the edit and reran the full dry run.

The first repaired full dry run passed at 99e8d4ae8bf. Before pushing I expanded the elementary Noetherian polynomial-ring argument behind local finite presentation in step 3, explicitly cited the existing finite-type-over-Noetherian node to make C Noetherian in step 4, and wrote the nonzero field-tensor argument for preservation of surjectivity after field extension in step 5. These add no new lemma or hypothesis. The citation file was regenerated and the final dry run was repeated on the exact revised files.
