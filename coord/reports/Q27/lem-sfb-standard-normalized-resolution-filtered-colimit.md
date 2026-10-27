# Q27 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-standard-normalized-resolution-filtered-colimit.json`: existing statement, now split in seven steps. Exact full statement retained. Mathlib verdict: no exact match for the full dg-algebra and finite-equation assertion.
- `citations.json`: one entry per cited node per proof step, with literal statement text (or a literal relevant excerpt).
- `report.md`: this report. Search-command output is retained in `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No Lean was written or compiled; no repository or launcher file was written, and no git command was run by the worker.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, standard/normalized/polynomial resolution phrases and shuffle. The matches concern other resolutions, Ext normalizations or Koszul complexes; no declaration states this entire item. The existing standard-resolution node records a Sheaf declaration containing an unproved coherence theorem, not an attachment of this item.

## WANTED

No new missing source. The shuffle-normalization prerequisite already records a request for Weibel Section 8.5. This delivery uses that existing node's precise displayed shuffle formula and functorial dg-algebra theorem; it does not pretend that Stacks 019A proves the shuffle theorem. Its own multiplication comparison is checked directly from the displayed formula.

## What needed repair

The item was statement-only, not a failed earlier split. The sandbox contained only dispatcher marker files, with no item, report or previous split. There is no released repair note for this item. The original statement is correct as stated: no STATEMENT-DISPUTED correction was necessary. Its source correctly distinguishes Stacks' cotangent-complex statement from the additional dg and finite-equation assertions.

The critical potential gaps were confusing an algebra colimit with a module colimit, silently commuting quotient normalization with colimits, replacing the standard resolution of D by the constant D, or requiring flat tensoring. The proof now handles these explicitly. In particular, the degeneracy witnesses are lifted before using eventual equality in the unnormalized polynomial degree; the quotient argument never requires tensoring an injection. Tensor commutes with ordinary colimits even when S is nonflat.

## Blueprint and searches

Read GOAL.md, SETUP's three levels, the chapter and unit records, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit statement and direct-image proof. The latest direct-image paragraph (3) is the recorded distant ancestor of this generic algebraic prerequisite; no chapter or unit route is replaced. `tools/blueprint_refs.py ancestor` reports a null ancestor at the end of the inherited created-item chain, so its existing detailed `from.place` and `via` are preserved rather than inventing a blueprint id.

Searched the whole DAG for normalization/colimit, polynomial/colimit, finite equations, tensor/filtered colimits, and Tags 08S9/019A; read the relevant matches. Whole-blueprint searches: `polynomial colimit` (0), `normalization` (many unrelated normalization results), `standard resolution` (4 unrelated geometric/homological results), `shuffle` (0). No blueprint node states this item. Existing nodes already give all non-elementary inputs. A new polynomial-colimit node would merely package the three-line universal-property argument of Step 1; a quotient-colimit node here would merely package the representative calculation of Step 3. Neither was created.

Retained the item's five inherited Q118 search records and read their returned declaration names/results. Ran new searches, recorded exactly from the command log, to test whether a more general polynomial or normalization statement could supply the full item: Loogle `"MvPolynomial", "colimit"`, LeanSearch on filtered quotient normalization and shuffle products, grep on standardResolution/shuffle-colimit/normalization-filtered, and two differently worded LeanFinder queries. All services answered. Hits concern ordinary ring colimits, finite-limit interchange, or additive Dold--Kan. The representation standardResolution is unrelated. Read the ordinary filtered ring-colimit construction and the normalized Moore/Dold--Kan source at the returned declarations. None includes the specified standard polynomial resolution with shuffle multiplication and fixed S tensor as the asserted dg comparison, so this item is not a Mathlib leaf. No search that did not run was added.

## Not duplicates

No new nodes, hence no new/existing-node pairs. Reused the existing multivariate polynomial definition, standard-resolution coherence, quotient shuffle normalization, algebra-to-module colimit comparison, module elementwise and criterion nodes, and varying-ring tensor-colimit theorem. The naive-cotangent comparison is a different two-term object and was not used as a surrogate for the standard resolution.

## Review by Q27

I read Stacks cotangent.tex at 08PM (definition-standard-resolution) and 08S9 (lemma-colimit-cotangent-complex), including its proof about the free and underlying-set functors. I read simplicial.tex at 019A (lemma-decompose-associated-complexes), which constructs the functorial degenerate complement, and algebra.tex at 00D6 (lemma-directed-colimit), 00D7 (lemma-zero-directed-limit), and 00DD (lemma-tensor-products-commute-with-limits), including the direct tensor proof. Verified these tag/label pairs in tags/tags. The quotient/shuffle conventions are those of the existing normalization node, not a substituted Moore-kernel model. The proof is honestly marked agent-written because it expands the colimit observation and adds the multiplication and finite differential-expression checks. There are no new nodes requiring independent source review.

For Step 1 I read the full statement of def-weil-pbc-mv-polynomial-ring. Its evaluation existence and uniqueness are exactly what converts a compatible family of maps out of D[T_i] to a single map out of D[T]; this is a direct universal-property calculation, not an unproved adjoint-preservation assertion.

For Step 2 I read lem-trf-cotangent-resolution-coherence: its statement actually specifies the iterated free/forgetful terms and strict functorial simplicial maps. I read lem-weil-pbc-filtered-colimit-algebras-underlying-module: it states the underlying D-module colimit, not just existence of ring colimits. I read lem-weil-pbc-filtered-colimit-modules-elementwise: it gives both representatives and eventual equality, not just representatives. These prove the induction from the given underlying-set colimit and its next polynomial iterate. Constant base D and small nonempty directed I meet all hypotheses. No transition map is taken to be an embedding.

For Step 3 I checked the normalization node's actual J_n=sum im(s_r) and quotient definition. Since every s_r is D-linear, any element of that sum has exactly the finite witness form used in the proof; no finite-generation assumption on P is needed. The module elementwise node applies to P_n, whose colimit was proved in Step 2, and therefore detects vanishing of the lifted difference. At n=0 there are no degeneracy witnesses. This is a short representative argument from the cited statements, so it remains an elementary step rather than a new task.

For Step 4 I read the module-colimit criterion in full and verified both assumptions using Step 3. The comparison respects the alternating face differential by the stated simplicial functoriality. Positive degrees are uniformly zero. No colimit over a larger or nonsmall index is introduced.

For Step 5 I read the full varying-ring tensor-colimit theorem, including its formula for the canonical map and its naturality clause. Its constant-ring, constant-first-module specialization is exactly colim(S tensor N_i)=S tensor colim N_i. Identity transitions on the constant systems meet the semilinearity hypotheses, and nonempty directedness makes their colimits D and S. I separately checked S-linearity on pure tensors, whose generation is explicitly in def-weil-pbc-module-tensor-product; thus a merely D-linear theorem is not silently promoted to an S-linear conclusion. Its naturality supplies compatibility with differentials. S need not be flat.

For Step 6 I reread the normalization node's actual shuffle formula and functoriality. Each degeneracy and polynomial multiplication commutes with the cocone maps, so every term, sign and finite sum maps to the identical shuffle term at the limit. The pure tensor formula then proves preservation of the dg product and unit. To define the product on the underlying degreewise module colimit, different choices of stages agree after a common later stage by eventual equality; each dg identity has finitely many inputs and is already true at that stage. The comparison is bijective degreewise, which also forces its inverse to preserve the product and differential. No derived-category identification is substituted for the asserted strict dg-algebra isomorphism.

For Step 7 I checked that the module elementwise node applies to the degreewise D-module cocone of Step 5. A homogeneous expression has finitely many operations, and comparison maps preserve each one by Steps 5 and 6; evaluating first at a stage is therefore legitimate. Each equation is a single zero difference in its indicated degree. Eventual vanishing followed by a common upper bound proves simultaneous equality, including coefficients in the fixed S (which are present at every stage).

I checked delivery-errors B--E against the actual files: self-contained unchanged statement and matching definition dependencies; no new statement-only-node issue; exact source tags; actual logged searches; every proof use appears in proof_deps and in citations.json; every citation quote is literal text from the node statement. Checked dependency closure for all nontrivial citations: none reaches the item, so no new cycle. The generic off-unit tools are declared in split_report.tool_uses with their limited purpose; definitions and Mathlib leaves require no route change. There is no new node restating the item or a clause. All seven steps are below 2000 characters, and none hides a separate comparison lemma behind the word standard.

Edge cases I checked explicitly: a singleton index; noninjective maps such as Z[x] to Z killing x; S=Z/2 over D=Z (nonflat); D=0 and S=0 where defined; a zero coefficient limit reached without injective transitions; n=0; positive degrees; empty collections of elements or equations; and B=D with its unmodified iterated standard resolution. These checks required no changes of hypotheses. No error in the blueprint route was claimed.

## What remains

No unresolved part of this split. Existing prerequisite nodes remain their own tasks. Delivery is subject to the required server dry run and push; no global or local Lean build is part of this stage-1 work.
