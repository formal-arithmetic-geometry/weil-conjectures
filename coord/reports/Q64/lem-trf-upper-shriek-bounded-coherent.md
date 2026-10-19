# Q64: lem-trf-upper-shriek-bounded-coherent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-upper-shriek-bounded-coherent.json`: statement, split; no exact Mathlib match. The seven proof steps use existing nodes only.
- `citations.json`: thirteen verbatim statement quotations, one for each use in each proof step.
- `searches.jsonl`: five actual Mathlib queries and their returned summaries, produced by msearch.py. `write_split.py` is a sandbox-only preparation script.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree by the exact item id, by the blueprint tag, and by algebraic/relative-dualizing, bounded-coherent and upper-shriek terminology, including the relevant six-functor source files. The upper-shriek hits concern etale/pro-etale coefficient sheaves, not the ordinary derived categories of modules for finite-type Noetherian ring maps. No project declaration gives this item. Upstream master remains reference material, not completion evidence. This created item has no `lean_audit` entry to expand.

## WANTED

None. All proof sources used are present locally.

## What was wrong or changed

The item was statement-only. Its statement is correct and is unchanged byte for byte. The explicit hypothesis that A is perfect over the chosen polynomial presentation is exactly what the computation needs; it does not require flatness of R to A. I added the existing notion nodes for D(R), finite type algebras, polynomial rings, perfect ring complexes and finite modules to `stmt_deps`. I preserved all inherited metadata, original search records and blueprint ancestry, filled the proof and its origin, and searched `same_as` (no matching blueprint statement).

The proof follows Stacks `dualizing.tex`, Tag 0BZK, `lemma-shriek-boundedness`, part (2). It expands the source's bounded finite-projective computation using the already available module-complex model instead of creating another tensor-Hom or finiteness lemma. This is the same polynomial-resolution argument, with good truncation written explicitly. The three levels remain fixed: no unit or chapter record changes, and no replacement of the semistable/coherent-duality route recorded in the item's ancestry. There is no statement dispute or source error.

The five new queries were run through the prescribed command. LeanFinder was queried first for upper shriek and then for the more general finite-projective derived-Hom preservation fact. I read all returned signatures: condensed finite-free functors, Grothendieck categories, cohomological-support instances, K-projectivity and Ext facts do not state this item. Loogle's quoted upperShriek search and the grep for upperShriek/relativeDualizing/dualizingComplex returned no hits. LeanSearch returned ordinary ring/scheme inverse-image and sheaf-comparison declarations, none an algebraic duality boundedness theorem. All five services succeeded, so none is recorded as unavailable. The inherited four Q102 search records were preserved as inherited records, not claimed as newly run by Q64.

## What could not be finished

Nothing mathematical remains for this one-level split. Supporting nodes remain at their existing project stages. Delivery validation is recorded below after running the required server dry run.

## Not duplicates

No new node was created. Whole-DAG and whole-blueprint searches for 0BZK, upper shriek bounded coherent, derived Hom with projective complexes, and finite Noetherian cohomology found the existing facts used here. In particular, `lem-trf-algebraic-shriek-relative-perfect` is the parent using this item and is not used in its proof; `lem-trf-perfect-complex-derived-biduality` only states perfect duality/biduality, not the preservation statement; the scheme-level `lem-pc-perfect-tensor-bounded-coherent` requires a different sheaf comparison and is unnecessary. No new copy of any of these is introduced.

## Review by Q64

I read Stacks `dualizing.tex` at `lemma-shriek-boundedness` (Tag 0BZK), its polynomial construction immediately above (0BZI), and the downstream use in `lemma-relative-dualizing-algebraic` (0BZW). The source works with ordinary unbounded derived module categories. I kept these coefficient categories throughout. I also read `more-algebra.tex` at 066E (`lemma-Noetherian-pseudo-coherent`), 064K (`lemma-derived-tor-quasi-isomorphism`) and 0A66 (`lemma-RHom-out-of-projective`), and `algebra.tex` at 00FN (`lemma-Noetherian-permanence`) and 00IK (`lemma-Noetherian-basic`). There are no new nodes needing additional source reviews. I read the trace-formula chapter, its sk-i-curve-zero unit and current blueprint proof of lem-trf-local-term-locality; this item serves the previously recorded coherent relative-duality subbranch rather than asserting an etale purity theorem. No SGA source is used.

For step 1 I opened the statements of the algebraic-shriek calculus, the perfect-ring-complex definition and the Noetherian finite-type algebra theorem. The calculus supplies the actual polynomial Hom model with the A-action, not merely existence of some right adjoint. Perfectness is a hypothesis for the chosen presentation, so the bounded projective E is supplied by the definition, with no need to use the parent flat-algebra theorem. The polynomial algebra has finitely many variables over the assumed Noetherian R, verifying the Noetherian theorem's hypotheses.

For step 2 I checked that the cited Noetherian pseudo-coherence criterion has both directions, assumes only an upper cohomology bound and finite cohomology, and applies over R. Its definition node explicitly supplies a bounded-above finite-free representative. I checked the bounded-flat K-flat statement and the derived-change-of-rings statement: the former applies to F after its free terms are shown flat, and the latter computes change of scalars in D(P) on that F. This avoids treating an arbitrary finite module as projective or assuming K perfect.

For step 3 the cited polynomial definition really gives finite monomial expansions and the cited flat-tensor theorem really preserves exact module sequences. I wrote out why tensor with P is a direct sum and hence exact, before invoking flat-tensor exactness to compute cohomology. The lower bound comes from K's cohomology; the upper bound also comes from the strict bound on F. For step 4 I recomputed the cohomology of the explicit cokernel truncation. In degree a it is the original kernel modulo the old boundaries, above a nothing changes, and below a both vanish. Finiteness of its only new term follows by taking images of generators in the quotient. This is an elementary construction, not an uncited bounded-coherent replacement theorem.

For step 5 I read the full statement of `lem-sc-affine-projective-complex-derived-hom`: it applies to module complexes on the one-point ringed site, with bounded-above projective source and bounded-below target, and states precisely the ordinary product-total Hom representation. Both bounds are supplied here. I checked the projective definition's lifting clause, which splits the finite free surjection onto E's term. Taking Hom reverses its two maps and still gives a retract. Projecting the finitely many generators proves the finite Hom term assertion directly. I checked the interval inequality a <= i+t <= b and u <= i <= v, obtaining [a-v,b-u]. No comparison, filtration convergence or spectral-sequence theorem is concealed in this step.

For step 6 I read the finite-submodule statement and checked P's Noetherianity was already established. It makes the cycles finite; projecting cycle generators proves finite cohomology without any assertion about infinite products. The calculus explicitly says forgetting the coinduced action gives ordinary derived Hom; exact restriction leaves cohomology groups unchanged. I checked the cohomological convention H^t(C[n]) = H^(t+n)(C), so the final interval is [a-v-n,b-u-n]. A finite P-generating set remains an A-generating set by mapping its coefficients. This uses no conservativity stronger than exact scalar restriction. Step 7 is the explicit R[0] specialization, including the zero ring.

I tested identity maps with the zero-variable presentation, polynomial extensions with A=P (the shift produces degree -n), a quotient Z to Z/p (the two-term resolution gives Ext in degree +1), zero inputs and the zero algebra. I also tested the identity over k[epsilon]/(epsilon^2) on the residue field: its finite-free resolution is unbounded to the left, but the good truncation remains a bounded finite module complex, so the proof does not silently impose finite projective dimension on K. None of the elementary steps packages a separate hard lemma. Every step is under 900 characters; none exceeds the 2000-character long-step threshold. All thirteen citation quotes were checked as exact substrings of the existing node statements. The generic off-unit tools are declared in split_report.tool_uses with the reason each is needed.

I checked delivery-errors B through E against the actual files: no new unsplit proof sketches or ambiguous object hypotheses, no restatement children, no parent dependency, no use of a cited proof in place of its statement, and no coefficient-category or shift change. All writes are confined to this item's sandbox; no Lean or compiler/build command was used.

## Delivery validation

The first dry run rejected the conclusion-only quotation of the finite-type Noetherian-algebra theorem as too short. I replaced it by that node's whole statement, including the hypotheses. The repaired required `deliver.py ... --no-push` then exited 0 and printed `OK (not pushed)` at c2cc0afcdb: server preflight passed. No mathematical or node change was needed after that successful check.
