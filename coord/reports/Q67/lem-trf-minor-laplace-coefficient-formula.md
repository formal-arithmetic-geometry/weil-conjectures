## Files written

- `dag/nodes/sec-trace-formula/lem-trf-minor-laplace-coefficient-formula.json`: item, split; statement and statement dependencies unchanged; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-ordered-block-permutation-sign.json`: new statement-only combinatorial lemma, unsplit; no exact Mathlib match.
- `citations.json`: verbatim statement quotations for every proof-step citation.
- `searches.jsonl`: actual msearch results, retaining every query run.

One new node; zero Mathlib leaves. The item has four steps, 2275 characters in total, each below 2000 characters. There was no previous sandbox split or report to preserve.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, Laplace, minor, determinant and permutation-sign terminology; inspected the relevant linear algebra files. The Cauchy--Binet and minor-ideal declarations concern other statements; no completed project declaration gives this coefficient formula.

## WANTED

None. The relevant Stacks source and latest blueprint are present. Stacks omits the proof, so the detailed argument is explicitly agent-supplied rather than attributed to a nonexistent Stacks proof.

## What was wrong or incomplete

The item had no proof. Its source is only a hint: Stacks Tag 07Z7, `lemma-ideals-generated-by-minors` in `literature/stacks-project/more-algebra.tex`, says that the proof is omitted and suggests row or column expansion. It does not state the displayed arbitrary-column coefficient formula. I kept the correct statement, supplied a Leibniz grouping proof and isolated the ordered-subset sign lemma. No statement dispute or unit-route error was found.

The latest blueprint is `literature/blueprint/latest/`, snapshot main-20261023-1620 (7284bb09daf97437d544c51882b325f9c52cd345). I read `sk-i-curve-zero/_section.md`, `lem-trf-local-term-locality.md` and its proof there. The nearest blueprint ancestor is about contracting local terms, with no determinant clause. The existing chain reaches this elementary algebra tool through nodal-family geometry and Fitting ideals. The provenance fields say that explicitly; no local-term proof has been substituted or attributed to a determinant source.

## Searches and decomposition

Whole-DAG and whole-blueprint searches covered Laplace, determinant, complementary minors, shuffle, permutation sign, the exact new id, and Tag 07Z7. `tools/blueprint_refs.py ancestor` returned `lem-trf-local-term-locality`. Blueprint searches for Laplace, shuffle and complementary minors returned no matching statement. The existing single-deleted-index sign lemma `lem-pc-signed-face-permutation` is narrower: it gives a sign comparison for deleting one index, not the simultaneous ordered-block formula. The determinant-column-permutation node gives matrix reindexing, not the numerical sign of a shuffle.

All Mathlib searches ran through msearch.py and their returned hits were read. Two semantic phrasings for the item found single-column/row expansions, not its multi-column identity. For the new sign node, two LeanFinder phrasings, LeanSearch, Loogle and grep found `Equiv.Perm.sign_sumCongr`, `sign_subtypeCongr`, `signAux` and related lemmas. I read Sign.lean at the sign definition, multiplicativity, conjugation and `sign_sumCongr` declarations, and the inversion-product definition. Those do not give the explicit exponent for arbitrary increasing subset enumerations by one-line specialization. The new node therefore remains unsplit rather than being marked Mathlib.

The sign lemma is genuinely smaller than the item and is independent of matrices or rings. For its future worker, the argument is: let e_U list U and then U-complement, both increasingly. Moving u_a from its original position to position a uses u_a-a adjacent transpositions, so sign(e_U)=(-1)^(sum U-s(s+1)/2). The permutation e_I^{-1} sigma e_T preserves the first and second blocks and has restrictions alpha and beta; its sign is sign(alpha)sign(beta). Multiplicativity gives the stated exponent, because s(s+1) is even. This proof guidance stays in the report, outside the new statement-only node.

## Not duplicates

lem-trf-ordered-block-permutation-sign vs lem-trf-minor-laplace-coefficient-formula: the new lemma is a matrix-free sign identity for a single permutation and its two restrictions; the item proves a ring-valued sum of products of determinants by reindexing every permutation.

lem-trf-ordered-block-permutation-sign vs lem-trf-fitting-ideal-minor-inclusions: the existing statement is three ideal inclusions for arbitrary rectangular matrices, and says nothing about the sign of a permutation on ordered blocks.

lem-trf-ordered-block-permutation-sign vs lem-trf-column-extension-minor-coefficients: the existing node defines recursive polynomial coefficients for adjoining columns, whereas the new node is an integer sign formula with no matrix or polynomial variables.

lem-trf-ordered-block-permutation-sign vs def-trf-minor-ideal: the existing definition introduces the ideal generated by minors, with oversized-minor conventions; it contains no permutation sign theorem.

lem-trf-ordered-block-permutation-sign vs lem-trf-fitting-ideal-direct-sum: the existing statement concerns the zeroth Fitting ideal of a module direct sum and does not supply ordered complementary-block signs.

lem-trf-ordered-block-permutation-sign vs lem-trf-row-minor-ideal-stable-invariance: the existing statement concerns ideals of rows from a submodule, stabilization and automorphisms; it neither states nor implies the explicit sign calculation as a one-line special case.

lem-trf-ordered-block-permutation-sign vs lem-pc-signed-face-permutation: the existing statement deletes a single index and constructs the induced permutation; the new statement handles two arbitrary subsets and simultaneous permutations of both complements.

## Unfinished work

The new sign lemma is deliberately statement-only, as required for a one-level split. No Lean files were written and no compiler, Lake command or local preflight/review checker was run. Server dry run and delivery are the remaining mechanical steps.

## Review by Q67

I checked the actual source at Tag 07Z7, label `lemma-ideals-generated-by-minors`, including its omitted-proof sentence. It supplies motivation for both the item and the new node but no missing proof to quote. The complete new node introduces q, s, the ordered subsets, both complementary lists, sigma, alpha and beta, and the integer-valued sign. Its only specialized notion, sign, is defined in the statement of `def-weil-pbc-matrix-determinant`, which I opened. It has no proof steps or disguised proof sketch. The proof-origin record on the item honestly identifies the additional argument as written by an agent.

For step 1 I read `def-weil-pbc-matrix-determinant`: its statement uses exactly the column-index Leibniz convention Q_(sigma(j),j), and its empty determinant is 1. The step writes an explicit inverse bijection, with disjoint images I and I-complement; thus no subset-selection multiplicities or unproved equivalence are hidden. Step 2 cites the new node's entire displayed sign assertion, not a determinant or ideal statement; sigma(T)=I is exactly what step 1 constructed. It passes to R by the integer ring map, requiring no domain assumption. Step 3 uses `def-weil-submatrix`, whose statement defines restriction to selected rows and columns, and the Leibniz definition again. I checked that the increasing row and column lists occur in the same positions as those definitions. Its only other operations are splitting a finite product and distributing two finite sums in a commutative ring. Step 4 uses the explicitly stated empty determinant convention. For full subsets the exponent is twice the index sum; for empty subsets the sign is 1. These observations apply also to the zero ring and characteristic two.

I tested the sign assertion exhaustively for all 50363 pairs of a permutation and a subset in q=0 through q=6, reconstructing both induced permutations and using one-based signs (switching to zero-based indices changes the exponent by 2s). I also evaluated the full determinant formula in 1260 integer matrix/subset cases, q=0 through q=5, and its reductions modulo 1, 2 and 6. This covers empty matrices, both extreme subset sizes, noninitial retained subsets, nontrivial signs and zero divisors. These checks support the handwritten argument; they do not replace it.

Against delivery-errors B--E I verified self-contained statements, TeX escaping, correct Stacks label and scope, absence of duplicate exact statements, citations matching statement text rather than proof internals, no additional ring hypotheses, no use of ideals as a substitute for explicit coefficients, and no cycle through the parent fitting-ideal lemma. The single new lemma is a reusable permutation result rather than a restatement of a coefficient identity. Every citation has a verbatim quote in citations.json. All four proof steps are under the long-step threshold. No prior delivery needed correction; the main repair to the imported material is the previously absent proof and its explicit sign dependency.
