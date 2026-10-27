# Stage-1 worker report: lem-sfb-holomorphic-coordinate-division

## 1. Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-holomorphic-coordinate-division.json`: the existing item, now `status: "split"`, with a four-step agent proof by convergent multivariable power-series coefficient division. The statement, `stmt_deps`, source and inherited blueprint metadata are retained. Mathlib verdict: no match.
- `citations.json`: empty list, because the proof is self-contained and cites no other DAG node.
- `searches.jsonl`: the four searches actually run by `msearch.py` for this item.
- No new nodes and no Mathlib leaves.

## 2. Attachments

None. I searched `lean/WeilConjectures/` and `lean/Sheaf/` for the item id, its blueprint tag, holomorphic-coordinate terminology and coordinate-division terminology, and searched the slopmaster2 checkout for the same. There is no exact project declaration, and no sorry-free declaration to attach.

## 3. WANTED

- `WANTED: literature/serre-gaga.pdf, Serre GAGA §1 no.1 (printed p.3), for the definition of holomorphic germs by convergent power series and the surrounding local analytic context.` The file is not present locally. The proof is therefore marked `proof_origin.by = "agent"` and gives the coefficient argument explicitly; no claim is made that the missing source states this exact lemma verbatim.

## 4. Findings and changes

The live item was `unsplit` and had an empty proof. Its statement is mathematically correct, including the pulled-back parameter term and the cases `r=0` and `d=0`; no `STATEMENT-DISPUTED` correction is needed. The inherited blueprint place identifies the smooth-coordinate calculation in the Serre Proposition 4 input, and a whole-blueprint search found no separate node stating this lemma. A DAG search found no duplicate; the sibling analytic-closed-ideal node uses this item as an input.

The proof chooses an absolutely convergent power-series representative on a polydisc, restricts to `z=0`, assigns each nonconstant monomial to its first nonzero `z` coordinate, and divides that monomial by the chosen coordinate. On a smaller polydisc the divided series is bounded termwise by `s⁻¹` times the original absolutely convergent series, so it defines a holomorphic germ. The coordinate index sets partition all nonconstant monomials, giving the required equality after regrouping. The zero-coordinate and no-parameter cases were checked directly, as were the monomials `z₁z₂`, a parameter-only germ, and the empty sum.

No new node is appropriate: the convergence estimate is the two-line coefficient estimate from the defining convergent-series representation, while a separate node would merely extract a clause of this item. The four Mathlib searches found only one-variable analytic/meromorphic factorization, scalar division, formal power-series substitution and germ utilities; none states joint coordinate-ideal division.

## 5. Unfinished work

None for this stage-1 split. No Lean file, compiler, Lake/build tool, repository file or launcher file was written or run.

## Not duplicates

No new nodes were introduced, so there are no new-node duplicate pairs. The existing `lem-sfb-holomorphic-weierstrass-division` is a different statement: it concerns analytic Weierstrass division after linear regularization with a polynomial remainder, whereas this item divides a germ vanishing on a coordinate subspace by the coordinate ideal with parameters.

## Review by Q35

I read the assigned item, its chapter `sec-six-functors-basics`, unit `sk-thm-sf-ctf-stability`, the current blueprint reference in the item, and the sibling node `lem-sfb-analytic-closed-ideal-local-quotient` that consumes this lemma. The local Serre GAGA PDF named by the item is absent, so I used the source locator only for provenance and wrote the power-series proof as an agent argument. I also read the existing Mathlib analytic-operation and Taylor-jet nodes to check for a reusable statement; neither supplies the required several-variable ideal division.

Step 1 uses only the item's definition of holomorphic germ: a representative has a convergent power series on a neighbourhood, and after shrinking to a common polydisc the usual absolute-convergence estimate applies. Step 2 is the direct restriction of that series to `z=0`; it removes exactly the terms with nonzero `z` multi-index and identifies the pulled-back `H(0,t)`. Step 3 defines `H_j` using the least positive coordinate of each multi-index and verifies convergence on a smaller polydisc by the explicit `s⁻¹` bound; this is the only analytic estimate, and it is written out rather than hidden behind an uncited lemma. Step 4 checks the monomial identity, the partition of the index set, and the `r=0`/`d=0` edge cases. Since no step cites a DAG node, `proof_deps` and `citations.json` are correctly empty.

I checked the statement on `H=0`, a parameter-only germ, `H=z₁z₂`, `r=1`, `r=0`, and `d=0`. The four recorded Mathlib searches are exactly those run in `searches.jsonl`, including the rejected Loogle identifier and its no-match verdict. No SGA source is cited, no off-unit tool use is asserted, and no unit or chapter record was modified.
