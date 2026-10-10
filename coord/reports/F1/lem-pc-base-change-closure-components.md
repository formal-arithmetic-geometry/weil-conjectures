1. Files written

- dag/nodes/sec-picard-framework/lem-pc-base-change-closure-components.json: repaired split; no Mathlib match.
- dag/nodes/sec-picard-framework/lem-pc-global-sections-separable.json: unsplit separability statement; no Mathlib match.
- dag/nodes/sec-picard-framework/lem-pc-separable-tensor-algebraic-closure.json: unsplit algebra statement; no Mathlib match.
- dag/nodes/sec-picard-framework/lem-pc-clopen-smooth-proper-curve.json: unsplit clopen permanence statement; no Mathlib match.

2. Attachments

None. No sorry-free declaration in the read-only Lean source states the parent or the new nodes exactly.

3. WANTED

None. I read the available Stacks sources in `/home/ubuntu/c1-stacks-review`: `varieties.tex` at Lemmas 0BUG and 0FD1, and `morphisms.tex` at Tags 01V6, 01W5, and 01W6. The parent also cites the existing DAG node for Cohomology of Schemes Lemma 02KH.

4. Problems found and corrected

The returned split merely relabelled the parent's three clauses. I deleted those three nodes and wrote the arguments in the parent. The imported blueprint's assertion that X over an algebraic closure is always connected is false: take X=P^1_C regarded as a curve over R; it has two complex components. The corrected parent statement was retained. The original degree step appealed to symmetry without identifying the components. It now identifies the sigma_j factor and compares each cohomology dimension over k, k', and Omega. I removed proof-only facts from statement dependencies and kept all surviving new statements in TeX.

5. Unfinished work

The three smaller nodes are unsplit stage-1 items and are intentionally left for later queue work.

## Review by F1

I read the parent blueprint paragraph in `lem-pc-ample-positive-degree`, the item source references to varieties.tex Lemmas 0BUG and 0FD1, and the exact source text in `/home/ubuntu/c1-stacks-review/varieties.tex` and `morphisms.tex` (01V6, 01W5, 01W6). I also opened every cited DAG node and copied its statement into `citations.json`; the delivery citation checker confirms each quote is verbatim. Step 1 now cites `lem-pc-projective-proper` for projective implies proper, `def-pc-curve` for the variety hypotheses, `lem-pc-h0-proper-variety` for finite global sections, and `lem-pc-global-sections-separable` for separability. Step 2 cites the tensor decomposition, flat base change, idempotent connectedness, proper and smooth base change, dimension base change, and the corrected clopen permanence statement; each cited statement supplies exactly that fact. I corrected the clopen node by dropping its false dimension-one conclusion, since a nonempty clopen component can have dimension zero in a disconnected smooth proper scheme.

For step 2 I moved the identification `X_j = X x_{Spec k',sigma_j} Spec Omega` and the dimension calculation into that step, explicitly checking that `X` is a curve over `k'` using integrality, separatedness, and finite type. For step 3 I added `lem-pc-euler-characteristic-well-defined` for finite-dimensional cohomology and finite alternating sums, and stated the quasi-compact and quasi-separated hypotheses needed by flat base change. I tested the statements on the one-component case, the real curve whose complexification has two components, and the trivial line bundle. The dry run `deliver.py ... --no-push` passed preflight at commit `e8ef0297`.
