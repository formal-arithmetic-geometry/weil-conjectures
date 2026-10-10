# lem-weil-pbc-two-term-homotopy-equivalence-direct-sum

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-two-term-homotopy-equivalence-direct-sum.json`: split the existing statement; no new node or Mathlib leaf was needed. The existing `def-weil-pbc-direct-sum-modules` is the sole dependency.

## Attachments

None. This node has no Lean declaration in its `lean_audit` record.

## WANTED

None. Stacks Project Algebra, Lemma 00S3 (`lemma-sum-two-terms`), is available in `algebra.tex` at lines 35709-35754.

## Source and split

The statement writes out exactly the two chain-map equalities and four homotopy identities assumed in Stacks 00S3. Its conclusion is the same isomorphism of binary direct sums. The proof now defines the two block maps, computes both products, gives explicit inverses for the resulting triangular maps, and shows the left and right inverses of the block map coincide. Stacks prints only one product and calls invertibility trivial; the reverse product and inverse argument are expanded here.

The item had no proof, no statement dependency for direct sum, and no split report. All three were supplied. No blueprint or source statement error was found. The existing Mathlib searches cover LeanSearch, LeanFinder/Loogle, and source grep; none matched this isomorphism. No new statement was introduced, so sections B1-B8 have no new node to check.

## Source error

In the displayed product in Stacks Algebra 00S3, `algebra.tex` lines 35737-35751, the upper-right entry is printed as $-h'\circ\psi_1+h\circ\psi_0$. The first composition is ill-typed: $\psi_1:B_1\to A_1$ but $h':B_0\to B_1$. Multiplying the displayed matrices gives $-\psi_1\circ h'+h\circ\psi_0:B_0\to A_1$. The reverse product, omitted in Stacks, is $CD=\begin{pmatrix}\mathrm{id}_{B_1}&\varphi_1h-h'\varphi_0\\0&\mathrm{id}_{A_0}\end{pmatrix}$; its entries have the stated types by the chain-map and homotopy identities. This repairs only the proof calculation; the item's mathematical statement and conclusion are unchanged.

For sections C-E: each step uses only the cited binary direct-sum definition and the explicit maps and identities in the item's own statement. Matrix multiplication and the triangular inverse are written out rather than delegated to an uncited fact. The block maps have the correct source and target even when a summand is zero. If all four modules are zero, each map is the unique map on zero; if both complexes are identical with identity comparison maps and zero homotopies, the formula is the triangular isomorphism $(a,b)\mapsto(a,d_Aa+b)$. The argument needs no finiteness, projectivity, or cancellation hypothesis. It follows the source's route and creates no cycle.

## Checks

- `python3 tools/review_split.py lem-weil-pbc-two-term-homotopy-equivalence-direct-sum`: PASS, 0 new nodes.
- `python3 tools/check_dag.py --cycles`: 0 cycles and 0 self-loops; exit 1 for seven pre-existing, unrelated unreachable constructible-approximation nodes.

## Unfinished

Nothing in this item. The global reachability warnings were not changed because they concern other items.
## Review by G1

I read Algebra Lemma 00S3 (`lemma-sum-two-terms`) in `algebra.tex:35709-35754`. The item writes the two chain-map equations and four homotopy equations implicit in the source's two-term homotopy equivalence, and its direct-sum isomorphism conclusion is unchanged. `def-weil-pbc-direct-sum-modules` supplies the only named construction needed; the matrix proof is expanded from the item's own hypotheses, with no new node.

Step 1 defines C and D on the stated summands with matching source and target types. In step 2 I multiplied the blocks in both orders: DC has identity diagonal and upper-right `h psi_0 - psi_1 h'`; CD has identity diagonal and upper-right `phi_1 h - h' phi_0`. The chain-map equations cancel the lower-left entries and the homotopy equations give the diagonals. Step 3 explicitly inverts both triangular products and derives a common left and right inverse for C, so no cancellation, projectivity, or finiteness assumption is used. The proof steps carry the calculation themselves and do not cite a tag as a substitute for a node.

I checked zero summands, zero differentials, and identity comparison maps; each formula remains typed and the inverse calculation still works. The worker found a source proof typo: 00S3 prints `-h' psi_1` in the upper-right of DC, which is ill-typed; direct multiplication gives `-psi_1 h'`. I sent this E6 issue back to the worker, who added the `## Source error` section. The theorem statement needs no change. No new nodes require B checks, the unit route is unchanged, and `review_split.py` passes with zero DAG cycles.
