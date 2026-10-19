# Q44 — lem-trf-congruence-polynomial-kernel

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-congruence-polynomial-kernel.json`: statement, split into seven elementary steps; no exact Mathlib match.
- `citations.json`: `[]`, because no step cites another DAG node.
- `report.md`: this report. The search wrapper also wrote `searches.jsonl`.

There are **0 new nodes and 0 Mathlib leaves**. No Lean, compiler, git command, or live-project edit was used.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and the read-only upstream master for the blueprint tag, monoid-algebra kernel, and congruence terminology found no declaration of this statement. The upstream master was treated only as reference material.

## WANTED

None. The proof is an agent-written elementary argument, explicitly marked as such. It does not attribute the kernel formula to the supporting Mathlib quotient facts.

## What was wrong and what changed

The item was a correct statement with no proof. Its source already warned correctly that `Con.mk'_ker` does not state the monoid-algebra kernel formula. I retained that warning and supplied the argument rather than using the quotient congruence theorem as though it proved the algebra theorem. The mathematical statement is unchanged; doubled TeX escapes were normalized to single TeX command backslashes.

The nearest blueprint ancestor is `lem-trf-local-term-locality`. I read its current main-20261015 statement and proof, the unit `sk-i-curve-zero`, the chapter record, and the immediate parent `lem-trf-fg-commutative-monoid-finite-presentation`. This is a supporting elementary algebra calculation in the inherited chart-spreading ancestry, not an alteration of the unit's geometric route. The immediate parent's steps 1 and 3 need the two clauses proved here. The blueprint ancestor itself contains no separate statement of this algebra fact. The existing `blueprint.from` ancestry was retained and its `same_as` remains empty after whole-blueprint searches for monoid algebra, congruence, kernel/basis/monomial/mapDomain concepts.

The inherited Mathlib searches were retained. Six actual new queries, recorded by `msearch.py`, were appended. These include a second semantic phrasing in terms of finitely supported functions and two grep queries. I read the search hits, including `Con.mk'_ker` (Hom.lean:154), its quotient-map surroundings and lift (195-213), `Finsupp.mapDomain_apply_eq_sum` (Basic.lean:1432-1434), `Module.Relations.ker_toQuotient` (Presentation/Basic.lean:88), and the definition of `Algebra.Presentation` (Presentation/Basic.lean:56-63). The last is not a proof of the kernel formula: its kernel equality is a field of the presentation one must supply. The module result describes a quotient by given linear relations; identifying it with the free module on congruence classes is precisely the argument required here. Neither is a one-line specialization proving the item. `Finsupp.ker_mapRange` concerns coefficient maps, not pushforward along an index quotient; the search result `range_lmapDomain` concerns the image, not this kernel.

## What remains unfinished

No mathematical work remains in this split. Validation and push results are recorded below after the required commands finish.

## Not duplicates

No new node was created. Before choosing the direct proof, I searched the full DAG for congruence, monoid algebra, MonoidAlgebra.lift, AddMonoidAlgebra.lift, kernel/basis/monomial combinations and Finsupp/mapDomain terminology, and used `tools/blueprint_refs.py search` for the whole blueprint. The only node stating the kernel formula was the item. The parent uses this formula and cannot be cited back without a cycle.

## Review by Q44

I read delivery-errors B through E in full and checked the seven steps against the actual definitions, with the node and supporting source open. There are no new-node statements to audit or hidden facts delegated to a freshly named copy of a conclusion. The statement already introduces the congruence, quotient, and monoid algebra, so no missing definition dependency was added. There is no Stacks result used in the argument and therefore no invented Stacks tag or section citation. Mathlib supplies the supporting quotient terminology, not a claimed literature proof of the item. No SGA source is involved.

Step 1 uses only the formula for the given map and the definition of the generated ideal as finite sums of ring multiples; the image of each such sum is displayed. Step 2 takes the coefficient of each quotient basis symbol after partitioning a finite support by its image. I explicitly wrote why the subsets partition the support and why the coefficient is the sum over its fibre, so no free-module quotient identification or exactness theorem is used without a node. Step 3 chooses representatives only for the finitely many nonempty fibres meeting that support. Equality of quotient classes means the two elements are related by c (the quotient definition, consistent with the statement read at `Con.mk'_ker`), and the displayed identity follows by expanding and cancelling two finite sums. Step 4 multiplies each generating difference by the ring element `a_m[0]` and adds the resulting terms; this verifies ideal membership instead of citing a kernel lemma. It also handles empty support explicitly.

In step 5 I checked all three equivalence-relation laws for d by the displayed zero, negation, and addition identities. Step 6 verifies the precise translation compatibility from the item's definition of monoid congruence, using `[u+w]-[v+w]=[w]([u]-[v])`; this holds without cancellativity, integrality, or saturation of M. It then uses the stated intersection/minimality definition of c, and checks that d contains S. Step 7 applies the definition of generated ideal to get the reverse inclusion and concludes the second formula from the first. These are seven short elementary calculations, each 378-518 characters except the 377-character first step; no step exceeds 2000 characters or hides an independently invoked comparison theorem. Every step's uses is empty; there are no unverifiable node quotations, and citations.json is consequently the empty list.

I checked all hypotheses where used: A is a ring so subtraction and negative closure are available; coefficients act by multiplication with `a[0]`; M is commutative so its algebra is a commutative ring and the translation product formula holds in the stated order. Only the finite support, not M, its quotient, or S, must be finite. Minimality is used only under the second-clause assumption. No basis-vector separation over a nonzero ring, domain hypothesis, or injectivity of A into a different ring is assumed.

Small cases checked by the formulas: if A is the zero ring, every coefficient and both ideals are zero and the calculation still applies. If c is equality, each fibre of the support is a singleton and the kernel is zero. If M is the one-element monoid, the map is the identity of A. If S is empty or contains only diagonal pairs, its generated congruence is equality and J=0. For M=N and relation 2~1, the formula gives `(t^2-t)`; for 2~0 it gives `(t^2-1)`, including characteristic 2. For the noncancellative monoid `{0,e}` with e+e=e, the diagonal congruence gives the identity of `A[t]/(t^2-t)`, and identifying e with 0 gives kernel generated by `t-1`. These examples check both minimality and the translation identity without introducing extra hypotheses. No statement dispute or route change was necessary.
