## Worker report

The module states `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_finiteType` with a single `sorry`; no definition or proof is introduced.

Hypothesis and clause correspondence:
- A field K: `(K : Type u) [Field K]`.
- Nonnegative cohomological bound c and finite dimension d: `(c d : ℕ)`.
- cd_tor(K) ≤ c: `hK : HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c`.
- A K-scheme X: `(X : Scheme.{u}) [X.Over (Spec (.of K))]`.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of K))]` and `[QuasiCompact (X ↘ Spec (.of K))]`, exactly the conventions node's conjunction.
- Dimension d: `hX : topologicalKrullDim X = (d : WithBot ℕ∞)`, equality rather than an upper bound.
- Conclusion cd_tor(X) ≤ 2d+c: `HasTorsionEtaleCohomologicalDimensionLE X (2 * d + c)`.

Dependency interfaces read: `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`, declaration `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`. Its full body quantifies over every `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u+1}`, local `F.IsTorsion`, and every natural q strictly above c, and asserts Subsingleton of ordinary derived-section cohomology. The conventions node has no declaration and explicitly introduces no notion: Mathlib `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`, `AlgebraicGeometry.Scheme`, and `Spec` render its relevant conventions. `topologicalKrullDim` is Mathlib's supremum of chain lengths of irreducible closed subsets. Both recorded proof-dependency modules are imported without `public`.

Edge cases: c=0 and d=0 are allowed; no separatedness, smoothness, connectedness, characteristic or uniform torsion-annihilator hypothesis is imposed. No restriction on torsion primes. Zero sheaves are included by the predicate. The empty scheme has topological dimension bottom, so has no natural-number dimension d satisfying the node's equality; this follows the stated dimension-d hypothesis, without an extra Nonempty assumption. The universe u is arbitrary and coefficient size u+1 is exactly the recorded definition's size convention.

Searches performed:
- msearch leanfinder: “torsion etale cohomological dimension of a finite type scheme over a field bounded by twice dimension plus field cohomological dimension”; eight unrelated cotangent/etale algebra hits, no match.
- msearch loogle: `HasTorsionEtaleCohomologicalDimensionLE, topologicalKrullDim`; zero hits, first identifier unknown to the Mathlib service.
- msearch grep in Mathlib AlgebraicGeometry: `torsion.*[Dd]imension|subsingleton_H_of_two_mul_add_lt`; zero hits.
- rg in project Lean, upstream WeilConjectures, and upstream name index for the node id and chosen declaration name: the chosen name does not occur. The upstream file `WeilConjectures/AlgebraicGeometry/Sites/CohomologicalDimension.lean` contains `Scheme.subsingleton_H_of_two_mul_add_lt`; its complete signature and docstring were read. It uses `Sheaf.H` (Ext cohomology), while the dependency deliberately specifies ordinary derived-section cohomology, and it assumes dimension at most d rather than equality. It therefore is not an exact existing declaration of this node. No duplicate predicate is introduced.
- rg of `HasTorsionEtaleCohomologicalDimensionLE` in `lean/Sheaf` confirmed the dependency predicate and its existing uses, with no finite-type bound using it.

No statement correction, new node, dependency repair, or disputed assertion is needed. Server compile and preflight results are recorded below when complete. Second reading is left to the independently dispatched reader.

## Second reading by NX

I reread the blueprint node, its source text, the dependency declarations, and the proposed
module line by line. The node introduces a field `K`, a natural-number field bound `c`, a
scheme dimension `d`, and a `K`-scheme `X`. The Lean binders `(K : Type u) [Field K]`,
`(c d : ℕ)`, and `(X : Scheme.{u}) [X.Over (Spec (.of K))]` render these objects with the
same universe and base-field structure. The node hypothesis
`cd_tor(K) ≤ c` is exactly
`hK : HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c`. Its finite-type hypothesis
is rendered by `[LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]`,
the recorded Mathlib formulation of the convention's “locally of finite type and
quasi-compact”. The dimension hypothesis is rendered exactly as
`hX : topologicalKrullDim X = (d : WithBot ℕ∞)`. Finally, the conclusion is exactly
`HasTorsionEtaleCohomologicalDimensionLE X (2 * d + c)`, with the same arithmetic and
predicate as [def-sc-etale-torsion-cd]. No hypothesis is added, omitted, or strengthened,
and no conclusion clause is changed.

I checked the dependency declaration `AlgebraicGeometry.Scheme.HasTorsionEtaleCohomologicalDimensionLE`
in `Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension`: it quantifies over all locally
torsion sheaves on the small étale site and ordinary derived-section cohomology, matching
the node. The scheme-conventions dependency deliberately introduces no declaration, and
its finite-type convention is represented by the two typeclasses used above. The imported
affine and affine-to-global modules are proof dependencies only and do not alter the
statement.

Edge cases remain covered: `c = 0` and `d = 0` are permitted; zero sheaves are included by
the torsion predicate; no characteristic, separability, smoothness, connectedness, or
separatedness assumption appears; and the universe `u` is arbitrary with coefficient
category universe `u + 1`. An empty scheme is not excluded by an extra assumption (it simply
cannot satisfy the displayed natural-dimension equality unless the equality holds). Empty
index sets and torsion-prime restrictions do not occur in this statement.

I repeated searches with `rg` over `lean/Sheaf`, the upstream `WeilConjectures` tree, and
the DAG name index, and with the LeanFinder/Loogle/grep searches recorded by the worker.
The only related upstream theorem is `Scheme.subsingleton_H_of_two_mul_add_lt`; it uses the
`Sheaf.H`/Ext notion and a dimension upper bound, so it is not this ordinary derived-section
statement. No exact existing declaration was found. The module compiled successfully with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NX thm-sc-finite-type-torsion-cd ...`.

No mismatch was found, so no source-based statement correction, dependency repair, or new
node was needed.
