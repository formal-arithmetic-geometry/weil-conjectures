## What changed

Proved `AlgebraicGeometry.IsCurve.dense_open_vanishing_comparison`, with its statement
unchanged, in `Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison`.
All new imports are proof-only. Used the existing
`Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` theorem rather than rebuilding
its closed-complement cohomology argument. Proved the coefficient compatibility directly
by commuting the equivalence with Kan extension and sheafification. Proved both torsion
transfers along a monomorphism and the primary/invertible-order zero-sheaf argument.
Private helpers are proved completely; no helper changes a public signature or definition.
Updated only proof, proof_deps and proof_origin in the item's DAG node.

## Proved and sorry left

Proved `AlgebraicGeometry.IsCurve.dense_open_vanishing_comparison` (the sole original sorry).
No sorry remains in the delivered module, and no new sorry or module is introduced.
The proof depends on the previously stated `AlgebraicGeometry.IsCurve.dense_open_high_cohomology`
(node `lem-pbc-s2-dense-open-high-cohomology`), whose high-degree geometric obligation
remains downstream; this delivery does not assert that the complete target axiom closure is closed.
The coefficient/Kan comparison, primary_of_mono, invertible_of_mono,
primary_invertible_isZero and cohomologyIsoEquiv are all fully proved private helpers.

## No longer needed

No original statement import was removed. Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`
- `Sheaf.AlgebraicGeometry.CurveCoefficientPair`
- `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`
- `Sheaf.Paper.ZeroDimensionalCohomology`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.Finite.Stalk`

Their needed declarations remain available through the retained imports. The following original direct proof dependencies
are no longer used directly by this theorem:

- `def-weil-geometric-point`
- `def-weil-pbc-C1`
- `def-weil-pbc-C2`
- `def-weil-pbc-cohomology-pullback`
- `def-weil-pbc-constructible-torsion`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-extension-pullback`
- `def-weil-scheme-morphism-properties`
- `lem-weil-pbc-cohomology-pullback-derived-unit`
- `lem-weil-pbc-pullback-cohomology-long-exact-ladder`
- `lem-weil-pbc-zero-dimensional-cohomology`
- `lemma-weil-pbc-finite-direct-image-exact`
- `lemma-weil-pbc-finite-stalk-formula`

In particular the proof needs no direct imports of
`Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`,
`Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`,
`Sheaf.Paper.ZeroDimensionalCohomology`,
`WeilConjectures.SixFunctors.Finite.Exact`, or
`WeilConjectures.SixFunctors.Finite.Stalk`.
These may still be needed by the reused high-cohomology theorem or other targets;
this is pruning of this node's direct argument, not a claim that they leave the entire target closure.
The high-cohomology module's restriction-to-other-opens clause is not used here.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically sound but repeated the closed-complement comparison already
stated by `dense_open_high_cohomology`. The coefficient discrepancy is genuine:
G is formed by extending the abelian sheaf and then applying E, whereas the reused
lemma extends the module sheaf. The proof supplies an actual isomorphism for this
rather than assuming definitional equality. The high-degree comparison needs neither
constructibility nor torsion; hP remains in the unchanged statement.

Read Stacks Tag 0GJA (`lemma-restrict-to-open`), proof and remark (a), at
https://stacks.math.columbia.edu/tag/0GJA (the local literature .tex is absent).
The helper arguments follow that source's coefficient/torsion reasoning and the
existing proved local code in Reductions/UnderlyingAbelianAssertions/PrimeAnnihilatedInvertibleCases.
Checked the empty curve, zero sheaf, U=X, exponent zero, and characteristic zero:
Kan extension and the monomorphism arguments impose no nonemptiness or nonzero-stalk
condition; exponent zero forces the element to be zero; characteristic zero has no prime
CharP witness. Uniqueness of characteristic handles the primary branch, without
assuming that conditional primary assertions imply equivalent torsion predicates.

Searches actually run: leanfinder for the dense-open extension-by-zero comparison
returned Sheaf.H and unrelated scheme/etale-locus results; loogle for
AddEquiv.ofBijective returned the exact Mathlib constructor used; msearch grep returned
no hits, and local rg located DenseOpenHighCohomology and the stalkwise proof patterns.
No new node is needed. The imported high-cohomology node is in the same unit sk-thm-p1,
and the route through dense-open reduction is retained. No unit-realized node is bypassed.

## Second reading by P2

1. Compared the delivered module with the repository version. The public theorem signature is byte-for-byte unchanged; only proof text, proof-only imports, and the node's proof metadata differ. Verdict: pass.

2. Compiled the module with `lcompile.py`; it succeeds with no errors. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. An explicit `#print axioms` in a scratch copy reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`, permitted here because the reused high-cohomology statement is still open; verdict: pass.

3. The proof introduces no split-off statements or new nodes. Existing private helpers are fully proved and are not public API. Edge cases described in the proof docstring remain covered; verdict: pass.

4. The route reuses `dense_open_high_cohomology`, then transports coefficients and torsion along the counit monomorphism. The direct closed-complement and finite-stalk imports from the old route are pruned, while the unit route through dense-open reduction remains. Verdict: pass.

5. The DAG proof, proof dependencies, and proof origin match the implemented route, and the unit remains `sk-thm-p1`. Verdict: pass.

Changed only the report during this second reading, completing the list of removed imports and recording the explicit axiom check; no Lean or DAG repair was necessary.
