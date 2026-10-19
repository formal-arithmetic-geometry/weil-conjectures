## Worker report

The module `Sheaf.TraceFormula.TotalSiteSimplexFreeResolution` states the componentwise exact augmented simplex resolution. `simplexModule Λ m p M` is the direct sum of copies of `M` indexed by morphisms `[p] → [m]` in Mathlib's `SimplexCategory`; `simplexFaceLinear` sends the α summand to the `δᵢ ≫ α` summand; `simplexDifferential` is the alternating sum; and `simplexAugmentation` is the fold map. `simplexAugmentedExact` packages exactness of the degree-zero augmentation short complex and of every consecutive positive-degree short complex. The theorem `totalSiteSimplexFreeResolution` has the node's hypotheses and conclusion, with proof postponed by `sorry`.

The node's hypotheses render as follows. The condition `m ≥ 0` is represented by `m : ℕ`, so every natural-number simplex dimension is included. A commutative coefficient ring is `[CommRing Λ]`. An ordinary module is `(M : Type v) [AddCommGroup M] [Module Λ M]`; no finiteness, flatness, freeness, nonzero, or characteristic hypothesis is added. The degree-p term is `simplexModule Λ m p M`. The face map clause is `simplexFaceLinear Λ m p M i`, using `SimplexCategory.δ i ≫ α`. The alternating differential clause is `simplexDifferential Λ m p M`. The fold augmentation clause is `simplexAugmentation Λ m M`. The exactness conclusion is `simplexAugmentedExact Λ m M`, whose first conjunct is the augmented short complex and whose second conjunct quantifies every `p : ℕ` for the consecutive differential short complex.

The module also names the postponed elementary identities used by the exactness package: `simplexDifferential_squared`, `simplexAugmentation_comp_differential_zero`, and `simplexDifferential_comp_zero`. Their data are the displayed maps; no definition contains `sorry`. The theorem docstring records the source proof: double-deletion cancellation and the vertex-zero extra-degeneracy contraction, including degree `-1`.

Dependency declarations used: the node's only statement dependency is `def-weil-pbc-simplicial-object`, recorded as Mathlib's `CategoryTheory.SimplicialObject`/`SimplexCategory` framework. No project dependency module was needed; the module imports `Mathlib.AlgebraicTopology.SimplicialObject.Basic` directly.

Edge cases checked in the source argument and statement design: `m = 0` (the prepended vertex is still available), `p = 0` (the augmentation equation is included), repeated entries in a monotone simplex, `M = 0`, torsion modules, and arbitrary coefficient characteristic. The construction uses finitely supported direct sums, so no finiteness of the indexing set is assumed.

Searches made: `msearch.py ... leanfinder "For each natural number m and module M, the augmented alternating face complex indexed by monotone maps [p] to [m] is exact"` returned only generic `ChainComplex.alternatingConst_exactAt`, Dold–Kan, and extra-degeneracy declarations, with no exact indexed direct-sum statement. `msearch.py ... loogle "CategoryTheory.SimplicialObject.Augmented.StandardSimplex.extraDegeneracy, ExtraDegeneracy.homotopyEquiv"` returned no matching declaration for this module. Grep of Mathlib `AlgebraicTopology` for `StandardSimplex|extraDegeneracy|alternatingFaceMapComplex` found generic APIs but no declaration of this explicit module complex. `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no existing declaration for this node; the only related project source is the consumer's postponed reference in `TotalSiteFreeModuleResolution.lean`.

No `STATEMENT-DISPUTED` or node fault was found.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the required review.
