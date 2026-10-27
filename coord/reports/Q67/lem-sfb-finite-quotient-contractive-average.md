## Worker report

Item: `lem-sfb-finite-quotient-contractive-average`, group Q67, stage 2.
The module `Sheaf.Analysis.FiniteQuotientContractiveAverage` states
`ContinuousMap.exists_finiteQuotientContractiveAverage`, with exactly one `sorry`.
It states existence of the precisely specified subspace and its averaging linear map.
There are no new definitions, helper theorems, new nodes, dependency repairs, or statement changes.
The source node and all its fields except `lean` are preserved.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
That paragraph supplies the scalar open-direct-image context, not this finite-sum lemma;
the node explicitly describes its assertion as an agent-formulated auxiliary with an exact
literature reference WANTED. The module preserves this qualification. Its docstring transcribes
all six accepted DAG proof steps, including the fiber bijections and denominator argument.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| A prime ell | `(l : ℕ) [Fact l.Prime]` |
| Nonarchimedean normed field B | `(B : Type v) [NormedField B]` and `_hB : IsNonarchimedean (norm : B → ℝ)` |
| B contains Q_ell isometrically | `[NormedAlgebra (Padic l) B]`; for normed fields `norm_algebraMap'` and `algebraMap_isometry` give the isometry, and a unital field map is injective |
| Compact Hausdorff topological group K | `(K : Type u) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]` |
| Open normal subgroup basis at the identity | `_h_basis` asks that every open W containing 1 contain an `OpenNormalSubgroup K` |
| Every finite continuous quotient has order prime to ell | `_h_order : ∀ U : OpenNormalSubgroup K, Nat.Coprime (Nat.card (K ⧸ U.toSubgroup)) l`; these quotients are finite by compactness, and conversely every finite continuous discrete quotient is the quotient by its open normal kernel, up to the canonical isomorphism |
| C(K,B), with supremum norm | Mathlib `C(K, B)` with the norm from `Mathlib.Topology.ContinuousMap.Compact` |
| Q_U and its projection | `K ⧸ U.toSubgroup`, `QuotientGroup.mk` |
| Q_U finite and nonempty | First conjunct `∀ U, Finite (K ⧸ U.toSubgroup) ∧ Nonempty (K ⧸ U.toSubgroup)` |
| D consists exactly of functions factoring through one Q_U | `∃ D : Submodule B C(K, B)`, with `∀ f, f ∈ D ↔ ∃ U g, ∀ k, f k = g (QuotientGroup.mk k)` |
| D is a B-linear subspace | The `Submodule B C(K, B)` type, whose carrier is fixed by the preceding iff |
| Contains every constant | `∀ b : B, ContinuousMap.const K b ∈ D` |
| Well-defined B-linear map A on D | `∃ A : D →ₗ[B] B`; it is a map of actual functions, not of quotient presentations |
| Finite average for EVERY presentation | `∀ (f : D) U g, (∀ k, (f : C(K,B)) k = g (QuotientGroup.mk k)) → A f = (Nat.card (K ⧸ U.toSubgroup) : B)⁻¹ * ∑ᶠ q, g q` |
| Refinement for V contained in U and any g | The next conjunct universally binds `U V`, `hVU : V ≤ U`, and `g`; `QuotientGroup.map V.toSubgroup U.toSubgroup (MonoidHom.id K) hVU` is the canonical map rho, and its two displayed averages are equated |
| Absolute value of A(f) at most the supremum norm | `∀ f : D, ‖A f‖ ≤ ‖(f : C(K, B))‖` |
| A(1) = 1 | `∀ f : D, (f : C(K, B)) = 1 → A f = 1`; constants membership supplies the unit in D, and subtype equality identifies any such f with that unit |
| Both translations preserve D and its average | For each `a : K` and `f : D`, witnesses `fL fR : D` satisfy the pointwise identities `fL h = f (a * h)` and `fR h = f (h * a)` and `A fL = A f ∧ A fR = A f` |
| Completeness not assumed | No `CompleteSpace B` or any equivalent hypothesis |
| Size convention | Explicit independent `universe u v` and `K : Type u`, `B : Type v`; no smallness or equality restriction |

The existential translated functions are uniquely specified by their pointwise identities;
they are the actual translations, with no arbitrary translation map supplied as a hypothesis.
Likewise the membership iff fixes D as an actual subset, so existentially bundling its submodule
structure changes no data. Every finite-quotient formula is simultaneous for the same A.
`∑ᶠ` is Mathlib's `finsum`: on the finite types asserted in the first conjunct it is the
ordinary finite sum (including zero values), avoiding auxiliary choices of `Fintype` instances.

Dependency declarations read and used:

- `def-weil-l-adic-numbers` is a Mathlib leaf, recorded by `mathlib_match`, not a missing
  Lean record. Its `Padic` declaration and docstring were read in
  `Mathlib/NumberTheory/Padics/PadicNumbers.lean:529–536`, and `Padic.valuation` at
  1039–1050. The module imports `Mathlib.NumberTheory.Padics.PadicNumbers` and uses
  `Padic l` in its normed-algebra hypothesis. Also read `Padic.norm_natCast_eq_one_iff`
  at 956–958 for the denominator step of the proof plan.
- `def-weil-size-convention` has an explicit `convention: true` record with null declaration
  and module: universe polymorphism is its instructed rendering. No dummy import or
  derived-category object is substituted for this metatheoretic convention.
- Existing notions read: `OpenNormalSubgroup` at `Mathlib.Topology.Algebra.OpenSubgroup:368`,
  `QuotientGroup.map` at `Mathlib.GroupTheory.QuotientGroup.Defs:308`,
  `NormedAlgebra` and `norm_algebraMap'` at `Mathlib.Analysis.Normed.Module.Basic:267,293`,
  `IsNonarchimedean` at `Mathlib.Algebra.Order.Ring.Basic:94`, and `finsum` at
  `Mathlib.Algebra.BigOperators.Finprod:103`. No private copies are introduced.

Edge cases checked mathematically before writing:

- K is the trivial group or U = K: the quotient has one element and the formula is evaluation.
- U = V: the refinement map is the identity; nested subgroups and arbitrary intersections
  also have the required common quotient.
- f = 0, constant f, and f = 1: the sum, contraction, constants, and normalization agree.
- Nonabelian finite quotients: left and right permutations are separate and do not require
  commutativity; the statement uses both multiplication orders.
- No empty quotient is possible, since K has an identity. Nonempty quotients are asserted,
  rather than assuming a nonempty indexing type independently.
- No norm completeness, finite dimensionality, metrizability, or countability is required.
- The coprimality hypothesis is essential: a delta function on a quotient of order divisible
  by l would have averaged norm greater than one. This case is excluded precisely by the node.
- The coefficient and group universes are independent; no quotient or function space is
  forced into a smaller universe.

Searches actually made (the wrapper recorded these in `searches.jsonl`):

- `msearch.py ... leansearch "Finite quotient averages of nonarchimedean valued continuous functions on a profinite group are compatible and contractive"`: 8 hits, principally `ProfiniteGrp.toFiniteQuotientFunctor` and its limit comparisons; none state this assertion.
- `msearch.py ... leanfinder "Normalized averages on finite quotients of a compact group give a linear contraction invariant under left and right translations"`: 8 hits, Haar constructions and invariant real integrals; no matching coefficient field or finite quotient contraction.
- `msearch.py ... loogle '"averageMap"'`: 4 hits, including `Representation.averageMap` and its projection/invariance lemmas. Read `Mathlib.RepresentationTheory.Invariants:123–147`; these concern a fixed finite group acting on a module, not compatible averages on quotient-function subspaces or the ultrametric bound.
- `msearch.py ... grep 'averageMap|norm_sum_le|OpenNormalSubgroup' RepresentationTheory`: 7 hits, all finite-representation averaging or its character applications; no full match.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for `OpenNormalSubgroup`, `IsNonarchimedean`, `NormedAlgebra.*Padic`, `averageMap`, contractive averaging, and the proposed declaration name: no exact match. The item id search in `lean/WeilConjectures` had no hit.
- Read `ContinuousMap.openNormalQuotientFunctions_dense` in
  `Sheaf.Topology.OpenNormalQuotientFunctionsDense`: the same factorization condition is
  written inline, with no pre-existing definition D to duplicate, and that theorem asserts
  density rather than averaging. Also inspected `Padic.primeToEll_linear_image_finite`;
  its open-normal-quotient coprimality hypothesis is the same standard encoding used here.
- The other nearby hit, `Sheaf.Analysis.ScalarCochainAveragingPrimitives`, cites this item
  in its proof plan and is a downstream cochain statement, not an existing match.

Validation: the prescribed `scompile.py Q67 lem-sfb-finite-quotient-contractive-average`
compiled both the sandbox and final module path successfully, with no errors or warnings.
The Lean file has no line over 100 characters and sets `autoImplicit false`.

No statement dispute or fault was found. The source's WANTED reference remains explicit.

## Second reading by Q67

This is a separate in-session rereading of the node and the completed module by the same
worker, not a claimed independent agent review: the dispatcher explicitly prohibits
starting other agents, and the maintainer supplies the independent delivery review.

Rechecked every row of the correspondence above against the finished theorem. In particular,
`NormedAlgebra (Padic l) B` is an isometric embedding of fields without completeness;
`_h_order` ranges over all open normal subgroups, not just a selected cofinal chain;
the carrier iff is two-way, so the existential submodule cannot be smaller than D;
the constants clause covers every b, not merely the unit; the formula covers every
presentation, not a chosen witness; refinement uses the canonical group quotient map;
and contraction uses the norm of the underlying continuous function. The unit clause
is nonvacuous because the constant-one function belongs to D. The final pointwise
identities specify both translations uniquely, and both witnesses lie in D before their
averages are compared. The first conjunct states finiteness and nonemptiness explicitly,
which also explains the use of `finsum`. Checked the sole theorem's proof is exactly
`sorry`, its six-step docstring covers the accepted proof, and only `lean` changes in the node.
No mismatch was found and no correction was made during this reading.
