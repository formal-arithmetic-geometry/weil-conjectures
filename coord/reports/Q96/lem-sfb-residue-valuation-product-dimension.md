## Worker report

The module `Sheaf.LinearAlgebra.ResidueValuationProductDimension` states
`Submodule.finiteDimensional_mul_and_finrank_add_sub_one_le`, with exactly one
postponed theorem and no new definitions. The node is unchanged except for `lean`.

Hypotheses and conclusions, clause by clause:

- The field k is `{k : Type u} [Field k]`; the extension K/k is
  `{K : Type v} [Field K] [Algebra k K]`. Both universes are explicitly bound and
  independent. No characteristic or algebraic-closedness assumption is imposed.
- The subring R contained in K and containing k is `(R : Subalgebra k K)`.
  Over a field this is exactly a unital subring containing the image of k:
  multiplication by a scalar is multiplication by an element already in R.
  The subtype inclusion is the canonical ring map R → K. No separate or
  potentially incompatible algebra structures on R are parameters.
- R is a DVR through `[IsDiscreteValuationRing R]`. Its domain instance is
  inherited from the subring of the field K. The class includes the local PID
  condition and a nonzero maximal ideal, exactly as in the dependency.
- K is its fraction field through `[IsFractionRing R K]`, for the canonical
  subtype inclusion R → K. Since R is a domain and K a field, this says every
  element is a quotient with numerator in R and nonzero denominator in R.
- The maximal ideal is Mathlib's `IsLocalRing.maximalIdeal R`. The canonical
  map from k to R modulo that ideal is
  `(IsLocalRing.residue R).comp (algebraMap k R)`.
  Its bijectivity is `hres`. Bijectivity of this specified ring homomorphism
  is precisely that the quotient map restricts to the stated isomorphism.
  This is not an arbitrary abstract isomorphism of fields.
- The subspaces are `(V W : Submodule k K)`, their finite dimensionality is
  `[FiniteDimensional k V] [FiniteDimensional k W]`, and their nonzeroness is
  `(hV : V ≠ ⊥) (hW : W ≠ ⊥)`.
- The dimensions r and s are written directly as `Module.finrank k V` and
  `Module.finrank k W`; naming these natural numbers separately introduces
  no additional mathematical data, so no extra dimension-equality premises
  are necessary.
- The defined subspace P is Mathlib's existing submodule product `V * W`.
  Read `Submodule.mul` and `Submodule.mul_def` in
  `Mathlib.Algebra.Algebra.Operations`: this is the k-linear span of the set
  of all v*w with v in V and w in W, exactly the node's construction.
- P is finite dimensional: the first conjunct is
  `FiniteDimensional k (V * W)`.
- Its dimension bound is the second conjunct,
  `Module.finrank k V + Module.finrank k W - 1 ≤ Module.finrank k (V * W)`.
  Subtraction is in the natural numbers, the dimension codomain of the node;
  nonzero V and W ensure r,s ≥ 1, so no truncation changes the bound.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, read its full class
  signature and preceding docstring (line 180).
- `def-pc-field-extension`: `Algebra`, Mathlib.Algebra.Algebra.Defs (line 95),
  using the dependency's exact `[Field k] [Field K] [Algebra k K]` interpretation.
- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  Mathlib.RingTheory.DiscreteValuationRing.Basic (lines 54–60).
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs (lines 73–76), the abbreviation
  for a finitely generated module.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  Mathlib.LinearAlgebra.Dimension.Finrank (lines 48–63).

Additional existing Mathlib interfaces read: `Subalgebra` and its canonical
algebra structures in Mathlib.Algebra.Algebra.Subalgebra.Basic;
`IsFractionRing` in Mathlib.RingTheory.Localization.FractionRing;
`IsLocalRing.ResidueField` and `IsLocalRing.residue` in
Mathlib.RingTheory.LocalRing.ResidueField.Defs; `Submodule.mul` and
`Submodule.mul_def` in Mathlib.Algebra.Algebra.Operations.
These existing constructions suffice, so there are no new notion nodes or
unusable dependency interfaces to repair.

Proof dependencies: `lem-sc-dvr-valuation-arithmetic` has its recorded Mathlib
match in Mathlib.RingTheory.Valuation.Basic, imported as a private proof import.
Read `AddValuation.map_mul`, `AddValuation.map_pow` and
`AddValuation.map_add_of_distinct_val` there. The definition dependencies used
in the proof are already public statement imports.
`lem-sfb-rational-residue-distinct-order-basis` currently has neither a Lean
record nor a Mathlib match; its future module cannot yet be imported. Its use
is preserved explicitly in the docstring, with the remaining argument in full.
It is only a proof prerequisite, not an object needed to type this statement.

Edge cases checked before writing: r=1, s=1 and r=s=1 give the expected bound
(the one-dimensional factor acts by multiplication by a nonzero field element).
Empty basis segments in the staircase family are omitted. Zero V or zero W is
excluded exactly by the stated nonzeroness hypotheses. No finite-dimensionality
of K over k is assumed. No characteristic restriction is added. R cannot be a
field, exactly as required by the DVR definition. The residue-field condition
is checked on the specified composite, preventing an unrelated field isomorphism
from satisfying the hypothesis. Distinct ambient universes impose no equality
on the universes of k and K. Every variable is explicit and `autoImplicit` is false.

Source reading: read local Stacks `algebra.tex`, labels
`definition-value-group` (Tag 00IE) and `lemma-properties-valuation` (Tag 00IF).
Read the current blueprint unit `sk-thm-sf-ctf-stability` and its proof under
`literature/blueprint/latest/`. The assigned node is an agent auxiliary, not
that unit's own statement. Checked Morrison's actual title and Section 2.4,
Theorem 5 on printed p.10 in
[GIT Constructions of Moduli Spaces of Stable Curves and Maps](https://arxiv.org/pdf/0810.2340):
the Clifford bound is the motivation; the product-subspace lemma is not
attributed to Morrison. The four proof steps in the node are reproduced as a
complete natural-language argument in the theorem docstring, with their DAG ids.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches for an existing theorem (2026-10-24):

- `msearch.py ... leanfinder`: "dimension of span of products of two finite
  dimensional subspaces of a field with rational discrete valuation is at least
  sum of dimensions minus one". Eight results, including
  `Submodule.finrank_add_le_finrank_add_finrank`,
  `Submodule.IsLattice.finrank_of_pi`, and `IntermediateField.rank_sup_le`;
  none is the product-span lower bound. The first compares a sum of subspaces;
  the second concerns a full lattice; the third bounds a compositum above.
- `msearch.py ... loogle 'Submodule, "finrank", "mul"'`: six results,
  including `LinearMap.finrank_le_of_isSMulRegular` and fixed-submodule
  inequalities for transvections; none gives the lower bound on product spans.
- `msearch.py ... grep 'finrank.*mul|mul.*finrank|valuation.*(basis|subspace)'
  LinearAlgebra`: 25 results about matrix ranks, field towers and related
  dimensions; no exact theorem.
- `msearch.py ... leansearch`: "The dimension of the span of products of two
  nonzero finite dimensional subspaces of a field with a rational discrete
  valuation is at least the sum of dimensions minus one". Eight results,
  including `FiniteDimensional.span_of_finite`, sum/intersection dimension
  equalities and `Submodule.prod_span`. These provide ingredients and the
  correct product operation, but not the bound.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `residue.*(product|dimension)|finrank.*mul|valuation.*subspace|rationalResidue`
  and narrowed searches for valuation/product-subspace and rational-finrank
  names found no exact theorem. The explicit item-id search in
  `lean/WeilConjectures` returned no matches.
- A name-clash search for
  `finiteDimensional_mul_and_finrank_add_sub_one_le` in Mathlib, both project
  source roots and `dag/lean_names_upstream.json` returned no matches.

Validation: `scompile.py Q96 lem-sfb-residue-valuation-product-dimension` on the
module succeeded on the server in sandbox and library modes, without errors or
non-sorry warnings. The delivery dry run rechecks the final module and node record.

## Second reading by Q96

Independent reading by the maintainer's second reader (the delivered section
was the worker's own check). Node clauses against the Lean of
`Submodule.finiteDimensional_mul_and_finrank_add_sub_one_le`:

- k a field [def-weil-field]: `{k : Type u} [Field k]`. Correct.
- K/k a field extension [def-pc-field-extension]: `{K : Type v} [Field K] [Algebra k K]`,
  the dependency's recorded `Algebra` rendering; independent universes. Correct.
- R ⊂ K a subring containing k: `(R : Subalgebra k K)`. A subalgebra over a field is a
  unital subring containing the image of k; the inclusion R → K is the subtype map. Correct.
- Fraction field K: `[IsFractionRing R K]` for the `Subalgebra.toAlgebra` structure,
  i.e. the given inclusion. Correct, no extra data.
- R a DVR [def-sc-discrete-valuation-ring]: `[IsDiscreteValuationRing R]` (domain instance
  inherited from K). Correct.
- Quotient map induces k ≅ R/m: `Function.Bijective ((IsLocalRing.residue R).comp (algebraMap k R))`,
  bijectivity of the specified composite, not an abstract isomorphism. Correct.
- V, W nonzero finite-dimensional k-subspaces [def-weil-finite-dimensional-subspace]:
  `(V W : Submodule k K) [FiniteDimensional k V] [FiniteDimensional k W] (hV : V ≠ ⊥) (hW : W ≠ ⊥)`. Correct.
- r, s dimensions [def-weil-vector-space-dimension]: `Module.finrank k V`, `Module.finrank k W`. Correct.
- P = k-span of the products: Mathlib `V * W` (`Submodule.mul_def`: span of the pointwise products). Correct.
- Conclusion: `FiniteDimensional k (V * W) ∧ finrank V + finrank W - 1 ≤ finrank (V * W)`;
  both clauses, ℕ-subtraction harmless since r, s ≥ 1. Not weaker, not stronger.

Edge cases: r = 1 or s = 1 (bound = max(r,s), true since multiplication by a nonzero
element is injective); V or W = 0 excluded as in the node; no finiteness of K/k,
characteristic or algebraic-closedness assumed; the residue hypothesis is needed
(V = W = L with [L:k] > 1 violates the bound) and is present. The statement is
true and sharp (V = W-type ⟨1,…,t^{r-1}⟩ examples).

One definition per notion: no new declarations; only Mathlib notions used. Name
`finiteDimensional_mul_and_finrank_add_sub_one_le` does not occur in Mathlib.
Records: stmt_deps are exactly the five definition nodes cited in the statement;
their records (`Field`, `Algebra`, `IsDiscreteValuationRing`, `FiniteDimensional`,
`Module.finrank`) are the declarations used. `lean.statement` is verbatim the
signature in the file. Docstrings carry the source place, `(blueprint: …)` and
the four proof steps; body is `sorry`; the proof-only dependency
lem-sfb-rational-residue-distinct-order-basis is not needed to type the statement.

Mismatches found: none in the Lean or records; this section replaces the
self-check section (H11).
