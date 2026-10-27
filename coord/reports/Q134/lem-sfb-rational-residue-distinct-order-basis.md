## Worker report

The delivery states `IsDiscreteValuationRing.exists_basis_strictMono_order_of_residue_bijective`
in `Sheaf.RingTheory.RationalResidueDistinctOrderBasis`. Its sole proof is `sorry`, as required
for stage 2. There are no new definitions, new nodes, dependency repairs, or statement changes.
The item node changes only in `lean`. No mathematical fault or disputed statement was found.

The source read is `literature/stacks-project/algebra.tex`, Definition `definition-value-group`
(Tag 00IE), its preceding ordered quotient-group lemma and normalization paragraph, and Lemma
`lemma-characterize-dvr` (Tag 00PD). These supply the valuation convention and DVR context.
The distinct-order basis assertion is explicitly an agent auxiliary, not a theorem of either tag.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| A field `k` | `(k : Type u) [Field k]` |
| A field extension `K/k` with its specified inclusion | `(K : Type v) [Field K] [Algebra k K]` |
| An integral-domain subring `R` of `K` | `(R : Type w) [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]`; the last assumption makes the algebra map injective, so its image is precisely an embedded copy of `R` |
| `R` contains the given copy of `k` | `[Algebra k R] [IsScalarTower k R K]`; the composite of the two algebra maps is the original map `k → K` |
| `R` is a discrete valuation ring | `[IsDiscreteValuationRing R]`, the recorded Mathlib local PID, not a field |
| Its maximal ideal `m` | `IsLocalRing.maximalIdeal R`, inside the residue-field definition and the height-one prime `IsDiscreteValuationRing.maximalIdeal R` |
| The quotient restricts to an isomorphism `k → R/m` | `hres : Function.Bijective ((IsLocalRing.residue R).comp (algebraMap k R))`; this is bijectivity of the specified ring homomorphism, equivalent to its being a ring isomorphism |
| Fraction field `K`, every element a quotient | `[IsFractionRing R K]`, localization at the nonzero elements of the domain |
| The normalized integer valuation | `-WithZero.log ((maximalIdeal R).valuation K x)` on nonzero `x`, the same canonical valuation convention as the recorded proof dependency `dvr_valuation_ring_characterization` |
| A `k`-linear subspace `U` | `(U : Submodule k K)` |
| `U` is finite-dimensional | `[FiniteDimensional k U]` |
| Its dimension is `d` | `Module.finrank k U`; `d` is substituted directly rather than introducing another parameter |
| A basis of `d` members | `∃ b : Module.Basis (Fin (Module.finrank k U)) k U, ...` |
| `nu(u_1) < ... < nu(u_d)` | `StrictMono (fun i ↦ -WithZero.log ((maximalIdeal R).valuation K (b i : K)))` |
| For `U = 0`, the empty basis | `Module.finrank k U = 0`, so the basis is indexed by empty `Fin 0`, and strict monotonicity has no pairs to test |

Representing `R` by a type and its injective fraction-field map is equivalent to the node's
subring presentation, with no extra mathematical hypothesis: any embedded `R` gives these
algebras and scalar tower, and the image of any such map recovers the embedded subring.
`IsFractionRing` supplies injectivity over a domain; no arbitrary map or embedding is assumed
in place of the fraction-field inclusion. All three universes are explicit and independent.
The ring-homomorphism bijectivity condition refers to the actual quotient restriction; an
abstract isomorphism of the residue field with `k` would not suffice and is not what was written.

The valuation is Mathlib's maximal-ideal adic valuation, with multiplicative value
`exp(-nu(x))`, followed by negative logarithm. `intValuationDef` counts the maximal-ideal
factor in a principal ideal, and `valuation` extends it to fractions. A uniformizer therefore
has additive value `1`. This is exactly the order-preserving normalized quotient valuation of
Tag 00IE. Basis elements are nonzero; `WithZero.log 0 = 0` is consequently never used in the
conclusion. The canonical valuation and logarithm are existing Mathlib constructions, not
additional notions requiring a new definition node.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, with its `algebraMap`.
- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank`, exposed through the finite-dimensional imports.
- Proof dependency `lem-sc-dvr-valuation-ring-characterization`:
  `IsDiscreteValuationRing.dvr_valuation_ring_characterization`,
  `Sheaf.RingTheory.DVRValuationRingCharacterization` (plain proof import).
- Proof dependency `lem-sc-dvr-valuation-arithmetic`: `AddValuation.map_mul`,
  `AddValuation.map_pow`, `AddValuation.map_add_of_distinct_val`,
  `Mathlib.RingTheory.Valuation.Basic`, exposed by the valuation import. The multiplicative
  form supplies the same arithmetic for `-WithZero.log` on nonzero elements.
- Proof dependency `lem-sc-dvr-nonnegative-valuation-in-ring`:
  `IsDiscreteValuationRing.exists_lift_of_le_one`,
  `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`.
- Proof dependency `lem-weil-pbc-idempotent-charpoly-rank-nullity`:
  `LinearMap.finrank_range_add_finrank_ker`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` (plain proof import).

The signatures and docstrings of the five statement dependencies and the four additional proof
dependencies were read. The module also uses the existing `IsLocalRing.ResidueField` and
`IsLocalRing.residue` (`Mathlib.RingTheory.LocalRing.ResidueField.Defs`),
`IsDiscreteValuationRing.maximalIdeal`, `IsDedekindDomain.HeightOneSpectrum.valuation`,
`WithZero.log`, `IsFractionRing`, `Module.Basis`, and `StrictMono`; their definitions were read.

Edge cases checked before writing:

- `U = 0`: empty `Fin 0` basis, no nonzero-vector or positivity assumption.
- Dimension one: any nonzero generator is a basis and `StrictMono` on `Fin 1` is vacuous.
- Elements of negative order: allowed because the target of the order function is `ℤ`, not `ℕ`;
  e.g. spans of negative powers of a uniformizer are included.
- Arbitrary characteristic and arbitrary scalar field: no characteristic, cardinality,
  completeness, or algebraic-closedness condition appears.
- `R` a field is already excluded by the recorded DVR definition; no duplicate hypothesis.
- Residue field genuinely larger than `k`: intentionally excluded by the node. This condition
  matters, since a two-dimensional scalar subspace of a larger constant residue field has only
  order-zero nonzero elements and cannot have distinct orders.
- Basis values cannot be zero in `K`, so the logarithm's junk value at zero adds no case.

Searches made with the prescribed `msearch.py` wrapper (2026-10-24):

- LeanFinder, query: “A finite dimensional vector subspace of a discretely valued field with
  residue field equal to the scalar field has a basis with strictly increasing valuations”.
  Eight hits: `Field.Emb.Cardinal.wellOrderedBasis`, `Module.Basis.ofZLatticeBasis`,
  `IsDiscreteValuationRing.isRankOneDiscrete`, `IsLocalRing.basisQuotient`,
  `Module.Basis.extendOfIsLattice`, `Submodule.basisOfPid`, `Submodule.basisOfPidOfLE`,
  `Submodule.smithNormalFormTopBasis`. None states a scalar basis with distinct orders.
- Loogle, query `Valuation, Module.Basis`: zero hits.
- Mathlib grep, query `valuation.*(basis|linearIndependent|finrank)|distinct.*valuat|valuat.*distinct`
  in `RingTheory`: two hits, both the distinct-value addition identity in
  `Mathlib/RingTheory/Valuation/Basic.lean`, not this basis assertion.
- LeanSearch, query: “A finite dimensional subspace of a discretely valued field has a basis
  with pairwise distinct valuations if the residue field is the ground field”. Eight hits on
  finite-dimensional basis indices, valuation topology and finite residue fields; no match.
- Project `rg` in `lean/WeilConjectures` and `lean/Sheaf` for distinct valuations, valuation
  bases, and rational residue fields: incidental evaluation/basis and residue-field results,
  with no declaration of this assertion. The exact node-id search in `lean/WeilConjectures`
  returned no hits. Searching both roots and Mathlib for the proposed full declaration's last
  component and module name returned no hits. The upstream declaration-name index was checked
  for the same valuation/basis concepts and did not supply this statement.

Complete natural-language proof, following the unchanged node:

Induct strongly on `d = dim_k U`. If `d = 0`, `U = 0` and the empty basis works. For `d > 0`,
choose a finite spanning family `e_1,...,e_r`. Write `e_i = a_i/b_i` in the fraction field,
where each `b_i` is nonzero in `R`, and set `q = product b_i`. This product is nonzero in
the domain. Each `q e_i` belongs to `R`, hence so does `q x` for every `x` in `U`, because
all scalars from `k` belong to `R`. For nonzero `x`, nonnegativity on `R` and multiplicativity
give `nu(x) >= -nu(q)`. The set of orders of nonzero vectors of `U` is nonempty and bounded
below in `ℤ`. Translate by an integer lower bound and use the least-element principle in
`ℕ` to choose a nonzero `u` of minimum order `n`.

For every nonzero `x` in `U`, `nu(x/u) >= 0`, so `x/u` belongs to `R` by the nonnegative-value
criterion; zero belongs as well. Let `rho : R → R/m` be reduction and `iota : k ≃ R/m` the
specified restriction, a ring isomorphism by the residue hypothesis. Define
`lambda(x) = iota⁻¹(rho(x/u))`. Division by fixed `u` is additive. For a scalar `c`,
`rho(c*x/u) = iota(c)*rho(x/u)`, proving scalar linearity after applying `iota⁻¹`.
Also `lambda(u) = 1`.

Put `W = ker lambda`, viewed also as a subspace of `K` through `U`. A nonzero `w` in `W`
has `w/u` in the maximal ideal, hence is not a unit: an ideal containing a unit contains
one. Its valuation is nonnegative by minimality of `n`, and nonzero because the kernel of
the quotient map `K× → K×/R×` consists exactly of the units of `R`. Thus its valuation is
positive, so `nu(w) > n`.

The vectors `f_i = e_i - lambda(e_i)*u` belong to `W`. If `w = sum c_i e_i` lies in `W`,
linearity gives `sum c_i lambda(e_i) = lambda(w) = 0`, so `w = sum c_i f_i`. Therefore `W`
is finite-dimensional. Since `lambda(c*u) = c`, its image is all of `k`, which has the
singleton basis `(1)` and dimension one. Rank-nullity gives `1 + dim_k W = d`, hence
`dim_k W = d-1 < d`.

Apply strong induction to `W` to obtain a basis `w_1,...,w_(d-1)` of strictly increasing
orders. All these orders exceed `n`, so prepend `u`. Every `x` decomposes as
`lambda(x)*u + (x-lambda(x)*u)`, whose second term lies in `W`, proving spanning. In a
relation `c*u + sum c_i w_i = 0`, applying `lambda` forces `c = 0`, then independence in
`W` forces every `c_i = 0`. This is the required basis of `d` vectors. When `d = 1`, the
tail basis is empty and the same argument applies.

Validation: the prescribed `scompile.py Q134 lem-sfb-rational-residue-distinct-order-basis`
compiled this file both as the sandbox module and at its final library module name, with no
errors or warnings (6.7 seconds and 2.1 seconds respectively). All binders and universe levels
are explicit, and all Lean lines have length at most 100. Delivery dry-run results are recorded
by the delivery wrapper. The maintainer performs the independent review under the direct-worker
workflow; no independent worker reading is claimed here.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
