## Worker report

Item: `lem-coef-simplicial-realization-cylinder`. Module:
`Sheaf.AlgebraicTopology.RealizationCylinder` at
`lean/Sheaf/AlgebraicTopology/RealizationCylinder.lean`.
The module defines the actual continuous comparison
`SSet.realizationCylinderComparison`, and states `SSet.realization_cylinder` with
one `sorry`. No proof is supplied and the definition has no postponed data or
proof fields. The helper is the very map introduced in this node, not a separate
notion: it is permitted in its owning module by the missing-canonical-maps rule,
and is listed in `lean.declarations`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Any small simplicial set: `(K : SSet.{u})`, with an explicitly bound arbitrary
  universe `u`, exactly the Mathlib notion recorded by
  `def-weil-pbc-simplicial-set`. There is no finiteness, nonemptiness, dimension,
  local finiteness, Kan condition, or additional topology on K.
- The usual quotient realization: `SSet.toTop.obj K`, written `|K|` using the
  public Mathlib `Simplicial` scope. `SingularSet.lean` constructs this as the
  left Kan extension of `SimplexCategory.toTop` along the simplicial Yoneda
  embedding. Its colimit presentation is exactly the disjoint union of the
  standard topological simplices indexed by simplices of K, modulo the stated
  operator relations, with final (quotient) topology. In particular no k-ification
  is applied to the product in the theorem.
- The topological simplex is `_root_.stdSimplex ℝ (Fin (n + 1))`; its data are
  real coordinates, all nonnegative and with sum one. This is the standard
  simplex defined in `Mathlib.AlgebraicTopology.TopologicalSimplex`.
  `SimplexCategory.toTopHomeo` identifies the realization of the representable
  simplex with this exact barycentric simplex. Thus the expression
  `toTop.map (yonedaEquiv.symm x) ((SimplexCategory.toTopHomeo ⦋n⦌).symm t)`
  is precisely the quotient point `[x,t]`. For an order-preserving alpha,
  naturality of `toTopHomeo` identifies the corresponding operator with
  `stdSimplex.map alpha`, whose coordinates are sums over the fibers of alpha.
  This uses the existing realization, not a private quotient construction.
- The standard interval simplex is `(Δ[1] : SSet.{u})`, the representable
  `SSet.stdSimplex.obj ⦋1⦌`. `K ⊗ Δ[1]` is the existing cartesian monoidal
  product of presheaves, degreewise pairs. The annotation
  `(⟨x, θ⟩ : (K ⊗ Δ[1]) _⦋n⦌)` makes the degreewise product explicit.
- The map rho is constructed, not postulated: realize
  `CartesianMonoidalCategory.fst K Δ[1]` and
  `CartesianMonoidalCategory.snd K Δ[1]`, compose the latter with
  `SimplexCategory.toTopHomeo ⦋1⦌` and
  `stdSimplexHomeomorphUnitInterval`, and pair the resulting continuous maps
  with `ContinuousMap.prodMk`. The latter homeomorphism selects the coordinate
  at vertex 1. `toContinuousMap` merely bundles an existing homeomorphism as a
  continuous map; it does not choose any new data.
- The stated representative formula is the second conjunct. `Prod.map id
  (fun s : unitInterval ↦ (s : ℝ))` keeps the first coordinate and views the
  second as a real number. Its value is asserted to be
  `([x,t], ∑ i : Fin (n + 1), if θ i = 1 then t.val i else 0)`.
  The sum is exactly the sum over the fiber of 1. The binders range over every
  dimension n, simplex x, monotone simplex θ, and barycentric coordinate t,
  including degenerate simplices and boundary coordinates. `Prod.map` only
  removes the subtype packaging to state the formula; it adds no constraint.
- Homeomorphism: the first conjunct is
  `IsHomeomorph (realizationCylinderComparison K)`. Mathlib's predicate requires
  continuity, openness and bijectivity and is equivalent to a bundled
  homeomorphism with exactly that underlying function. The target is
  `|K| × unitInterval` with its ordinary product topology; `unitInterval` is
  the subtype `[0,1]` of the reals with the usual subtype topology.
- Naturality: the third conjunct quantifies over every `(L : SSet.{u})`,
  `(f : K ⟶ L)` and `z : |K ⊗ Δ[1]|`. It says that applying the realized
  `f ▷ Δ[1]` and then rho_L agrees with rho_K followed by
  `Prod.map (toTop.map f) id`. This is exactly the naturality square.
- Zero endpoint: the fourth conjunct states, for every `z : |K|`, that the
  realization of `SSet.ι₀ (X := K)` followed by rho is `(z, 0)`.
- One endpoint: the fifth conjunct gives the corresponding formula `(z, 1)`
  for `SSet.ι₁ (X := K)`. Their definitions in `Monoidal.lean` use the
  constant-0 and constant-1 simplices, respectively, so the orientation agrees.

Dependency declarations and source inspection:

- Statement dependency `def-weil-pbc-simplicial-set` is a Mathlib leaf, so its
  `mathlib_match` is used directly. Read the full definitions/docstrings of
  `SSet` in `Mathlib.AlgebraicTopology.SimplicialSet.Basic`, `SSet.degenerate`
  and `SSet.nonDegenerate` in `.Degenerate`, `SSet.Subcomplex` in `.Subcomplex`,
  and `SSet.Finite` in `.Finite`. Only `SSet` is needed in this statement.
- `public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj` supplies the
  existing `SSet.toTop`, `SSet.stdSimplex`, `SSet.yonedaEquiv`, degreewise
  monoidal product and its projections, `SSet.ι₀`, `SSet.ι₁`,
  `SimplexCategory.toTopHomeo`, and `stdSimplexHomeomorphUnitInterval`.
  Read `SingularSet.lean`, `TopAdj.lean`, and the relevant signatures and
  definitions in `StdSimplex.lean` and `Monoidal.lean`.
- Proof dependency `lem-coef-realization-finite-limits` is imported without
  `public` from `Sheaf.AlgebraicTopology.RealizationFiniteLimits`:
  `SSet.realization_finite_limits`. Read its full signature and proof docstring;
  the proof plan uses its lift of the actual `SSet.toTop`, finite products in
  k-spaces, and compact-test topology.
- Proof dependency `lem-coef-compact-open-currying` is a Mathlib leaf:
  `ContinuousMap.curry` and `ContinuousMap.uncurry` in
  `Mathlib.Topology.CompactOpen`, imported without `public`.
  Read their signatures and docstrings at lines 430–467; only uncurrying needs
  local compactness of the interval. Neither proof import is omitted.

Source: opened Hovey's Model Categories PDF at
<https://ericmalm.net/ac/projects/symmetric-spectra/hovey--model-cats.pdf>,
printed pp. 77–78 (PDF pages 87–88), Lemma 3.1.8 and the preceding realization
construction. It supplies the product comparison in k-spaces. The ordinary
product passage and explicit endpoint calculations follow the four-step proof
already recorded in the node. The declaration docstring includes all four
steps, with compact-test currying/uncurrying and the interval orientation.
No node statement correction was needed; no new or dependency nodes are added.
No `STATEMENT-DISPUTED` issue was found.

Edge cases checked before writing:

- Empty K: source and target are both empty; all point formulas are vacuous,
  and homeomorphism still makes sense. No inhabitance binder excludes it.
- `K = Δ[0]`: gives the standard interval with 0 and 1 in the prescribed order.
- A discrete or an infinite simplicial set: no finite-index or compactness
  assumption has been imposed on K; only the interval is compact in the proof.
- `n = 0`: theta is constant; the one barycentric coordinate is 1, so the
  interval value is its selected endpoint.
- Theta constantly 0 or constantly 1 in any degree: the finite sum is 0 or
  the sum of all coordinates, respectively, hence 1 in the latter case.
- Vanishing barycentric coordinates, degenerate simplices, and simplicial
  operators are included in the formula, so quotient identifications and the
  two endpoints are not restricted to interiors or nondegenerate cells.
- The universe `u` is arbitrary, including zero; `unitInterval` is a real
  subtype, and no independent universe or forced universe equality appears.

Searches made before introducing declarations:

- `msearch.py ... leanfinder` with query
  `Geometric realization of a simplicial cylinder is naturally homeomorphic
  to the ordinary product of its realization and the unit interval, with the
  endpoint inclusions`: 8 hits, all abstract model-category or homological
  cylinders (`HomotopicalAlgebra.Precylinder.I`,
  `HomologicalComplex.cylinder.homotopyEquiv`, and related results).
  None states this geometric realization theorem.
- `msearch.py ... loogle '"SSet.toTop", "Homeomorph"'`: OK, 0 hits.
- `msearch.py ... grep 'toTop.*prod|prod.*toTop|[Rr]eali[sz]ation.*[Cc]ylinder'
  AlgebraicTopology`: OK, 0 hits. Search output is also in `searches.jsonl`.
- Direct `rg` of `WeilConjectures/` for realization and cylinder concepts:
  results concern algebraic chain-complex cylinders, Frobenius realizability,
  or adic realization, not simplicial topological cylinders.
- Direct search for the item id in `WeilConjectures/`: no hit.
- Direct `rg` of `lean/Sheaf` for cylinder realization: existing results
  concern CW descriptions, finite limits in k-spaces, or nerve homotopy
  consequences. Read `RealizationFiniteLimits.lean` and its cited
  `RealizationCWSubcomplex.lean`; neither defines this comparison or states
  this theorem. The latter already supplies simplex characteristic maps;
  their expression is used directly rather than duplicated as a new helper.
- Direct search of Mathlib, `dag/lean_names_upstream.json`, upstream
  `WeilConjectures/` and `lean/Sheaf` for `realizationCylinderComparison` and
  `realization_cylinder`: no existing declaration. The helper's ingredients
  are the existing Mathlib constructions listed above.

Validation: `scompile.py NO lem-coef-simplicial-realization-cylinder
<absolute module path>` compiled both the isolated sandbox and library module
cleanly (1.6 s and 1.8 s), with no warnings. The declaration explicitly binds all
variables and the universe, and `autoImplicit` is disabled. All lines are at
most 100 characters. Only the item's `lean` field was changed.

## Second reading by NO

I read the node statement, its source place (Hovey, *Model Categories*, Lemma 3.1.8,
printed pp. 77–78), the recorded dependency declaration for `def-weil-pbc-simplicial-set`,
and the complete `RealizationCylinder.lean` module. The item-by-item correspondence is:

- The node's arbitrary small simplicial set `K` is Lean's `(K : SSet.{u})`; `SSet` is the
  recorded Mathlib notion, with no finiteness, Kan, dimension, nonemptiness, or topology
  hypothesis.
- The node's realization `|K|` is Lean's `SSet.toTop.obj K`, written `|K|`. The module
  uses the existing quotient realization and `SimplexCategory.toTopHomeo`; it introduces
  no private realization or altered topology.
- The node's standard topological simplex and barycentric coordinates are rendered by
  `_root_.stdSimplex ℝ (Fin (n + 1))` and
  `((SimplexCategory.toTopHomeo ⦋n⦌).symm t)`. The formula's sum over
  `if θ i = 1 then t.val i else 0` is exactly the fiber sum in the node.
- The node's `Δ[1]` and degreewise product `K × Δ[1]` are `(Δ[1] : SSet.{u})` and
  `K ⊗ Δ[1]`, the existing cartesian monoidal product. The explicit pair annotation
  `(⟨x, θ⟩ : (K ⊗ Δ[1]) _⦋n⦌)` has the intended degreewise meaning.
- The canonical map `ρ_K` is the definition
  `SSet.realizationCylinderComparison K`. It is built from the realized first and
  second projections and the existing `SimplexCategory.toTopHomeo` followed by
  `stdSimplexHomeomorphUnitInterval`; no map or homeomorphism is postulated.
- The homeomorphism clause is `IsHomeomorph (realizationCylinderComparison K)` and
  therefore has the exact bijective, continuous, open-map content. Its target is the
  ordinary product `|K| × unitInterval`.
- The representative clause is the second conjunct of
  `SSet.realization_cylinder`, with all `n`, `x`, `θ`, and barycentric `t` quantified,
  and with `Prod.map id (fun s : unitInterval ↦ (s : ℝ))` only removing subtype
  packaging from the interval coordinate.
- Naturality is the third conjunct, for every `L`, every simplicial map `f : K ⟶ L`,
  and every realization point `z`; it compares realization of `f ▷ Δ[1]` with
  `Prod.map (toTop.map f) id` exactly as in the node.
- The zero and one endpoint clauses are the fourth and fifth conjuncts, using the
  existing `SSet.ι₀` and `SSet.ι₁`, and state respectively `(z, 0)` and `(z, 1)`.
  Their orientation agrees with Mathlib's constant-zero and constant-one definitions.

No hypotheses are added or dropped, and the quantifier order and all five conclusion
clauses match the node. The source's finite-product result is used with the interval
specialization; the module's proof docstring records the ordinary-product compact-test
passage and the representative calculation required by the node.

Edge cases checked: the empty simplicial set (the homeomorphism and endpoint formulas
are vacuous), `K = Δ[0]` (the comparison is the standard interval in the stated
orientation), infinite/discrete `K` (no finiteness condition is imposed), `n = 0`,
constant `θ = 0` and `θ = 1`, zero barycentric coordinates, degenerate simplices, and
simplicial operator identifications. The sum gives `0` for constant zero and `1` for
constant one; no interior or nondegeneracy restriction is present. The universe `u` is
explicit and arbitrary, including `u = 0`; the real interval is independent of `u` as
intended.

I repeated the required existing-notion searches. `msearch.py` LeanFinder for the
geometric realization cylinder found only unrelated abstract/model-category cylinders
and the standard one-simplex homeomorphism; Loogle for `SSet.toTop, stdSimplexHomeomorphUnitInterval`
returned no match; grep over Mathlib `AlgebraicTopology` found no
`realizationCylinder`/`realization_cylinder` or realization-product comparison. Direct
`rg` over the slopmaster2 `WeilConjectures`, the repository `lean/Sheaf`, and
`dag/lean_names_upstream.json` likewise found no declaration. The dependency
`def-weil-pbc-simplicial-set` is the existing Mathlib `SSet` record and is used directly;
there are no new definition or dependency modules in this delivery.

No mismatch was found, so no Lean or node repair was necessary. The module was compiled
with the mandated wrapper:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NO lem-coef-simplicial-realization-cylinder
/home/ubuntu/weil-newtargets-stage2-sandbox/NO/lem-coef-simplicial-realization-cylinder/lean/Sheaf/AlgebraicTopology/RealizationCylinder.lean`;
both sandbox and library compilation completed without errors or warnings.
