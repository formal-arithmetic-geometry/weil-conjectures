## Worker report

The module `Sheaf.LinearAlgebra.ExteriorTopDirectSum` states the canonical top-exterior-power
isomorphism and its naturality, with two theorem proofs equal to `sorry`. It introduces no
new definitions. The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- A commutative ring is `{R : Type u} [CommRing R]`; the two arbitrary modules are
  `{M : Type v} [AddCommGroup M] [Module R M]` and the analogous binders for `N`.
- Bases with `r` and `s` elements are `(r s : ℕ) (_bM : Module.Basis (Fin r) R M)` and
  `(_bN : Module.Basis (Fin s) R N)`. These give exactly finite free modules with the stated
  basis sizes; a separate `Module.Free` hypothesis would be redundant. Every basis of a
  finite set of that size can be reindexed by `Fin`, so no modules or ranks are excluded.
- The exterior powers are the submodules `⋀[R]^r M`, `⋀[R]^s N`, and
  `⋀[R]^(r + s) (M × N)` from Mathlib. The standard product of two modules is their binary
  direct sum: its two inclusions are `m ↦ (m, 0)` and `n ↦ (0, n)`. This uses the existing
  module product, not another definition of a direct sum.
- `⊗[R]` and `⊗ₜ[R]` are Mathlib's module tensor product and its pure tensors.
- The conclusion `∃! e : (⋀[R]^(r + s) (M × N)) ≃ₗ[R]
  ((⋀[R]^r M) ⊗[R] (⋀[R]^s N)), ...` has exactly the orientation of the displayed
  isomorphism in the node. The formula is stated for `e.symm`, because the node specifies
  the map in the opposite direction. For ALL `m : Fin r → M` and `n : Fin s → N`,
  `e.symm ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n))` is the wedge
  `ιMulti R (r + s) (Fin.append (fun i ↦ (m i, 0)) (fun j ↦ (0, n j)))`.
  `Fin.append` puts the `M` factors first and the `N` factors second, with coefficient +1.
  This is the alternating-map characterization, not just a formula on the chosen bases.
  Uniqueness spells out canonicity: wedges span the exterior powers and their pure tensors
  span the tensor product, so there is precisely one isomorphism with the node's formula.
- Naturality is the second declaration, `exteriorPower.topDirectSum_natural`.
  It takes arbitrary comparison modules `M' : Type v'`, `N' : Type w'` with their module
  instances and arbitrary `f : M ≃ₗ[R] M'`, `g : N ≃ₗ[R] N'`. Its `e` and `e'` are any
  isomorphisms satisfying precisely the preceding pure-wedge characterization (`he`, `he'`).
  Its equality, for every `x` in the top exterior power of the sum, is
  `e' (map (r + s) (f.toLinearMap.prodMap g.toLinearMap) x) =
  TensorProduct.map (map r f.toLinearMap) (map s g.toLinearMap) (e x)`.
  Thus the exterior map of the direct-sum isomorphism and the tensor product of the two
  exterior maps commute with the canonical isomorphisms. No bases are needed in this
  conditional compatibility theorem; the existence theorem supplies `e`, and transported
  bases supply `e'`. It asserts the compatibility of the uniquely characterized maps,
  rather than naturality of an unspecified or basis-chosen equivalence.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: its Mathlib match `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic`, says there exists an indexed `Module.Basis`.
  Its basis notion is `Module.Basis` in `Mathlib.LinearAlgebra.Basis.Defs`, which is a
  linear equivalence with finitely supported coordinate functions. We use that very notion
  for the node's stronger explicit finite-basis hypothesis, importing `Basis.Defs`.
- `def-weil-pbc-exterior-algebra`: `ExteriorAlgebra`, `ExteriorAlgebra.exteriorPower`
  in `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`. The latter is the degree-n submodule
  `LinearMap.range (ι R) ^ n`. `exteriorPower.ιMulti` in
  `Mathlib.LinearAlgebra.ExteriorPower.Basic` is the codomain restriction of the same
  alternating exterior-algebra product, so it represents precisely the products in the
  dependency. The same module's `exteriorPower.map` is induced by a module linear map.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, its pure tensor and bilinear universal map,
  and `TensorProduct.lift` in `Mathlib.LinearAlgebra.TensorProduct.Basic`. Naturality uses
  `TensorProduct.map` from `Mathlib.LinearAlgebra.TensorProduct.Map`, which sends a pure
  tensor to the tensor of the two images.
- The existing `LinearMap.prodMap` in `Mathlib.LinearAlgebra.Prod` sends `(m,n)` to
  `(f m,g n)`. `Fin.append` in `Mathlib.Data.Fin.Tuple.Basic` concatenates the two finite
  tuples, with the left tuple in the first `r` positions.

Source check: the source markdown is absent from this machine's untracked literature.
Read the original via read-only ssh on the server, lines 135–155 of
`literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/lem-sc-riemann-roch.md`.
The determinant paragraph gives the local splitting and the top-wedge/tensor
identification, with the first summand placed before the quotient summand. This agrees
with the reviewed node's free-module formulation. No correction or disputed statement.

Edge cases checked before writing:

- `r = 0`, `s = 0`, or both: `Fin 0` supplies the empty tuple and `ιMulti R 0` is the
  empty product, i.e. the unit in degree zero. The formula includes the canonical
  `R ⊗ R`, `R ⊗ ⋀^s N`, and `⋀^r M ⊗ R` identifications without a nonzero-rank restriction.
- Zero modules and the zero ring are permitted; no `Nontrivial R`, positive ranks, or
  rank uniqueness hypotheses are imposed. Over the zero ring even nonunique basis sizes
  remain valid and all modules in the conclusion are zero.
- In characteristic two, the coefficient +1 concatenation and alternation remain valid;
  neither a division by a factorial nor invertibility of 2 is assumed.
- Separate universes `u v w v' w'` cover arbitrary ring and module universe sizes,
  including comparison modules in different universes. Every binder is explicit.
- For `r = s = 1`, the formula is `(m,0) ∧ (0,n)`, in the required order.

Searches made (logged by `msearch.py` in `searches.jsonl`):

- LeanSearch: "top exterior power of direct sum of finite free modules is tensor product
  of top exterior powers". Service unavailable (HTTP Internal Server Error); no results.
- LeanFinder: same query. Eight hits include `exteriorPower.toTensorPower`,
  `ExteriorAlgebra.ιMulti_apply`, `ModuleCat.exteriorPower`, `ExteriorAlgebra.exteriorPower`,
  `exteriorPower.alternatingMapLinearEquiv_apply_ιMulti`, and exterior-power map formulas.
  None states the direct-sum top-degree isomorphism.
- Loogle: `exteriorPower, TensorProduct`. No hits, unknown identifier `exteriorPower`.
- Mathlib grep (via `msearch.py`, LinearAlgebra):
  `exterior.*direct.sum|directSum.*exterior|exteriorPower.*(sum|prod)`.
  Three hits in exterior-power spanning/basis documentation and the exterior-algebra
  collected basis; no direct-sum top-degree isomorphism.
- `rg` of the same direct-sum/exterior-power patterns and the node id in upstream
  `WeilConjectures` and in the repository's `lean/Sheaf`: two unrelated upstream
  exterior-power occurrences (purity and weights), no matching statement, no node-id hit.
- `rg` of `exterior.*[Dd]irect|exteriorTopDirectSum` in `dag/lean_names_upstream.json`:
  no candidate names. Exact searches for `existsUnique_topDirectSum` and
  `topDirectSum_natural` in Mathlib, upstream `WeilConjectures`, repository `lean/Sheaf`,
  and the upstream-name record found no collisions.

Validation: the final module passed remote single-file compilation (exit code 0,
1.6 seconds), with no errors or warnings. Both statements have only `sorry` proofs.
The required delivery dry run checks the complete package; the second reading is left
to its designated independent reader.

## Second reading by H1

I independently opened the node, its source paragraph, and
`Sheaf.LinearAlgebra.ExteriorTopDirectSum`. The node introduces a commutative ring
`R`, modules `M,N`, finite bases of cardinalities `r,s`, the exterior powers, the
binary direct sum, and the module tensor product. The first conclusion clause is a
canonical isomorphism
`⋀^(r+s)(M ⊕ N) ≃ ⋀^r M ⊗ ⋀^s N`; the displayed alternating map puts the `M`
factors first and the `N` factors second. The final clause requires naturality under
isomorphisms of both modules.

The Lean rendering matches each item: `{R} [CommRing R]`, module structures on `M`
and `N`, and `Module.Basis (Fin r)`/`Module.Basis (Fin s)` are the hypotheses;
`⋀[R]^n` and `ιMulti` are Mathlib exterior powers and wedge generators;
`M × N` is the standard binary direct-sum product model for modules; and
`⊗[R]`/`⊗ₜ[R]` are Mathlib's tensor product and pure tensor. The existential unique
isomorphism has exactly the node's orientation and formula via `e.symm`, with
`Fin.append` placing the two inclusions in the required order. The second theorem
`topDirectSum_natural` quantifies arbitrary comparison modules and linear
isomorphisms, assumes exactly the same wedge characterization for `e,e'`, and states
the commuting exterior-power/tensor-product square for every `x`. No hypothesis or
conclusion clause is missing, added, weakened, or strengthened.

Edge cases checked are `r=0`, `s=0`, both zero (empty `Fin` tuples and degree-zero
exterior powers), zero modules and the zero ring, characteristic two, and all five
explicit universes. No positivity, nontriviality, rank uniqueness, or finite-universe
assumption is present. The `r=s=1` formula gives `(m,0) ∧ (0,n)` in that order.

The existing-definition searches were repeated with LeanSearch, LeanFinder/Loogle,
Mathlib `rg`, upstream `WeilConjectures` `rg`, project `lean/Sheaf` `rg`, and
`dag/lean_names_upstream.json`. They found only exterior-power infrastructure
(`ExteriorAlgebra`, `exteriorPower`, `ιMulti`, maps, and tensor-product bases), with
no direct-sum top-degree isomorphism or matching statement. The three dependency
records (`Module.Free`, `ExteriorAlgebra.exteriorPower`, and `TensorProduct`) are the
declarations actually imported and used. No new definition or dependency module was
needed.

No mismatch was found, so no source, node, or Lean declaration was changed during
the second reading. The module compiles cleanly with `scompile.py`; both theorem
proofs remain `sorry` as required for stage 2, and all declaration docstrings name
the source and `(blueprint: lem-sc-exterior-top-direct-sum)`.
