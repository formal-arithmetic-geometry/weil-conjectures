## Worker report

The sandbox carries `Sheaf.AlgebraicTopology.MarkedHomotopyPrecomposition.lean`.
It defines `SSet.Marked.Over.mapFlatVertex` with actual data (the constant
parameter embedding of an over-base map) and states
`SSet.Marked.Over.marked_homotopy_precomposition` with the single postponed proof
required by this statement node.  The module is the exact project declaration
already recorded for this node; its delivery metadata is updated to Q145.

The hypotheses and conclusions are rendered as follows.  `S : SSet.{u}` is the
fixed base and `U V W : SSet.Marked.Over S` are marked objects over the maximally
marked base.  `h₀ h₁ : U ⟶ V` are the endpoint over-maps.  The map `H` has source
`productLeft U (flat Δ[1])`, and `endpoints` states for every `i : Fin 2`, every
simplex degree and every source simplex that its restriction at the constant
interval vertex is `h₀` for `i = 0` and `h₁` otherwise.  The theorem gives an
over-map `Φ : mapFlat V W ⊗ Δ[1] ⟶ mapFlat U W`.

The first conjunct is the degreewise formula: for every parameter degree `n`,
source degree `m`, `a : (mapFlat V W).obj n`, interval simplex `τ`, and pair
`(x,v)`, the value of `Φ` is
`a (H (x, (yonedaEquiv.symm τ).app m v), v)`.  This retains every parameter
simplex.  The second conjunct gives both endpoint maps as
`productMapLeft (if i = 0 then h₀ else h₁) (flat Δ^n) ≫ a`.  The third conjunct
uses `mapFlatVertex a` and the Yoneda vertex for the identity interval to state
that the component at a vertex `a : V ⟶ W` is the composite `H ≫ a`.  The final
conjunct assumes that `H` sends every marked source edge paired with every
interval edge to a marked edge of `V`; under this sharp-marking hypothesis it
produces `b : (mapSharp U W) _⦋1⦌` whose underlying map is that component.  No
fibrancy or invertibility assumption is added, and all quantifiers include
degree zero and degenerate parameters.

The dependency declarations used are:

- `SSet.Enhanced.coneCategory` and the surrounding degreewise simplicial
  product/internal-functor declarations from
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` (node
  `def-cbc-enhanced-diagrams-cones`);
- `SSet.Marked.flat`, `sharp`, `product`, `productMap`, `flatSimplex`,
  `sharpSimplex`, `mapFlat`, and the marked-map definitions from
  `Sheaf.AlgebraicTopology.MarkedPointCartesianModel` (node
  `lem-coef-marked-point-cartesian-model`);
- `SSet.Marked.Over`, `productLeft`, `mapFlat`, `mapSharp`, and
  `productMapLeft` from `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`
  (node `lem-coef-marked-relative-cartesian-model`).

The edge cases checked are `k = 0`/degree zero, empty `U` or `W`, constant `H`,
degenerate interval parameters, and a non-sharp `H`: the sharp conclusion is
conditional and is therefore not asserted in the last case.  The endpoint
formula remains meaningful when the two endpoint maps coincide, and no
nonemptiness or fibrancy condition is hidden in the binders.

Searches made before packaging included:

- `msearch.py ... leanfinder "marked simplicial homotopy relative flat mapping
  precomposition"`: only ordinary relative-morphism homotopy precomposition
  (`SSet.RelativeMorphism.Homotopy.precomp`) was returned, which lacks marked
  products, the fixed base, and the sharp-component clause;
- `msearch.py ... loogle "SSet Marked Over mapFlat mapSharp precomposition"`:
  no usable exact hit (the query parser also reported that `SSet` was treated
  as a non-function);
- `msearch.py ... grep "marked_homotopy_precomposition|mapFlatVertex"
  AlgebraicTopology`: no Mathlib hit;
- `rg` over `WeilConjectures/` and project `lean/Sheaf/`: only this recorded
  project module was found; no upstream or Mathlib duplicate exists;
- `grep -rl '"lem-cbc-marked-homotopy-precomposition"' dag/nodes`: the item
  itself and its reviewed parent `lem-cbc-marked-mapping-simplex-descent` are
  the only DAG references.

No new definition node, dependency module, statement correction, or
`STATEMENT-DISPUTED` issue is needed.  `scompile.py` compiles the module and
its temporary sandbox import with no errors or warnings; the expected warning
for the theorem's `sorry` is suppressed by the module option.

## Second reading by Q145

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
