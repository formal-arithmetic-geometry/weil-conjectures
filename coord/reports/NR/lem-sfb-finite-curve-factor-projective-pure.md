## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteCurveFactorProjectivePure` states
`AlgebraicGeometry.finite_curve_factor_projective_pure`. Its single theorem has proof
`sorry`; there are no new definitions, auxiliary postponed theorems, new nodes, dependency
repairs, or statement corrections. The node copy changes only `lean`.

### Clause-by-clause reading

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| S, X, T, Y are k-schemes | Four explicit structure maps `pS`, `pX`, `pT`, `pY` to `Spec (.of k)` |
| Each is integral | `[IsIntegral S] [IsIntegral X] [IsIntegral T] [IsIntegral Y]` |
| Each is finite type over k | `LocallyOfFiniteType p` and `QuasiCompact p` for each of the four structure maps, exactly the conjunction recorded in def-weil-finite-type-morphism |
| f : X → S is a k-morphism | `f : X ⟶ S`, `hf : f ≫ pS = pX` |
| f is H-projective | `[IsHProjective f]` |
| S is H-projective over k | `[IsHProjective pS]` |
| Every geometric fibre of f is pure dimension one | `hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S), Scheme.IsPureDimension (pullback (C := Scheme.{u}) f s) 1` |
| q : T → S is a finite surjective k-morphism | `q`, `[IsFinite q] [Surjective q]`, and `hq : q ≫ pS = pT` |
| ν : Y → X is a finite surjective k-morphism | `ν`, `[IsFinite ν] [Surjective ν]`, and `hν : ν ≫ pX = pY` |
| g : Y → T is a dominant k-morphism | `g`, `[IsDominant g]`, and `hg : g ≫ pT = pY`; `IsDominant` is dense range of the underlying continuous map |
| q ∘ g = f ∘ ν | `hcompat : ν ≫ f = g ≫ q`; the equality is oriented for the canonical pullback lift |
| The induced h = (ν,g) is finite | `hfinite : IsFinite (pullback.lift ν g hcompat)`; this is the universal induced morphism, not an arbitrary map |
| The generic fibre over k(T) is nonempty and pure dimension one | `hgGeneric : Nonempty (pullback (C := Scheme.{u}) g T.fromSpecFunctionField) ∧ Scheme.IsPureDimension (pullback (C := Scheme.{u}) g T.fromSpecFunctionField) 1` |
| X, Y, T are H-projective over k | `IsHProjective pX ∧ IsHProjective pY ∧ IsHProjective pT` |
| g is H-projective | `IsHProjective g` |
| At every y the fibre local topological dimension is at least one | `∀ y : Y, ((1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDimAt (g.asFiber y)` |
| Every geometric fibre of g is pure dimension one | The final `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T), Scheme.IsPureDimension (pullback (C := Scheme.{u}) g t) 1` |
| No flatness or normality is assumed | There is no `Flat`, `IsNormal`, smoothness or reduced-fibre binder |

All object and field carriers use the scheme universe `u`, and every variable is explicitly
bound under `set_option autoImplicit false`. This is the standard small-scheme geometric-point
encoding used by the project. The geometric fibres quantify over all algebraically closed
field-valued points in that universe, rather than choosing a single special fibre or requiring
nonempty fibres. Morphisms are composed left-to-right in Lean.

### Recorded definitions used

- `def-weil-field`: Mathlib `Field` (`Mathlib.Algebra.Field.Defs`, re-exported by the imports).
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`, `AlgebraicGeometry.Scheme.functionFieldOfComponents`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`, `AlgebraicGeometry.Scheme.IsPureDimension`.

For `def-sc-function-field` the recorded module is imported and its documented integral-scheme
clause is used: Mathlib `Scheme.functionField`, the generic stalk, rather than the product
`Scheme.functionFieldOfComponents` intended for reducible curves. The existing canonical map
`Scheme.fromSpecFunctionField` from `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`
is `fromSpecStalk` at `genericPoint T`. Its domain is literally `Spec T.functionField`.
No replacement function field or arbitrary generic-point map is introduced.

The ordinary fibre and its distinguished point are Mathlib `Scheme.Hom.fiber` and
`Scheme.Hom.asFiber` from `Mathlib.AlgebraicGeometry.Fiber` (def-pc-scheme-fibre).
The local dimension is the recorded `topologicalKrullDimAt` from
`WeilConjectures.Mathlib.Topology.KrullDimension` (def-kun-topological-dimension-at-point):
the infimum of dimensions of open neighbourhoods, not the Krull dimension of a local ring.
Both nodes already occur among the item's proof dependencies, and their existing interfaces
are reused directly. `Surjective` and `IsDominant` are read in Mathlib
`AlgebraicGeometry/Morphisms/UnderlyingMap.lean`; they are pointwise surjectivity and dense range.

### Sources, proof imports, and edge cases

Read the full source hypotheses and conclusions of Stacks morphisms.tex
`lemma-H-projective-composition` (01WE), `lemma-finite-projective` (0B3I),
`lemma-dimension-fibre-after-base-change` (02FY), and
`lemma-openness-bounded-dimension-fibres` (02FZ), and schemes.tex
`lemma-fibre-product-after-map` (01KR). The finite-over-projective input is deliberately
used only over the affine field base. The supplied seven-step proof is carried in full,
with its dependency ids, in the theorem docstring. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read to check its scope; this helper is not the unit's own statement.

The already stated proof modules for H-projective composition, finite-over-projective,
equidimensional opens, local fibre dimension openness, fibre dimension base change,
supremum of local dimensions, fibre-image dimension bounds, and constant-local-dimension
components are imported privately. Mathlib proof dependencies are available through the
properness, Noetherian, finite-type, finite, and quasi-finite imports. The proof dependency
`lem-sfb-finite-constant-projective-graph` has no Lean record or closed upstream audit at
this reading, so it has no module to import yet; the maintainer can add its import when stated.
It is a proof prerequisite only, not a missing notion needed to type this statement.

Edge cases checked against the definitions:
- Integral schemes are nonempty by their given definition; no extra nonemptiness is imposed.
- Empty ordinary or geometric fibres remain permitted. Geometric purity is vacuous on the
  empty scheme, exactly as `Scheme.IsPureDimension` specifies. The local lower bound only
  quantifies over actual points of Y and therefore does not demand a point in an empty fibre.
- Generic-fibre nonemptiness is retained explicitly; purity alone would be vacuous if empty.
- Generic fibres are over the ordinary function field, not its algebraic closure; the
  geometric-fibre clauses separately quantify over algebraically closed fields.
- There is no restriction on the characteristic of k, no separability or perfection
  assumption, no bound on the dimensions of S or T, and no normality or flatness assumption.
- The H-projective predicate is the recorded finite-coordinate projective-space embedding
  convention, including the P^0 case; no proper-only substitute is used.
- The canonical pullback lift uses the exact commuting square; its finiteness is retained
  even though projectivity/separatedness can supply related finiteness facts in proofs.

### Searches and validation

- `msearch.py grep`: `(IsHProjective|IsPureDimension).*([Ff]inite|[Cc]urve)|([Ff]inite|[Cc]urve).*(IsHProjective|IsPureDimension)`. Result: 0 hits. No match in Mathlib.
- `msearch.py loogle`: `AlgebraicGeometry.IsHProjective, AlgebraicGeometry.IsFinite`. Result: 0 hits. The index does not know `AlgebraicGeometry.IsHProjective`; no matching statement.
- `msearch.py leanfinder`: `Finite cover of an integral projective curve family factoring through a finite base cover is projective with pure dimension one geometric fibres`. Result: 8 hits. Returned individual finiteness, properness, Proj or finite-fibre declarations; none states the combined projectivity and pure-fibre result.
- `msearch.py leansearch`: `Finite relative factor of a projective pure curve family is projective and has pure one dimensional geometric fibres`. Result: 8 hits. Returned individual finiteness, properness, Proj or finite-fibre declarations; none states the combined projectivity and pure-fibre result.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `finite_curve_factor`, `finite.*curve.*factor`, `curve.*factor.*pure`, and the node id:
  no existing declaration of this statement. Searches for `IsHProjective`,
  `IsPureDimension`, `functionFieldOfComponents`, and `topologicalKrullDimAt` identified
  the reused notions and related but distinct finite-dominant-fibre-purity statement.
- The prescribed example Sheaf compact-object module is now withdrawn; its node points to
  `WeilConjectures.CategoryTheory.CompactObject`, which was also read for current header,
  declaration/docstring and public-section conventions.
- Compiled the delivered module through `scompile.py` against the live published library:
  both sandbox and actual module checks passed without errors or non-sorry warnings.
  Explicit `C := Scheme.{u}` fixes category inference for the generic-fibre pullback.

No STATEMENT-DISPUTED flag or node fault was found. The maintainer's independent review
is the second reading under the current dispatcher instructions.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
