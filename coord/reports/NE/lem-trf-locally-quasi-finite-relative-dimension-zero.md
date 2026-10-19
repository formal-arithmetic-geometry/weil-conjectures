## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension` states
`AlgebraicGeometry.Scheme.Hom.isLocallyQuasiFinite_iff_topologicalKrullDimAt_fiber_eq_zero`.
It binds schemes `X` and `S` in the same universe, a morphism `f : X ⟶ S`, and the
hypothesis `[AlgebraicGeometry.LocallyOfFiniteType f]`. Its conclusion is the exact
iff in the node: `f.IsLocallyQuasiFinite` if and only if for every `x : X`, the local
Krull dimension `topologicalKrullDimAt` of the scheme-theoretic fibre at the canonical
point `f.asFiber x` equals `0`.

The Lean rendering of each clause is:

- “`f : X → S` is a morphism of schemes” is `(f : X ⟶ S)` with
  `{X S : AlgebraicGeometry.Scheme.{u}}`.
- “`f` is locally of finite type” is the typeclass hypothesis
  `[AlgebraicGeometry.LocallyOfFiniteType f]`.
- “`f` is locally quasi-finite” is the left side `f.IsLocallyQuasiFinite`, the
  Stacks-style project predicate from `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`.
- “the scheme-theoretic fibre over `f(x)` and its point lying over `x`” is the
  canonical Mathlib fibre point `f.asFiber x : f.fiber (f x)`.
- “Krull dimension at that point is zero for every `x`” is the right side
  `∀ x : X, topologicalKrullDimAt (f.asFiber x) = 0`.

The proof is postponed with `sorry` exactly as required at stage 2. Its docstring
records the source argument: affine neighbourhoods reduce to finite-type ring maps;
the affine fibre is an open neighbourhood in the scheme-theoretic fibre, and the
homeomorphisms preserve local dimension; the affine quasi-finiteness/zero-dimension
criterion gives both implications; universal quantification handles all points and
the empty source.

Dependencies used are:

- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`, declarations
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` and the fibre infrastructure
  imported there (`AlgebraicGeometry.Scheme.Hom.fiber`, `fiberHomeo`, `asFiber`).
- Mathlib `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `AlgebraicGeometry.Scheme.Hom.fiber` from `Mathlib.AlgebraicGeometry.Fiber`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`, declaration
  `topologicalKrullDimAt` (the recorded declaration for `def-kun-topological-dimension-at-point`).
- `AlgebraicGeometry.Scheme` / `AlgebraicGeometry.Scheme.Hom` for schemes and morphisms,
  supplied by the imported dependencies.

Edge cases checked: if `X` is empty, both the local quasi-finite condition and the
universal dimension condition are vacuous; for an affine line over a field the fibre
at every point has local dimension one, so the right side correctly fails; for an
open or closed immersion the fibres are zero-dimensional and the criterion agrees
with local quasi-finiteness; the canonical `asFiber` point exists for every `x`,
including non-closed and generic points. The same-universe binder does not restrict
any node case because the recorded Scheme and fibre declarations use `Scheme.{u}`.

Searches made before writing:

- `msearch.py NE ... leanfinder "locally quasi-finite iff relative fibre dimension zero"`:
  returned only `AlgebraicGeometry.LocallyQuasiFinite` constructors/recursors and
  `locallyQuasiFinite_iff`; no fibre-dimension theorem.
- `msearch.py NE ... loogle "AlgebraicGeometry.LocallyQuasiFinite, dimension zero"`:
  zero hits (the service reported unknown identifier `dimension`).
- `msearch.py NE ... leanfinder "A locally finite type scheme morphism is locally
  quasi-finite exactly when every fibre has relative dimension zero"`: related
  locally-quasi-finite and finite APIs only; no dimension characterization.
- Mathlib grep for `LocallyQuasiFinite|quasiFinite.*dimension|dimension.*quasiFinite`:
  hits in `AlgebraicGeometry/Morphisms/QuasiFinite.lean` and
  `ZariskisMainTheorem.lean`, but no equivalence with local fibre dimension.
- Project grep for `locally.*quasi|LocallyQuasi|relative.*dimension`: no declaration
  stating this equivalence.
- DAG search of all `dag/nodes` confirmed no other node carries the same statement.

No statement correction, new node, dependency repair, or `STATEMENT-DISPUTED` flag is needed.

## Second reading by NE

I reread the node, all five statement dependencies, their recorded declarations and
source docstrings, and the Stacks Tag 0397 source place. The theorem has exactly the
node's single hypothesis (locally finite type), both sides of the iff, the universal
quantifier over all `x : X`, and local dimension zero on the scheme-theoretic fibre
at the canonical point. `f.asFiber x` is precisely the point supplied by the fibre's
homeomorphism over `f(x)`, so no point or fibre clause is dropped. The empty-source
case remains included. The imported project predicate is used directly rather than
redeclared, and the recorded `topologicalKrullDimAt` declaration is used directly.
The module compiled cleanly with `scompile.py`; the only expected diagnostic is the
postponed theorem proof `sorry`.
