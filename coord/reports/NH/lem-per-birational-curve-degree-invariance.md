## Worker report

The module `Sheaf.AlgebraicGeometry.BirationalCurveDegreeInvariance` states
`AlgebraicGeometry.Scheme.Modules.degree_tensorPullback_of_birational_curve`,
with exactly one postponed theorem proof (`sorry`) and no new definitions.
The node statement and its dependency lists are unchanged.

Hypotheses and conclusion, clause by clause:

- A field k: `(k : Type u) [Field k]`; no characteristic or algebraic-closedness condition.
- Schemes X and X': `{X X' : Scheme.{u}}`, with an arbitrary explicitly bound universe u.
- Schemes over that field: `[X.Over (Spec (.of k))]` and
  `[X'.Over (Spec (.of k))]`. These specify the scalar structures used in both degrees.
- Integrality: `[IsIntegral X] [IsIntegral X']`, the recorded Mathlib predicate,
  including nonemptiness and reducedness, without a normality hypothesis.
- Proper over k: `[IsProper (X ↘ Spec (.of k))]` and
  `[IsProper (X' ↘ Spec (.of k))]`.
- Each topological Krull dimension equals one: the binders
  `hdimX : topologicalKrullDim X = 1` and `hdimX' : topologicalKrullDim X' = 1`.
- A k-morphism f: `(f : X' ⟶ X) [f.IsOver (Spec (.of k))]`.
- The map induces an isomorphism between dense open subschemes: `hbirational`
  existentially quantifies `U' : X'.Opens`, `U : X.Opens`, and
  `e : U'.toScheme ≅ U.toScheme`. `Dense (U' : Set X')` and
  `Dense (U : Set X)` express both density conditions. The equation
  `U'.ι ≫ f = e.hom ≫ U.ι` says this is the restriction of the given f,
  rather than an unrelated isomorphism of opens. This equation also makes e a k-map.
- Every invertible O_X-module: `(L : X.Modules) [L.IsInvertible]`.
- The pullback is the existing explicit sheaf tensor construction
  `(tensorPullback f).obj L`.
- Equality of degrees over the same k:
  `((tensorPullback f).obj L).degree k = L.degree k`.
  The upstream definition is literally
  `M.eulerChar k - Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf)`;
  `eulerChar` is the alternating finsum of cohomological k-dimensions. Properness
  and invertibility ensure the intended coherent, eventually vanishing situation.
- No smoothness is assumed on either curve, and k is an arbitrary field.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, local triviality at every point.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the recorded
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`, and its
  publicly imported upstream `tensorPullback` from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`. I read the latter's live
  source using `scompile.py --source`; its objects really are the sheafified
  extension of scalars of the abelian inverse image. The normalized adjunction
  is not needed in the signature, which only uses its underlying pullback functor.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`:
  `AlgebraicGeometry.Scheme.Modules.degree`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar`.

All recorded proof-dependency modules are imported without `public`; the relevant
Mathlib proof leaves are available through Properties, Proper, Finite, FunctionField,
Noetherian, and KrullDimension. The nine-step proof docstring follows the node:
finiteness, coherent defect, injection at affine charts, zero-dimensional support,
ordinary rank-one projection formula, tensor exactness, affine cohomology comparison,
Euler additivity, and the degree definition. No independent helper notion or
unrecorded postponed theorem was introduced.

Source check: read `literature/stacks-project/varieties.tex`,
`lemma-degree-birational-pullback` (Tag 0AYU), including its proof. The node is its
rank-one specialization for integral proper schemes of dimension exactly one.
The source allows more general curves and vector bundles; the delivered signature
keeps precisely the narrower statement already specified by this node.

Edge cases checked before writing:

- The identity map permits both opens to be the whole scheme and e the identity.
- L = O_X has degree zero; no equality of the two structure-sheaf Euler
  characteristics is asserted, since it can fail for normalization of a singular curve.
- Nodal or cuspidal normalization is allowed: neither source nor target is assumed smooth.
- Non-algebraically-closed and positive-characteristic fields are allowed; degrees
  use k-dimensions, so residue-field contributions are retained.
- Empty schemes and dimension-zero schemes are excluded by the original integrality
  and dimension-one conditions, not by an added restriction. Dense opens cannot be
  empty because the ambient integral schemes are nonempty.
- The equation on open immersions rules out an arbitrary constant or higher-degree f
  accompanied only by an unrelated open isomorphism.

Searches for an existing statement (via the prescribed `msearch.py NH <item>`):

- `leanfinder`: "A birational morphism between proper integral curves preserves the
  Euler characteristic degree of pullbacks of line bundles". Eight hits, including
  IsDominant.respectsIso, IsProper.instRespectsIsoScheme, integral base-change and
  Weierstrass base-change declarations; no degree-invariance theorem.
- `loogle`: `"degree", "birational"`. Zero hits.
- `grep`: `degree.*birational|birational.*degree|degree.*pullback`, restricted to
  Mathlib AlgebraicGeometry. Zero hits.
- `leansearch`: "Birational pullback preserves the degree of an invertible sheaf on
  a proper integral curve". Eight hits on module pullback, isomorphism comparisons,
  and polynomial normalization; no match.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for degree/birational
  and degree/pullback patterns. Upstream `Modules.degree_pullback` and
  `Modules.degree_pullback_of_isPullback` concern field base change, not arbitrary
  birational morphisms. The project has no theorem with the desired statement.
- Search for the exact item id in upstream `WeilConjectures` returned no match.
- The candidate declaration name does not occur in the read-only upstream or project
  sources. No existing theorem can be recorded instead.

Validation: `scompile.py NH lem-per-birational-curve-degree-invariance
lean/Sheaf/AlgebraicGeometry/BirationalCurveDegreeInvariance.lean` passed both
sandbox and library checks (2.2 seconds each), without errors or unexpected warnings.
Every variable and universe is explicit, with autoImplicit and relaxedAutoImplicit disabled.
No statement faults or STATEMENT-DISPUTED concerns were found.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
