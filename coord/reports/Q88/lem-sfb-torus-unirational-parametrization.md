## Worker report

The module `Sheaf.AlgebraicGeometry.TorusUnirationalParametrization` states
`AlgebraicGeometry.torus_unirational_parametrization`, with its proof left as
`sorry`. It introduces no definitions. The item node changes only in `lean`.

Source read: Milne, Algebraic Groups (2017), printed pp.250--251, Definition
12.59, Propositions 12.60, 12.63 and 12.64, directly from the supplied PDF using
pdftotext. Proposition 12.64 says every torus is unirational; Definition 12.59
identifies this with a parametrization on an open of affine space. The node's
weaker dense-image form is stated exactly. The proof docstring contains all
three accepted proof steps: quotient of an induced torus, determinant-open
coordinates for its unit functor, and composition giving a dense image.

Clause-by-clause correspondence:

- Any field k: `{k : Type u} [Field k]`, with no infinitude, perfection,
  characteristic or algebraic-closedness hypothesis.
- A k-group scheme T: `(T : Grp (Over (Spec (.of k))))`; `T.X` is the underlying
  object over Spec k, `T.X.left` its scheme and `T.X.hom` its structure map.
- T becomes a finite power of G_m over the algebraic closure:
  `(hT : MultiplicativeType.IsTorus T)`, using exactly the dependency's definition.
  Its existential rank is natural and includes zero.
- An integer n >= 0: `∃ (n : ℕ)`, which includes n = 0.
- An open subscheme U of affine n-space:
  `(U : (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))).Opens)` and `U.toScheme`.
  The standard inclusion is `U.ι`; Mathlib makes this an open immersion. It is
  not necessary to add a second, redundant open-immersion conjunct.
- Nonempty U: `Nonempty U.toScheme`, referring to scheme points.
- A k-morphism q: `∃ q : U.toScheme ⟶ T.X.left` with the equality
  `q ≫ T.X.hom = U.ι ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k))`.
  This is precisely the compatibility with the structure morphisms, not a
  group-homomorphism condition.
- Zariski dense image: `IsDominant q`, whose defining field is `DenseRange q`.
  By the topological definition, every nonempty open of T has nonempty inverse
  image. This is density of scheme points, without a rational-point assertion.
- Affine space is Spec k[x_1,...,x_n]: the recorded Mathlib `AffineSpace`
  definition is used. Its `AffineSpace.SpecIso` identifies it with the spectrum
  of `MvPolynomial (ULift (Fin n)) k`, and `SpecIso_inv_over` identifies the
  projection with the constants inclusion. This is a description of the same
  object, not an additional theorem clause to be conjoined.

Dependency declarations and source signatures read:

- `Mathlib.Algebra.Field.Defs`: `Field`, for def-weil-field.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `AlgebraicGeometry.MultiplicativeType.IsTorus`, together with `baseChange` and
  `splitTorus`. The entire module and docstrings were read. Rank zero is the
  tensor unit; the algebraic closure and group-scheme isomorphism are retained.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and
  `CategoryTheory.Grp`, for def-sc-group-scheme. The group-object data include
  the unit, multiplication, inverse and their diagrams; bundling adds no
  mathematical hypothesis.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme` and
  `Scheme.Opens.ι`, including its `IsOpenImmersion` instance.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace`,
  `AffineSpace.over`, `AffineSpace.SpecIso`, `AffineSpace.SpecIso_inv_over`;
  these implement def-sbc-affine-space.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`,
  for def-weil-affine-spectrum.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.IsDominant`, whose docstring and full signature were read.

The group, field, spectrum and open-immersion APIs are publicly available
through the imported statement dependencies. Both proof-dependency nodes,
lem-sfb-torus-induced-quotient and lem-sfb-finite-algebra-units-affine-chart,
have no Lean records in the read repository; there are therefore no available
proof-dependency modules to import. They are named in the proof docstring.

Edge cases checked: The trivial torus is allowed by `IsTorus` at rank zero.
For it n = 0 and the whole affine zero-space give the expected constant
parametrization; the supplied proof can alternatively use a redundant G_m
factor. The empty open cannot witness the result because of `Nonempty`.
Finite fields and imperfect fields satisfy the exact same binders. A split
positive-rank torus has its usual principal-open embedding. The coordinate
type `ULift.{u} (Fin n)` lies in the same universe as k, including n = 0,
so no coordinate-universe restriction or extra rank assumption is imposed.

Searches actually run:

- msearch leanfinder, `dominant morphism nonempty open affine space torus scheme`:
  returned affine-space surjectivity, `IsDominant`, `Scheme.Hom.denseRange`,
  affine-space structure and the canonical map to Spec of global sections;
  none states the torus parametrization.
- msearch loogle, `IsDominant, Scheme.Hom, AffineSpace`: zero hits, with the
  service reporting unknown identifier `IsDominant`; this is not evidence of
  absence and the local source was inspected instead.
- msearch leansearch, `Every algebraic torus over any field is unirational`:
  returned analytic `UnitAddTorus`, formally unramified and geometrically
  reduced algebra results, and unrelated field results; no match.
- msearch grep, `IsDominant|denseRange|Dense` in AlgebraicGeometry: returned
  density and site infrastructure; the local exact `IsDominant` definition
  was read in UnderlyingMap.lean.
- msearch grep, `unirational|Unirational|IsTorus` in AlgebraicGeometry: zero hits.
- rg over `lean/WeilConjectures` and `lean/Sheaf`,
  `unirational|Unirational|IsTorus|torus.*parametr|torus.*dominant`:
  found the existing IsTorus definition and its consumers, but no parametrization.
- grep of `lem-sfb-torus-unirational-parametrization` in
  `lean/WeilConjectures`: no match.

No disputed statement, missing notion, unusable dependency, or source-based
statement correction was needed.

## Second reading by Q88

Re-read the node and completed Lean file in this worker session, independently
of the drafting pass; no second agent was started, as instructed. The eventual
maintainer review remains independent of this worker.

The binders introduce exactly k and T with the existing IsTorus predicate.
The conclusion introduces a natural dimension and an actual open subscheme,
requires a point of that scheme, and then quantifies a scheme morphism. Its
one equality expresses exactly that q is over k. IsDominant requires dense
image in the entire underlying scheme of T; it neither assumes nor asserts
density of rational points. There is no rank-positivity restriction and no
added finite-field or characteristic hypothesis. The affine-space polynomial
spectrum clause agrees with the recorded SpecIso API. No mismatch was found
and no node correction or dependency module was introduced.
