## Worker report

The module `Sheaf.AlgebraicGeometry.SeparableCurveDifferentialNonzero` states
`AlgebraicGeometry.relativeDifferentialsPullbackMap_ne_zero_of_finite_separable`.
Its single proof is `sorry`; it defines no new object. The statement and all other
DAG fields are unchanged; only the item's `lean` record is supplied.

### Matching every hypothesis and conclusion

- The base field is `(k : Type u) [Field k]` (def-weil-field).
- The underlying schemes are `(X Y : Scheme.{u})`. The structure map of Y is
  `(g : Y ⟶ Spec (.of k))`; that of X is `f ≫ g`.
- `[IsIntegralCurve g]` and `[IsIntegralCurve (f ≫ g)]` express exactly that both
  schemes are integral, separated, of finite type over k, and of dimension one.
  The recorded `IsIntegralCurve` extends `IsVariety`, whose parents are
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`, and whose integral
  field is an instance. The curve class adds `topologicalKrullDim = 1`.
- `[Smooth g]` and `[Smooth (f ≫ g)]` express smoothness of both curves over k.
  No projectivity, properness, algebraic closure, perfection, or restriction on
  characteristic is imposed.
- `(f : X ⟶ Y)` is a k-morphism because the source structure map is the composite
  `f ≫ g`. This parametrizes every commuting triangle: given a separate source
  structure map and its equality with this composite, substitution gives exactly
  this statement, and conversely this composite supplies the commuting triangle.
- `[IsDominant f]` says the underlying map has dense range, exactly the stated
  dominance condition.
- `Y.functionField` and `X.functionField` are Mathlib's structure-sheaf stalks at
  the generic points, with their canonical field instances on integral schemes.
  This is the integral-scheme clause of def-sc-function-field; the more general
  component product is not used for these integral schemes.
- `[Algebra Y.functionField X.functionField]` supplies the extension structure.
  `hfield` requires
  `Spec.map (CommRingCat.ofHom (algebraMap Y.functionField X.functionField)) ≫
  Y.fromSpecFunctionField = X.fromSpecFunctionField ≫ f`.
  Here `fromSpecFunctionField` is exactly `fromSpecStalk` at the generic point.
  This equality specifies the function-field map induced by f, rather than an
  unrelated field algebra. Dominance gives the generic-point equality; the
  induced stalk map satisfies this square. Conversely the generic-point
  inclusion is a monomorphism (a stalk-spectrum inclusion), so the square
  determines its spectrum map uniquely, hence the same field map by Spec's
  full faithfulness. Thus this binder records the node's word "induced" and
  imposes no additional mathematical condition.
- `[Module.Finite Y.functionField X.functionField]` states finiteness of this
  extension, as prescribed in def-pc-field-tower.
- `[Algebra.IsSeparable Y.functionField X.functionField]` states that every
  element has separable minimal polynomial over k(Y). This is exactly finite
  separability together with the preceding binder.
- The conclusion `g.relativeDifferentialsPullbackMap f ≠ 0` is nonvanishing as
  an O_X-module morphism, with source
  `(Scheme.Modules.tensorPullback f).obj g.relativeDifferentials` and target
  `(f ≫ g).relativeDifferentials`. The recorded canonical map is uniquely
  characterized by `1 ⊗ da ↦ d(f♯a)`. Thus the conclusion is precisely
  `df : f* Ω_Y/k → Ω_X/k` nonzero, rather than a claim about an arbitrary map
  or only about a separately chosen vector-space map.

### Dependency declarations read and used

Statement dependencies:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`:
  `AlgebraicGeometry.IsVariety`, `AlgebraicGeometry.IsIntegralCurve`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`:
  `Scheme.functionFieldOfComponents` and its documented integral-scheme clause;
  the actual integral function field is `Scheme.functionField` in
  `Mathlib.AlgebraicGeometry.FunctionField`.
- `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree` and the module's
  convention that finite separable means `Module.Finite` and `Algebra.IsSeparable`.
  These existing Mathlib notions are used, rather than a second finiteness predicate.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`.
- `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`:
  `Scheme.Hom.relativeDifferentialsPullbackMap`, with its recorded existence and
  uniqueness theorem and its explicit generator formula.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  the recorded normalized tensor pullback interface, publicly importing the
  actual `Scheme.Modules.tensorPullback` construction from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`.

The additional public import `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`
provides the existing abbreviation `Scheme.fromSpecFunctionField` used to specify
the induced algebra. Its data is the canonical stalk inclusion, not a choice.

Stated proof dependencies are imported, privately when not already statement
imports: `AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen`
(Mathlib.AlgebraicGeometry.FunctionField), `AlgebraicGeometry.dimension_locally_algebraic`
(WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic),
`Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials` (the differential module),
`SheafOfModules.IsFiniteLocallyFreeOfRank`
(WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree),
`AlgebraicGeometry.tilde.toStalk` (Mathlib.AlgebraicGeometry.Modules.Tilde),
`KaehlerDifferential.isLocalizedModule_map` (Mathlib.RingTheory.Etale.Kaehler),
`Scheme.Modules.exists_tensorPullback_stalk_iso`
(WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk),
`KaehlerDifferential` and `KaehlerDifferential.D` (the publicly inherited Mathlib
Kahler module), and `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`
(Mathlib.RingTheory.Etale.Kaehler), with `Algebra.FormallyEtale.of_isSeparable`
(Mathlib.RingTheory.Etale.Field). The docstring records all six DAG proof steps.

### Source and edge cases

Read `literature/stacks-project/curves.tex`, lemma-generically-etale, lines 2346--2389,
Tag 0C1C. The source asserts exactly the implication from its finite separable
function-field extension (5) to the nonzero differential (1). The node's additional
explicit dominance makes the induced extension meaningful. No correction is needed.

The identity on any smooth integral curve has a degree-one separable extension
and nonzero identity differential. On the affine line the map t ↦ t^n has a
nonzero differential when n is prime to the characteristic; when positive
characteristic divides n, separability fails, so Frobenius is correctly excluded.
Nonproper curves remain included. Imperfect base fields remain included because
smoothness, not perfection, supplies rank-one differential sheaves. The empty
scheme and dimension-zero schemes are excluded by the original integral-curve
hypotheses, not by extra binders. Arbitrary field universes are allowed by u;
there is no quantified test-object universe that could make a condition vacuous.

### Searches

Searches were rerun using the prescribed msearch wrapper:

- LeanFinder: "The canonical differential sheaf map for a dominant morphism of
  smooth integral curves with finite separable function field extension is nonzero".
  Eight hits: differentIdeal_ne_bot, aeval_derivative_mem_differentIdeal,
  Weierstrass curve maps/nonzero coordinate classes, and rational-map function-field
  constructions. None states nonvanishing of this sheaf morphism.
- Loogle: `"differential", "separable"`; no hits.
- Mathlib grep: `separable.*differential|differential.*separable|functionFieldMap`;
  no hits from the wrapper.
- LeanSearch: "The canonical differential map of a dominant morphism of smooth
  curves with finite separable function field extension is nonzero". Eight hits:
  differentIdeal_ne_bot, manifold differentials, algebraic differential functoriality,
  separable polynomial derivatives, and Differential.differentialFiniteDimensional.
  None says the geometric sheaf-map assertion.
- `rg` of the same separability/differential and functionFieldMap expressions in
  `lean/WeilConjectures` and `lean/Sheaf` found field differential dimension facts,
  divisor function-field maps, the numerical Riemann--Hurwitz consumer, and related
  trace results. None states this theorem. The blueprint-id search in
  `lean/WeilConjectures` gave no declaration. The chosen theorem name was also
  searched in Mathlib, WeilConjectures and Sheaf and was absent.

No new nodes, dependency repairs, statement correction, or disputed statement.
The retained sandbox initially contained only dispatcher brief markers; this delivery
supplies a new stage-2 `lean` record and module, while preserving the reviewed split.

### Validation

Compiled through the prescribed scompile wrapper in required module mode, with
explicit universes and both auto-implicit options disabled. The initial compile
passed in both sandbox and library modes. The final compile and delivery preflight
are run by deliver2.py before pushing. Independent review is the maintainer's;
no independent second-worker reading is claimed here.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
