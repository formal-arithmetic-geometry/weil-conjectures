## Worker report

The module `Sheaf.AlgebraicGeometry.SeparatingSteinGenericCurve` states
`AlgebraicGeometry.separating_stein_generic_curve`, with a single `sorry` and
no definitions or proofs. The seven-step proof is transcribed in its docstring.
The node is unchanged except for its Lean record and addition of the already
recorded `def-weil-pbc-separable-field-extension` to statement dependencies:
this node owns the existing `Algebra.IsSeparablyGenerated` notion used here.

Hypotheses and conclusions, checked against the entire node statement:

- Fields k ⊆ F ⊆ L ⊆ E: four `Field` instances, six `Algebra` instances,
  and the four compatible `IsScalarTower` instances. These are the displayed
  inclusions and their composites; they impose no characteristic restriction.
- E/k and F/k finitely generated: `hEfg`, `hFfg` use
  `(⊤ : IntermediateField k _).FG`, field generation, not algebra finite type.
- E/F separably generated of transcendence degree one: `hsep` uses the
  upstream `Algebra.IsSeparablyGenerated`, and `htrdeg` is `Algebra.trdeg F E = 1`.
  The upstream notion permits arbitrary separating bases, but under finite
  generation and transcendence degree one its basis is finite (one element),
  and the algebraic extension above that basis is finite. Thus it is precisely
  the node's finite separating-basis convention in this context.
- L/F finite: `[FiniteDimensional F L]`. Its separability is the first conclusion
  `Algebra.IsSeparable F L`; finiteness is already in context.
- L algebraically closed in E: `hclosed` says every element algebraic over L
  is the image of an element of L, using the specified `algebraMap L E`.
- Integral finite-type k-schemes T and Y: `[IsIntegral T]`, `[IsIntegral Y]`,
  structure maps `t`, `y`, each locally of finite type and quasi-compact.
- Proper dominant k-morphism: `g`, `[IsProper g]`, `[IsDominant g]`, `hg`.
- T normal: `hT` says every local ring is a domain and integrally closed,
  exactly the node's explicit normality convention.
- k(T) = E and k(Y) = L as k-fields: ring equivalences `eT`, `eY`;
  `heT`, `heY` require the induced generic spectrum maps to commute with
  the structure maps to Spec k. No arbitrary algebra on a generic stalk is used.
- The map on function fields is L ⊆ E: `hmap` evaluates the recorded
  `g.dominantFunctionFieldAlgebra` on every element and transports through
  `eY`, `eT`. This is the actual pullback of germs, not an unrelated embedding.
- The generic fibre C = T ×_Y Spec L: `C`, its projections `j`, `c`, and `hC`
  present exactly that pullback, with base arrow
  `Spec.map eY.toRingHom ≫ Y.fromSpecFunctionField`. This is an arbitrary
  representative of the specified fibre product, by its universal property;
  it adds no restriction to the theorem. In particular the canonical chosen
  pullback with `pullback.fst` and `pullback.snd` always supplies these binders.
- E/L separably generated of transcendence degree one: the second and third
  conjuncts `Algebra.IsSeparablyGenerated L E` and `Algebra.trdeg L E = 1`.
  As above its finite-generation-over-L follows already from E/k finite
  generation and k ⊆ L, so this includes the finite convention for its basis.
- Proper finite-type L-scheme C: `IsProper c`, `LocallyOfFiniteType c`,
  `QuasiCompact c` (finite type written explicitly as in its dependency record).
- C normal: the next conjunct quantifies over all stalks and requires both
  `IsDomain` and `IsIntegrallyClosed`.
- C geometrically integral: `GeometricallyIntegral c`, the recorded Mathlib
  notion quantifying over all field extensions of the base.
- Its function field is E over L: the existential provides `IsIntegral C`
  before forming `C.functionField`, then a ring equivalence `eC` to E.
  Its equation says the generic spectrum morphism composed with `c` is
  precisely `Spec.map (algebraMap L E)`. Thus the field identification
  respects the specified L-structure, rather than merely being a ring iso.
- Dimension C = 1: `topologicalKrullDim C = 1`.
- Dimension Y = trdeg_k F and dimension T = trdeg_k F + 1: the last two
  conjuncts, with `Cardinal.toENat` and the inclusion into `WithBot ℕ∞`.
  Finite generation makes the cardinal finite, so the conversion loses no data.
- No smoothness assertion is made. The node's final generic explanations of
  projective morphisms, semilinear actions and birational morphisms introduce
  no hypotheses or conclusions involving those notions in this item.

The fields and schemes live in one explicitly bound universe `u`: all the
inclusions land in E and each field can be represented in this common universe.
There is no separate smaller universe restricting test field extensions. All
variables are bound; `set_option autoImplicit false` enforces this.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (`def-weil-field`).
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` (and `IsReduced` in the
  proof plan); `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `LocallyOfFiniteType`, with `QuasiCompact`; `Morphisms.Proper`: `IsProper`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded component
  product module explicitly documents reusing `Scheme.functionField` for
  integral schemes, which is the generic stalk in Mathlib's FunctionField.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`; `Mathlib.RingTheory.AlgebraicIndependent.Basic`:
  `Algebra.trdeg`; `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.RingTheory.AlgebraicIndependent.Defs`: `IsTranscendenceBasis`;
  `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `WeilConjectures.FieldTheory.SeparableExtension`: `Algebra.IsSeparablyGenerated`,
  using exactly the preceding basis and separable-algebraic notions.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `Pullback.IsPullback.Defs`: `IsPullback`
  is its universal-property presentation, not another fibre-product definition.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`.
- `Sheaf.TraceFormula.LocalDimensionFormula`:
  `Scheme.Hom.dominantFunctionFieldAlgebra`; its implementation uses the
  generic-point equality and `Scheme.Hom.functionFieldMap` from
  `WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`:
  `Scheme.fromSpecFunctionField`, defined as `Scheme.fromSpecStalk` at the
  generic point, supplies the canonical generic spectrum morphism.

The already stated proof dependency modules are imported without `public`,
including the separating-field, irreducible-generic-fibre, tensor-reducedness,
generic-stalk geometric-reducedness, finite-separable-closure,
generic-residue-field geometric-irreducibility and dimension/trdeg results.
The local-spectrum-base-change-stalks node has no recorded declaration and is
not imported; it supplies no object needed to type this statement. The
localization and transcendence-degree Mathlib proof dependencies are imported.

Sources read: Stacks `varieties.tex`, lemma-geometrically-irreducible-function-field
(Tag 054Q) and item-dimension-irreducible-trdeg (0B1C);
`algebra.tex`, lemma-characterize-separable-field-extensions (030W) and
lemma-make-geometrically-irreducible (037Q). These agree with the node.

Edge cases checked: F = L, including F = L = k and E = k(t), gives a proper
normal geometrically integral curve over k and base dimension zero. Finite
inseparable L/F is excluded by the separating E/F hypothesis, not an added
assumption. Extra algebraic constants would violate `hclosed`. Imperfect
fields and normal curves which are not smooth remain included. Empty T or Y
is excluded by integrality; empty C cannot present this dominant generic
fibre. No assumption that Y is normal, or that any scheme is projective,
is imposed. The finite-type hypotheses rule out infinite cardinal trdeg in
the dimension formulas. No statement correction or disputed mathematical
claim was necessary.

Searches (2026-10-24):

- `msearch.py leanfinder`: “A proper dominant morphism of normal integral
  varieties with separably generated function field of transcendence degree
  one and relatively algebraically closed constants has a normal geometrically
  integral generic curve.” Eight hits on normalization, proper sections, and
  integral morphisms; none states this theorem.
- `msearch.py loogle`: `GeometricallyIntegral, IsNormal, functionField`.
  Unknown unqualified identifier `GeometricallyIntegral`; no hits.
- `msearch.py leansearch`: “Generic fibre of a proper dominant morphism of
  normal integral schemes has function field the same as the source and is a
  geometrically integral curve when the field extension is regular of
  transcendence degree one.” Eight hits: `Scheme.Hom.fiber`, `IsDominant`,
  `Scheme.functionField`, fibre projection and fraction-field declarations;
  none is the requested conjunction.
- `msearch.py grep`: `geometricallyIntegral.*(generic|fiber)|generic.*[Gg]eometricallyIntegral`
  in AlgebraicGeometry. Five hits in Mathlib Geometrically/Integral are fibre
  consequences or fibrewise criteria, not the generic-curve theorem.
- `rg` of upstream WeilConjectures and Sheaf for the item id and
  `separatingStein|separating_stein|IsSeparablyGenerated|dominantFunctionField`
  located the existing separably generated definition, the canonical field
  algebra, and NormalSteinConstantField (the predecessor producing constants).
  No existing declaration states this item. Searches for `genericFiber`,
  `genericFibre`, and `fromSpecFunctionField` located constituent APIs only.
- `rg` of Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json`
  for `separating_stein_generic_curve|separatingSteinGenericCurve`: no collision.

Validation: `scompile.py N6 lem-sfb-separating-stein-generic-curve` compiled
this module on the server against the published live build. No errors or
unexpected warnings were reported. The final imports are checked again by
scompile and the prescribed delivery dry run.

## Second reading by N6

The assigned worker performed a separate second pass with the node and the
final theorem open; no other agent was started, as the dispatcher forbids it.
The maintainer performs the independent delivery review. This pass checked
all the correspondences above, particularly the k-compatibility of the two
field identifications, the canonical rather than arbitrary function-field
map, and the L-compatibility of the output identification. It also checked
that `IsPullback` presents the stipulated generic fibre, that normality is
asserted on C itself rather than on every geometric fibre, and that finite
field generation is represented by IntermediateField.FG rather than
Algebra.FiniteType. No mathematical mismatch was found. The existing
separably-generated definition node was added to statement dependencies and
its module imported; no duplicated definition was introduced.
