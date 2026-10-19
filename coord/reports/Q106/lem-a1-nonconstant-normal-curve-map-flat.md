## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.NonconstantNormalCurveMapFlat` states
`AlgebraicGeometry.flat_of_nonconstant_of_isNormalCurve`, with its proof left as `sorry`.
It is exactly Stacks Project, Curves, Tag 0CCK, lemma-flat, read in
`literature/stacks-project/curves.tex`, lines 85–105. The declaration docstring records
all seven steps of the node's expanded proof and their supporting DAG nodes.

Hypothesis and conclusion correspondence:

- “k is a field”: `{k : Type u} [Field k]`.
- “X and Y are schemes over k”: `{X Y : Scheme.{u}}`,
  `[X.Over (Spec (.of k))]` and `[Y.Over (Spec (.of k))]` give the structure morphisms.
- “curves, separated integral schemes of finite type and dimension one”:
  `[IsIntegralCurve (X ↘ Spec (.of k))]` and its Y counterpart. The recorded class
  extends `IsVariety`, which includes `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsIntegral`, and adds `topologicalKrullDim_eq_one`.
  Locally finite type plus quasi-compact is finite type. The recorded proof dependency
  `Scheme.dim_eq_topologicalKrullDim` identifies the local-ring dimension convention.
- “f is a k-morphism”: `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]` asserts the structure triangle.
- “its image contains at least two points”:
  `(h_nonconstant : ∃ x₁ x₂ : X, f x₁ ≠ f x₂)`. A pair in the image has preimages,
  and distinct images of preimages give a pair in the image, so this is equivalent
  without asserting injectivity or surjectivity.
- “Y is normal, every stalk an integrally closed domain”:
  `(h_normal : IsNormalScheme Y)`. The exact dependency definition is
  `IsIntegral Y ∧ ∀ y, IsDomain (Y.presheaf.stalk y) ∧
  IsIntegrallyClosed (Y.presheaf.stalk y)`. Its integral clause is already supplied
  by the curve hypothesis and does not strengthen the node.
- “f is flat”: `Flat f`, the recorded Mathlib predicate. Its theorem
  `Flat.iff_flat_stalkMap` gives exactly the stated stalkwise flat-module condition.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`:
  `AlgebraicGeometry.IsIntegralCurve`, `AlgebraicGeometry.IsVariety`, their full
  signatures, docstrings, and fields. The file is absent from the older source tree;
  its full definition was read in the shared side-project source and confirmed with
  `scompile.py --source WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`.
- `Sheaf.AlgebraicGeometry.NormalScheme`: `AlgebraicGeometry.IsNormalScheme`, read
  from the shared published module, using its actual integral/stalk conjunction.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, and
  `AlgebraicGeometry.Flat.iff_flat_stalkMap`, read from the pinned Mathlib source.

All recorded modules of proof dependencies are imported non-publicly, including
`Sheaf.AlgebraicGeometry.Dimension`, `WeilConjectures.AlgebraicGeometry.Regular`,
`WeilConjectures.Topology.PresheafModuleStalkFunctor`, and the Mathlib modules for
sobriety, topological/ring dimension, local rings, affine stalk localization,
Noetherianity, function fields, and PID torsion-free flatness. No additional
statement hypotheses are introduced by these imports.

Edge cases checked before writing:

- Empty schemes and zero-dimensional schemes are excluded by the node's own
  integral dimension-one curve convention, not an additional Lean assumption.
- Constant maps are excluded by the exact two-point-image hypothesis; a constant
  map of curves need not be flat, so this hypothesis is essential.
- The identity of a normal curve and non-surjective nonempty open immersions are
  included. No finiteness, properness, surjectivity, smoothness, perfection, or
  algebraic-closedness hypothesis on f or k was added.
- Non-smooth normal curves over imperfect fields are included; only target
  normality is required. The source may be singular and nonnormal.
- At the target generic point the local ring is a field, not a DVR; the docstring
  retains this case. No finite generation as a module over a stalk is assumed.
- One explicit arbitrary universe u is used for the field and schemes, matching
  the recorded curve interface. There are no quantified auxiliary test objects
  or independent small universes that could make a condition vacuous.

Searches made with `/home/ubuntu/weil-launcher-nt/msearch.py Q106
lem-a1-nonconstant-normal-curve-map-flat`:

- LeanFinder: `A nonconstant morphism of integral curves with normal target is flat`.
  Eight hits: Flat, its ring-hom-property/multiplicativity/flat-open-immersion
  interfaces, normalization integrality, generalizing maps, the stalk criterion,
  and IsSmooth; none is the desired theorem.
- LeanSearch: `A nonconstant morphism from an integral curve to a normal curve is flat`.
  Eight hits: ring-map and scheme flatness definitions, Flat.mk, flat_iff,
  flat open immersions, multiplicativity, and the two stalk criteria. None matches.
- Loogle: `AlgebraicGeometry.Flat, AlgebraicGeometry.IsIntegral`.
  Four hits: flatness over a subsingleton integral target and three integrality
  results for geometric base changes. The first has a one-point target and the
  others assume flatness; none gives flatness over a normal curve.
- Mathlib grep in AlgebraicGeometry:
  `flat.*(curve|[Dd]edekind|[Dd]ominant)|([Dd]edekind|[Dd]ominant).*flat`.
  Four hits in SchemeTheoreticallyDominant, all about flat base change rather
  than this implication. The actual Flat declarations and single-point-target
  instance were opened and read.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` for curve/normal/dominant flatness:
  unrelated normalization, flat morphisms already assumed, and existence of a
  finite flat map to the projective line, which is a different assertion.
  The target id is mentioned in the proof docstring of the downstream
  NonzeroDifferentialGenericallyEtale module, but has no statement there.
- The exact node id was searched in upstream WeilConjectures and the exact new
  name `flat_of_nonconstant_of_isNormalCurve` in upstream, the upstream-name index,
  the shared Lean modules, and Mathlib AlgebraicGeometry: no existing declaration.

No node faults, disputed statement, new nodes, dependency repairs, or changes to
statement/dependency/proof fields were needed. Only the item's `lean` field changes.

## Second reading by Q106

Author self-check under the remote direct-delivery instruction; independent review
belongs to the maintainer. Reopened the node, source lemma, recorded definitions,
and generated file. Checked field, base structures, both integral curves, the
k-linearity triangle, the pair of different image points, target normality, and
flatness conclusion against the correspondence above. No mismatch was found.
In particular the normality predicate's integral clause is redundant given
IsIntegralCurve Y, and the two-point condition does not require closed points.
All theorem variables/universes are explicitly bound, all proofs are `sorry`,
and there is no new definition. No source or statement correction was made.

## Validation

The prescribed scompile.py wrapper passed with no errors or warnings: sandbox
compile 44.0 seconds and library-path compile 11.2 seconds. The file has exactly
one theorem and one sorry; every line is at most 100 characters. The copied JSON
was compared with the shared base: `lean` is its only changed key. The dry-run
preflight and per-file compilation are run with deliver2.py before the final push.
