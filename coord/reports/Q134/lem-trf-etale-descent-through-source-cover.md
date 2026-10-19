## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover` states
`AlgebraicGeometry.Etale.of_comp_of_surjective_etale`. Its only proof is `sorry`,
as required for stage 2. No definitions, helper nodes or statement corrections are needed. The item's
`lean` field changes, and one proof dependency receives the module-wrapper repair below.

Clause-by-clause comparison with the node:

- Schemes T, X, Y: `{T X Y : Scheme.{u}}`, with explicitly declared `universe u`.
- Morphism h from X to T: `(h : X ⟶ T)`.
- Morphism p from Y to X: `(p : Y ⟶ X)`.
- Surjectivity of p on underlying points: `[Surjective p]`.
- Etaleness of p: `[Etale p]`.
- Etaleness of h composed with p: `[Etale (p ≫ h)]`. Lean's composition order is
  first p, then h, exactly the node's h composed with p.
- Conclusion that h is etale: `Etale h`.
- The absence of separation, finite-type and Noetherian assumptions is preserved:
  the signature has only the displayed three hypotheses. There is also no
  quasi-compactness assumption on p.

Statement dependency declarations read in full and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`. These are schemes and locally ringed-space morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.Surjective`, whose field is `Function.Surjective p`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, defined by
  etale ring maps on affine opens. Its `iff_flat_and_formallyUnramified` equivalence
  and the dependency record identify it with the node's notion.

Proof dependency modules are imported without `public`, with the recorded declarations:

- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`:
  `AlgebraicGeometry.smooth_and_fibre_dimension_zero_of_etale`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth.of_comp_of_flat_of_surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `AlgebraicGeometry.SmoothOfRelativeDimension`.
- `Mathlib.AlgebraicGeometry.AffineScheme`:
  `AlgebraicGeometry.Scheme.isBasis_affineOpens`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation.finitePresentation_appLE`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint`:
  `AlgebraicGeometry.flat_composite_fibre_dimension_at_point`.
- `Sheaf.AlgebraicGeometry.EtaleOpenOfSmoothZeroFibreDimension`:
  `AlgebraicGeometry.exists_etale_open_of_smooth_of_fibre_dimension_zero`.
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`:
  `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`.

The theorem docstring gives every step of the node's proof, including the derivation
of local finite type, additive dimension at a point of the scheme-theoretic fibres,
and the final open-cover locality argument. The three Sheaf proof modules were also
read using `scompile.py --source` to confirm their published interfaces.

Source and edge cases checked before writing:

- Read `literature/stacks-project/descent.tex`, `lemma-etale-etale-local-source`
  (Tag 036W). It states that etaleness is etale local on the source; applying this
  to the singleton surjective etale cover gives exactly this node.
- X empty: h is etale by the empty open cover. No nonemptiness binder excludes it.
- Y empty: surjectivity forces X empty, so the same case applies.
- T empty: existence of h forces X empty, and existence of p forces Y empty.
- Identity p: the composite hypothesis is precisely etaleness of h.
- An infinite disjoint union of etale source neighbourhoods is permitted; p need not
  be quasi-compact. No finite-cover assumption appears in the statement or proof plan.
- All three schemes lie in the same arbitrary universe, as in the project's scheme
  category; there is no bounded independent universe for test objects.

Searches for an existing statement:

- `msearch.py`, LeanFinder, query `Etaleness of a scheme morphism descends along a
  surjective etale cover of its source`: eight hits, including `IsEtale.of_comp`,
  `IsEtale.instHasOfPostcompPropertyScheme` and `Algebra.IsStandardEtale.of_surjective`.
  None match: the first results cancel the other arrow, and the last concerns a
  surjective ring map.
- `msearch.py`, Loogle, query `"Etale", "Surjective"`: four hits,
  `Algebra.FormallyEtale.iff_of_surjective`, `Algebra.IsStandardEtale.of_surjective`,
  `AlgebraicGeometry.instDescendsAlongSchemeEtaleMinMorphismPropertySurjectiveFlatQuasiCompact`,
  and `AlgebraicGeometry.Scheme.pointSmallEtaleFiberObjToPreimage_surjective`.
  None match. Read `LocalFlatDescent.lean`: its etale instance descends under target
  base change, whereas the item descends through precomposition on the source.
- `msearch.py`, Mathlib grep in `AlgebraicGeometry`, query
  `Etale.*of_comp|of_comp.*[Ee]tale|[Ee]tale.*[Dd]escent|[Dd]escent.*[Ee]tale`:
  four hits, in WeaklyEtale, Etale and LocalFlatDescent. Reading `Etale.of_comp`
  confirms that its conclusion concerns the first arrow, unlike this item.
- `rg` with the same pattern over the upstream `WeilConjectures` source and the
  project's `lean/Sheaf` found composition uses, target descent, torsor descent,
  coefficient descent and other etale constructions; no exact statement.
- `grep -rn 'lem-trf-etale-descent-through-source-cover'` in the upstream source:
  no hits. In `lean/Sheaf`, the node is mentioned in the proof documentation of
  `ValuationSmoothBranchesStrictChart`, without a matching declaration.
- Exact prospective-name search using `rg` for
  `etale_of_comp_of_surjective|of_comp_of_etale_of_surjective|Etale.of_comp_of_surjective|etale_descent_through_source_cover`
  over upstream and `lean/Sheaf`: no hits.

No statement dispute or node fault was found.

## Dependency modules

`lem-sbc-flat-composite-fibre-dimension-at-point`: its recorded module
`Sheaf.AlgebraicGeometry.FlatCompositeFibreDimensionAtPoint` was a legacy non-module
file. The first compilation failed with `cannot import non-module ... from module`.
The delivered dependency module preserves its theorem statement, source and complete
proof docstring, and `sorry` proof. It adds a copyright header, `module`, public
imports and an exposed public section. It also imports the recorded proof-dependency
modules as the stage requires: `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula`,
`Sheaf.AlgebraicGeometry.CompositeFibreLocalModels`,
`Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`, and
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`; the open-subspace dimension result is
already supplied by the public KrullDimension import. Its node changes only in `lean`, with the
required explanation in `lean.note`. This is an interface repair to an existing
proof dependency, with no mathematical change. In particular the binders remain
arbitrary schemes U, X, S; maps a and f; a point u; local finite type of both maps;
and flatness of a at u. The conclusion remains the exact additive dimension equality
at the three specified fibre points. Empty domains cause no extra obligation because
the statement explicitly has a point u; no global flatness or Noetherian hypothesis
is introduced. The item's dependency lists are unchanged.

## Second reading by Q134

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
