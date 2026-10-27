## Worker report

The module `Sheaf.AlgebraicGeometry.NodalTraitNormalizationAtlas` states
`AlgebraicGeometry.exists_nodal_trait_normalization_atlas` with one postponed theorem
proof. The auxiliary proposition `NodalAtlasSplitBranchDescription` abbreviates the
specific two-axis pullback clause of this theorem; it constructs no chosen algebra or
normalization. Its existential ring map is characterized on every polynomial class
by the two axis restrictions, so the comparison is with the canonical normalization
map, not an arbitrary ring map.

Hypotheses and clauses, in statement order:

- DVR: `R : CommRingCat.{u}`, `[IsDomain R]`, `[IsDiscreteValuationRing R]`.
  `π : R` and `_hπ : Irreducible π` express the chosen uniformizer, using Mathlib's
  `irreducible_iff_uniformizer`. `K`, `Field K`, `Algebra R K`, and `IsFractionRing R K`
  specify the fraction field and its canonical structural map.
- `f : X ⟶ Spec R` is the given scheme morphism. `IsHProjective f` is exactly the
  recorded finite-projective-space embedding convention. `Flat f` is flatness.
  `LocallyOfFinitePresentation f`, `QuasiCompact f`, `QuasiSeparated f` together say
  finite presentation, following the recorded definition's comparison clause.
- `hf` ranges over all algebraically closed fields in the scheme universe and all
  maps `Spec Ω ⟶ Spec R`. Its `Nonempty`, `IsReduced`, `IsPureDimension 1` conjuncts
  impose exactly the three fibre conditions, without adding connectedness.
- At every closed nonsmooth geometric-fibre point, the last conjunct of `hf` gives
  `Nonempty (NodalFiber.completedLocalRing z ≃+* NodalFiber.powerSeriesQuotient Ω)`.
  The stalkwise formal-smoothness test follows the already recorded DVR local-form
  theorem: for this finitely presented field fibre it tests smoothness at the point.
- `IsNoetherian X ∧ IsReduced X` gives both initial conclusions.
- `m : ℕ`, `U : Fin m → Scheme`, and `p` describe one finite family. Every member
  satisfies `IsAffine` and `Etale`; the quantified point-lifting clause is joint
  surjectivity, with no separate atlases for the later conclusions.
- A chart meeting the special fibre is recognized by a point mapping to
  `IsLocalRing.closedPoint R`. Its `A`, injective local `φ : R →+* A`, DVR and
  `Etale (Spec.map φ)` clauses specify the étale extension of DVRs; `Irreducible t`
  specifies its uniformizer. The zero-parameter disjunct uses the existing
  `StrictSemistableModel.nodal 0`; the other uses `.nodal (t ^ n)` for `n : ℕ`.
  Each `q` is étale, and the displayed equality is the triangle over Spec R.
- The zero-parameter normalization is `NodalAtlasSplitBranchDescription`: its ring
  map sends each polynomial to its restrictions to the u and v axes in
  `Polynomial A × Polynomial A`. The isomorphism between the two pullbacks commutes
  with their projections to U. The nonzero-parameter case asserts `IsIso` of the
  normalization pullback projection, i.e. identity normalization over U.
- Charts not meeting the special fibre factor through `Spec K` by `r`, with its
  explicit structural equality. They are either smooth with identity normalization,
  or étale over the zero-parameter model over `L`, where `Module.Finite K L` and
  `Algebra.IsSeparable K L` say finite separable. The same axis-restriction helper
  supplies the two-branch normalization formula over L.
- `IsFinite X.fromReducedNormalization` and `Surjective` state both properties of ν.
  The next five conjuncts state H-projectivity, flatness and finite presentation
  of `X.fromReducedNormalization ≫ f`.
- The next quantified geometric-fibre clause repeats precisely the original
  nonempty, reduced, pure-dimension-one, closed-nonsmooth-point nodal conditions
  for the normalized family. No connectedness is imposed.
- `Smooth (pullback.snd ... (Spec.map (algebraMap R K)))` states smoothness of C_K/K.
- `IsIso (pullback.snd X.fromReducedNormalization f.smoothLocus.ι)` is the identity
  normalization on the entire relative smooth locus.
- The final isomorphism identifies C_K with the existing componentwise normalization
  of X_K. Its two equalities identify the induced map to X_K by both pullback
  projections, hence say the isomorphism is over X_K, including its K-structure.

Dependencies read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing` and
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`: `Scheme.reducedNormalization`,
  `Scheme.fromReducedNormalization`, and the actual component construction.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`; the companion integral
  definition was read in `Morphisms.Integral`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and its pointwise locus.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsReduced`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Sheaf.TraceFormula.StrictSemistableCurve`: `strictNodalRing`,
  `StrictSemistableModel.nodal`, `.scheme`, `.baseMap`.
- `Sheaf.AlgebraicGeometry.NodalGeometricFibreLocalRings`:
  `NodalFiber.completedLocalRing`, `.powerSeriesQuotient`, `.projection`.

The last two already-landed definition nodes are added to `stmt_deps`; they are not
new notions. Statement dependencies are public imports. Recorded modules of stated
proof dependencies are plain imports. Unstated proof dependencies have no module
available to import and are not restated merely for the future proof. The theorem
docstring follows all fourteen existing proof steps, with their dependency names.

Edge cases checked before writing: n=0 gives uv=1 and is retained; n>1 is not
restricted; split nodes over both DVR and finite separable generic coefficient
fields are retained. Nonempty fibres exclude the empty source, but the finite index
binder still permits m=0 syntactically. No connectedness, excellence, completeness,
normality or generic smoothness hypothesis is added. A disconnected reduced nodal
curve is allowed. The normalization used throughout is the componentwise one even
for reducible X. Empty individual atlas members cause no extra restrictions.
All scheme/ring/field universes are explicitly u; no implicit universes or variables.

Searches for an existing declaration (2026-10-24):

- msearch leanfinder: `finite etale atlas normalization nodal curve family over
  discrete valuation ring` returned eight hits, including Weierstrass reduction,
  standard-étale presentations and relative normalization, none this theorem.
- msearch loogle: `AlgebraicGeometry.Scheme.reducedNormalization,
  AlgebraicGeometry.Etale` returned no hits; the service does not index this
  project's componentwise normalization declaration.
- msearch grep in Mathlib/AlgebraicGeometry: `nodal|Nodal|normalization` found relative
  normalization and Zariski main theorem, not this atlas or the componentwise result.
- msearch leansearch: `normalization nodal curve family discrete valuation ring
  finite etale charts` returned DVR characterizations and relative normalization,
  no matching theorem.
- rg in both `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry`: `nodal|Nodal|normalizationAtlas` located existing
  DVR local forms, geometric-fibre local rings, normalization comparison and binomial
  models. Each relevant recorded declaration and docstring was read. An exact item-id
  search in `lean/WeilConjectures` found no declaration. A name search for the new
  theorem/helper names in both project roots found no collision.

Source checking: read Stacks models.tex Tag 0CDD, including its smooth n=0 chart and
DVR étale-neighbourhood construction, and more-morphisms.tex Tag 07TD. Read the current
blueprint's direct-image stability proof in the item's unit; this is a supporting
DAG lemma, not the unit's own statement. There is no statement correction, new node,
or disputed statement in this delivery.

Compiler/import note: the first server compile rejected importing the legacy proof-only
module `Sheaf.AlgebraicGeometry.NodalFamilyEtaleSourceLocality` from module mode
(`cannot import non-module ... from module`). Its current live source was checked with
`scompile.py --source`; it still has no `module` command. That single incompatible
proof-only import is omitted, while its theorem remains in the proof plan. No statement
notion depends on it, no private definition substitutes for it, and its source is not
edited. The maintainer can restore this proof import when that legacy module is migrated.
All other recorded proof imports were checked for module mode.

Validation: the final module compiled cleanly through `scompile.py` in both sandbox
and library mode (13.9 s and 3.9 s compiler runs). Explicit `C := Scheme.{u}` parameters
resolve category/coercion inference on the geometric-fibre pullbacks. No diagnostic
commands remain; the theorem's sole proof is `sorry`; definitions contain no `sorry`.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
