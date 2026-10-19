## Worker report

The theorem `WeilConjectures.a1LisseSectionsStalkEvaluation` states finite
closed-point detection, finite dimension, invertibility of the specified ordinary
geometric Frobenius, and evaluation compatibility with its degree-th power. Its
proof is postponed. The helper module constructs the canonical evaluation map by
the whole-system adjunction counit, rationalization, coefficient extension, and
cohomology. No arbitrary map replaces evaluation.

Hypothesis and clause correspondence:

- The finite field, its algebraic closure and characteristic are `D : FiniteFieldDatum`.
  The prime is `l`, `[Fact l.Prime]`, with `hl : l ≠ D.p`.
- The finite-type separated scheme is `Y₀ : Over (Spec (.of D.k₀))` with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure map.
  Its geometric fibre is precisely `D.geometricFiber Y₀`.
- The coefficient closure is `Ω`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
  `[IsAlgClosure ℚ_[l] Ω]`. The common point-fibre API has coefficient and scheme
  universes `u`; this follows the recorded local Frobenius dependency.
- `G : sfCommonStageWeilSheaf ...` supplies the heart object and its actual Weil
  isomorphism. `_hG : IsCommonStageLisse ... G.obj.carrier` supplies chart-local
  finite rational freeness, without a global lattice or a Weil-stable lattice.
  The added landed definition node makes this notion explicit in this model.
- `c₀ : Compactification Y₀.hom` is the retained presentation required by the
  published cohomology functor, with `compact = false`. Every separated finite-type
  scheme has such a presentation; this binder does not assert properness of Y₀.
- `A1SectionEvaluation.sections ...` is exactly degree-zero ordinary published
  cohomology, the module carrying `globalGeometricFrobeniusQbarOnCohomology ... false 0`.
- `∃ m, ∃ y : Fin m → {y // y ∈ closedPoints _}, ∃ ι, ∃ hι` supplies a finite
  indexed family with no distinctness requirement. The residue-field embeddings
  `ι` and their base compatibility `hι` give the actual geometric lifts through
  `localClosedPoint`. Injectivity is of the function evaluating at these lifts.
- `FiniteDimensional Ω (sections ...)` renders finite dimension.
  `IsIso (globalGeometricFrobeniusQbarOnCohomology ... false 0)` renders the linear
  automorphism assertion, since the recorded arrow is in `ModuleCat Ω`.
- The last universally quantified clause uses every closed point, every compatible
  residue embedding, every section, and exponent `localClosedPointDegree`.
  Its right side is exactly `localQbarClosedFrobeniusStalk`, including semilinear
  return and the iterated Weil isomorphism. Positivity of that recorded degree is
  `localClosedPointDegree_pos`, not an additional hypothesis.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `WeilConjectures.FiniteFieldDatum.geometricFiber`.
- `Sheaf.Paper.LisseIntegralSmallCoefficients` records the inverse-system lisse
  convention; `Sheaf.Paper.CommonStageLocallyFree` supplies
  `WeilConjectures.IsCommonStageLisse` in the fixed-pair model.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`,
  `sfCommonStageWeilComplex`, `sfWeilPrimeInvertible`.
- `Sheaf.Paper.GlobalGeometricFrobenius`:
  `globalGeometricFrobeniusQbarCohomology`,
  `globalGeometricFrobeniusQbarOnCohomology`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localClosedPoint`,
  `localClosedPoint_compatible`, `localClosedPointDegree`, `localQbarStalk`,
  `localQbarClosedFrobeniusStalk`, `localQbarPullbackStageIso`, `localQbarFibreObjIso`.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`: the actual integral
  pullback unit and composition comparisons; the imported system realization
  provides `FrobeniusExchange.models`, `systemAdjunction`, and `directImageFunctor`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`:
  `frobeniusCoefficientModules`, `frobeniusCohomologyStageEmbedding`,
  `frobeniusCohomologyQbarSourceEq` and the ordinary rational cohomology functor.
- `Sheaf.Paper.FieldCohomologyScalarExtension`:
  `DerivedCategory.fieldDerivedHomologyIso`; the coefficient cohomology dependency
  supplies `coefficientFdCohomology` and `coefficientQbarCohomology`.
- Upstream exact derived functors provide
  `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`.
  Mathlib supplies `ModuleCat.extendScalarsComp` and the category and module notions.

Edge cases read against the source: the empty scheme allows `m = 0`, and its
section module is zero. Rank zero is allowed by chart-local lissity. On
`Spec F_q` evaluation has the expected degree-one identity. On `Spec F_(q²)`
there can be two geometric components over the same closed point: the indexing
allows both lifts and the identity uses T². No connectedness, nonemptiness,
positive rank, or Frobenius-stable integral lattice is assumed. The scalar
normalization includes identity field embeddings, not just strict extensions.

Searches: `msearch.py leanfinder` for finite stalk detection returned scheme germ
injectivity and arithmetic-Frobenius lemmas, no match. `loogle` for
`FiniteDimensional, LinearMap.ker` returned general linear algebra only.
`msearch.py grep` for `lisse|globalSections.*frobenius|stalk.*frobenius` in
Mathlib AlgebraicGeometry returned no hits. `leansearch` for canonical evaluation
via the pullback/direct-image counit returned generic sheaf/module counit and
stalk maps, no common-stage construction. The exact outputs are retained in
`searches.jsonl` and the new node's search records. Project `rg` in
`lean/WeilConjectures`, `lean/Sheaf`, and DAG nodes found the upstream
`WeilSheaf/Stalk` result in a different coefficient model and
`ProperSectionsSemilinearGerms`, whose properness assumption is unavailable here.
`blueprint_refs.py search 'section evaluation'` returned no match. No existing
declaration states this conjunction for the recorded fixed-pair operators.

No statement correction or disputed mathematical statement is proposed.

## New nodes

`def-a1-lisse-section-evaluation` defines evaluation on ordinary common-stage
cohomology through the actual adjunction counit, with the canonical normalized
scalar-size comparison. Its source is the parent's second paragraph and Deligne
Weil II (1.1.7), (1.1.10)-(1.1.14). The new module includes one postponed theorem
asserting existence and uniqueness of the scalar comparison with its pure-tensor
normalization. This determines the chosen isomorphism uniquely; its definition
has real data selected from that unique characterization. All remaining helper
maps are explicit compositions of recorded maps. The searches above exclude a
duplicate in this model, and the node cites each construction it uses.

## Second reading by NR

Author's second pass (not an independent reviewer): checked every clause against
the node and the parent proof, retaining repeated lifts and the semilinear return.
The source and stalk use different derived-category universes; their comparison
is an exact scalar-and-size transport, not an imposed equality of universes.
The initial draft's scalar cohomology source was corrected to the published
`coefficientFdCohomology` functor with its original derived instance. Independent
review is reserved to the maintainer, as specified by this dispatched brief;
no other agents were started.

Validation: both modules compiled without diagnostics through scompile.py.
The delivery dry run returned OK at commit 1a2cd51fe3, including server preflight
and per-file compiles. The geometric lift evaluation uses Mathlib
`pullback.lift_snd` for its structural-map equality.
