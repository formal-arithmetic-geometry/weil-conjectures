## Worker report

The module `Sheaf.Paper.PurityCompositionCompatibleDncCharts` states the item as a
suite of theorems, all with `sorry`. Every helper definition has real data. No
statement correction, dependency repair or new DAG node is required.

Source read: main-20261015 `sec-smooth-purity/sk-prop-sp-composition/
thm-pur-composition-coherence.proof.md`, Step 1, together with the current node's
eight proof steps. The suite retains the actual source, normal-cone and
exceptional-adjunction comparisons; it does not replace these by arbitrary
isomorphisms, and it does not assume absolute separatedness of X, Y or Z.

Hypotheses and clauses:

- `P : PurityFiniteSetting.{u}` contains the fixed finite-field datum, prime ell
  distinct from its characteristic, the actual finite intermediate field E of
  the coefficient closure, and positive `level`. `P.Coefficient` is the standard
  universe lift of the existing quotient O_E/(varpi_E^n), at every positive level.
- `d e : ℕ` includes zero. `SmoothOfRelativeDimension d f` and its g counterpart
  are the recorded smooth pure-dimension classes. `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact` render separated finite type for each map.
  The finite-type structure map `aZ` induces the structure maps of Y and X by
  composition. Thus no choices of incompatible field structures are introduced.
- `composition_compatible_affine_charts` quantifies over every point of X and
  supplies affine opens U,V,T containing that point in U. Its inequalities hUV
  and hVT express the two image inclusions. The maps x,y are etale and their
  projection equations make them charts of the restricted f,g. It also supplies
  the smooth dimensions, separated finite-type restrictions and finite-type
  structure map on T needed by the subsequent local theorem suite.
- `compatibleCompositeChart` uses `AffineSpace.homOfVector` and `Fin.addCases`:
  the first d coordinates are x, the last e are the pullbacks of y along f.
  `composition_compatible_tangent_normal` asserts this map is etale and lies
  over gf. `CompatibleTangentSequence` tests all modules over Γ(U,O_U):
  derivations for f and g are uniquely determined by the x and y coordinates;
  derivations for gf are uniquely determined by their ordered pair. The last
  two clauses assert the canonical inclusion (same derivation, zero y values)
  and restriction to V. Under the three bijections these are exactly first
  inclusion and second projection, so the sequence splits by (0,w).
- `compatibleNormalFirst` and `compatibleNormalSecond` are actual maps from
  the actual associated-graded normal cone of Δ_gf. They apply the ordered
  `chartNormalCoordinateMap`, project to the relevant block, and invert the
  corresponding actual normal coordinates. The second map also applies f on
  the base. `compatibleNormal_condition` makes their pullback lift well typed;
  `compatibleNormalSplitting_spec` states invertibility, preservation of the
  projection to U, and both zero-section equations. Its target is
  N_f ×_V N_g, canonically N_f ⊕_U f* N_g.
- `CompatibleCentredChart` records an open neighbourhood of the actual diagonal,
  a section factoring Δ through it, etaleness of its actual coordinate differences,
  and the Cartesian square with the standard zero section. It does not identify
  the whole zero fibre in the unreduced self-product with Δ. These centred data
  exist for all three charts in `CompatibleDncEquations`, independently of any
  twist-transport witness.
- `CompatibleDncEquations` first uses the recorded `DiagonalPasting.Statement`
  and `ChartEquation`: alpha_gf kappa = sigma(alpha_f tensor f*alpha_g), together
  with their canonical open-restriction and difference-coordinate assertions.
  Sigma and kappa are the recorded exceptional-adjunction maps.
- For h=f,g,gf the next three equations are exactly theta_h = beta_h delta_h
  alpha_h inverse, using `diagonalDualizingObject` and `chartDiagonalAssembly`.
  The statement quantifies over all normalized twist transports t, without
  adding existence of a purity arrow as a hypothesis.
- `CompatibleCentredChart.source` is open restriction followed by the inverse
  normalized etale exceptional restriction from the standard zero pair.
  `chartNormalCoordinateComparison` independently uses the actual conormal/
  symmetric-algebra/Rees coordinates. The following three conjugation equations
  assert delta_f=1, delta_g=1, delta_gf=1 in these very coordinates. Pulling the
  g equation by f gives the stated identity on the U standard invariant.
- `compatibleStandardBaseChange` is the actual zero-section smooth-base-change
  comparison. `compatibleStandardPullback` inserts the comparison-site pullback
  constraint. `compatibleNu` is precisely the recorded `DiagonalPasting.nu`
  transported by the strong monoidal etale/pro-etale comparison. It uses no
  orientation or twist identification. Its source and target are D_d tensor D_e
  and D_(d+e) on U.
- `compatibleKappa` transports the recorded kappa from its etale presentation
  back to the actual pro-etale source sections, retaining both `sourceComparison`
  factors and the pullback comparison for the second factor. The penultimate
  equation in `CompatibleDncEquations` states kappa=nu after the specified source
  comparisons. The last equation states (dagger), delta_gf kappa =
  nu(delta_f tensor f*delta_g), in the specified actual normal coordinates.
- `composition_compatible_dnc_charts` asserts all these equations on every affine
  compatible chart triple. `compatibleNu_etale_restriction` explicitly states
  the canonical commuting square for nu under further etale (including open)
  base restriction, with monoidal pullback and both zero-section base changes.
  `compatibleDelta_etale_restriction` gives the corresponding square for the
  conjugated actual delta. Assemblies use the recorded orientation restriction
  comparisons; kappa uses the recorded pasting open comparison. Together with
  the local equation on every etale chart, these give restriction compatibility
  of the normalized assembly. There is no arbitrary coordinate trivialization.

Dependency declarations read and used (names below are under
`WeilConjectures.PurityFiniteSetting` unless qualified):

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Coefficient`.
- Mathlib `Morphisms.Smooth`, `Morphisms.Etale`, `Morphisms.FiniteType`,
  `Morphisms.Proper`/`Separated`: `Smooth`, `SmoothOfRelativeDimension`, `Etale`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`. The node records proper
  morphisms too, but no `IsProper f` hypothesis is used here.
- Mathlib `Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections,
  diagonal, universal lift and map; Mathlib `AlgebraicGeometry.AffineSpace`:
  `AffineSpace`, projection and base-change square, with `ULift (Fin r)`.
- `Sheaf.Paper.DerivedPullbackTensorHom` and the published finite-coefficient
  pro-etale derived modules: derived pullback and tensor, via the recorded
  dependency presentations. `ConstructibleExceptionalAdjunctionCoefficients`:
  the recorded `ConstructibleExceptionalCoefficients.System`; its finite
  exceptional object is used through `diagonalDualizing` and the DNC interfaces.
- `PuritySectionInvariantIntrinsic`: `sectionInvariantFinite`, used through
  `Dnc.sourceSection` and `sourceComparison` in `PurityDncComparisons` and
  `PurityDncInvariance`. `Dnc.pullComparison` is the canonical site transport.
- `PurityNormalProjection`: `Scheme.Hom.purityNormalProjection`;
  `VectorBundleZeroSection`: actual symmetric total space and augmentation.
  Their interfaces enter through `chartNormalCoordinateMap` and its spec.
- `PurityDiagonalBaseChangeCompared`: `comparedDiagonalBaseChange`, through
  `chartDiagonalAlpha`. `PurityDncInvariance`: `Dnc.existsUnique_dncInvariance`,
  through `chartDiagonalDelta`. `VectorBundlePurity`: integration-normalized
  bundle purity, through `chartDiagonalBeta` and its dependency normalization.
- `IntrinsicCoefficientTwistsUnrestricted` and `PurityDiagonalDualizingObject`:
  `diagonalTwist`, `diagonalDualizingObject`, its unique counit normalization.
- `PurityDiagonalSectionPasting`: `DiagonalPasting.Statement`, `ChartEquation`,
  `kappa`, `nu`, `zeroInvariant`, `geometryProperties`, `first`, `q`, `A`, `pr`,
  `zero`, `affineDimension`. All these are the recorded maps, not new versions.
- `DiagonalDncChartNormalization`: `chartDiagonalAssembly`,
  `chartSourceCoordinateComparison`, `chartNormalCoordinateComparison`,
  `chartNormalCoordinateMap`, `chartNormalCoordinateMap_spec`,
  `chartStandardSection`, `chartCoordinateDifferences`.
- `AffineDifferenceTowerFactorization`: `exists_compatible_charts`,
  `factorization` (proof imports). `DiagonalRegularPureCodimension` and
  `RelativeTangentBundle` are proof imports. The unstated sigma-locality node
  has no importable module; its argument is described in the proof docstrings,
  and no replacement or circular prerequisite is introduced.
- `ComparisonMonoidal`: `ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`;
  finite derived pullback monoidality: `ProEtale.leftDerivedUpperStarTensorIso`.
  Generic helper declarations fix coefficient structures before specializing,
  avoiding expensive comparisons of concrete monoidal instance terms.

Edge cases checked: X empty makes the cover assertion vacuous; the local suite
allows empty affine schemes and arbitrary modules, including zero. d=0, e=0 and
both zero use empty Fin blocks throughout, with canonical zero-rank unit
comparisons as in the normalization dependency. An etale chart of degree >1
requires the centred neighbourhood; it is never assumed that coordinate
differences cut out only the diagonal on the whole self-product. There is no
absolute separatedness assumption on X,Y,Z, no ramification divisibility
assumption, and no restriction on positive coefficient levels. Site universes
are unchanged: Scheme.{u}, small site objects in u+1, coefficient modules in u+1.

Searches: the sandbox `searches.jsonl` retains the actual launcher search results.
LeanFinder query "compatible etale charts for composable smooth morphisms and
normalized deformation to normal cone section pasting" returned eight generic
etale/composition results, no match. Loogle query
"AlgebraicGeometry.SmoothOfRelativeDimension, AlgebraicGeometry.Etale" returned
three zero-dimensional equivalences, no match. Grep query
"compatible.*[Cc]hart|[Dd]nc|[Dd]eformation.*[Nn]ormal" in Mathlib AlgebraicGeometry
returned no hits. LeanSearch "smooth composite compatible etale charts split
tangent sequence normalized diagonal deformation normal cone" returned eight
smooth/composition results, no match. Additional rg of project Sheaf and upstream
WeilConjectures, and grep of the exact blueprint ID in WeilConjectures, found no
existing declaration for the combined statement. The generic composition
coherence theorem is downstream, not an exact match for this local chart lemma.

Validation: all compilation uses the prescribed `scompile.py`, with no local or
global build. Earlier timeout probes were superseded by successful full-module
compiles. No warnings are accepted except the stage's expected sorry warning.

## Second reading by Q75

Self-check only: the dispatch explicitly forbids starting another agent; an
independent maintainer review remains required. Reopened the current node,
source proof and final Lean file and matched every hypothesis and clause as
listed above. Found and repaired missing restricted-chart interface witnesses,
the normal splitting's projection to U, and explicit standard-pasting/DNC
restriction equations. Moved existence of centred neighbourhoods outside the
quantifiers over normalized presentation data. Checked the arrow order in
(dagger): kappa first, then delta_gf then normal coordinates; on the other side
tensor delta_f with f*delta_g, then the normal coordinate comparisons, then nu.
The g base-change comparison is included and no arbitrary map replaces it.
The node statement, proof, statement dependencies and proof dependencies are
unchanged. No STATEMENT-DISPUTED flag is warranted by these checks.
