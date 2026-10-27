## Worker report

The module `Sheaf.Paper.CoordinateLineAdjunction` states
`AlgebraicGeometry.ProEtale.CoordinateLine.coordinateLineAdjunction`. Its proposition
`CoordinateLineStatement` collects the clauses of the existing DAG statement. The
ordinary maps are constructed, rather than selected from a mere existence assertion.
The new canonical-map module is owned by the definition node below.
There is one postponed theorem, with the complete six-step node proof in its docstring.
The node's statement and split are unchanged.

Hypotheses and clauses:

- The finite-field datum, coefficient prime, finite subextension of the fixed coefficient
  closure, uniformizer quotient, and positive coefficient level are exactly
  `P : WeilConjectures.PurityFiniteSetting.{u}`. `AffineLinePurity.Ring P` is the published
  `finiteTateCoefficient` at zero-based index `P.level - 1`; `ringEquiv` identifies it
  with `P.Coefficient`. This is the existing quotient and its standard size lift.
- `aT : T ⟶ Spec (.of P.field.k)` with `LocallyOfFiniteType aT`, `QuasiCompact aT`,
  and `IsSeparated aT` means separated finite type over the specified algebraic closure.
- `r : ℕ` indexes `a=r+1`; `hA` says `ell^(r+1)` annihilates that quotient.
  `CoordinateLineStatement` quantifies over all these exponents, without ramification
  divisibility assumptions, and asserts `ell^P.level=0`, so a=n is available.
- `AffineSpace PUnit T`, `ProjectiveLine T`, `ProjectiveLine.affineChart T`, their
  structural maps, and `affineTraceLineCompactification T` are the published geometric
  objects and compactification. `Geometry` asserts Noetherianity, finite Krull dimension,
  separated finite-type projection, openness of the chart, properness of the projective
  projection, and qj=p. It applies also to every `iteratedAffineLine T d` including d=0.
- The ordered coordinate projection is `iteratedAffineLineProj`; zero coordinates use
  `Scheme.Hom.toIteratedAffineLine` with the constant zero vector, and the last section
  is `AffineSpace.zeroSection PUnit`. The three tower equations are included literally.
  Coordinate divisors are the zero-locus subschemes of `iteratedAffineLine.coord`.
  Their inclusions have invertible kernels for every base scheme B, so all base changes,
  including nonreduced ones, are covered.
- `Scheme.finiteEtaleTateSheaf` is the recorded roots-of-unity coefficient extension,
  signed powers and duals. The local etale-cover trivializations assert rank one for all
  signed powers. `IsFiniteTateSiteComparison` at the canonical `twistComparison`
  asserts the root-normalized comparison with the specified Tate powers. The shifted line `line` is the canonical chart restriction of the
  published ordinary projective line coefficient, as in `AffineLinePurity.etaleCoefficient`.
- `right` is `ordinaryFiniteTwistedPullback` for p and that shifted restricted coefficient.
  `rightComparison` is tensor pullback followed by inverse-image composition. Its use
  of the restricted line is canonically identified with L_X[2] by the published
  roots-normalized Tate pullback. `adjunction` composes the actual open adjunction
  and the trace-normalized projective adjunction and transports the right side by this
  specific comparison.
- `integration` is Rq_* of the actual open counit followed by `projectiveLineTrace`.
  `projection` is precisely `projectionMapOfCompactification` conjugated by the two
  tensor symmetries specified in the affine-line comparison convention.
  `CounitNormalization` asserts an isomorphism whose hom is this exact projection and
  says the actual counit is its inverse, tensor integration, and `derivedTensorSingleUnitIso`.
  K is restricted by the existing ordinary `constructibleFiniteTor` predicate.
- `exceptionalAdjunction` is `Adjunction.ofIsLeftAdjoint` at the literal standard
  compactification. `comparison` is `conjugateIsoEquiv` of the identity of its left
  functor, thus a natural isomorphism, not only an isomorphism of objects.
  `NormalizedOrdinary` includes its counit-preservation equation and the equation
  identifying its component with the transpose of the calculated counit.
- `sourceCoordinates` identifies the published ordinary affine-line source with the
  right functor. `comparedConjugate` uses the inverse of `sourceComparison`, comparison
  pullback of the ordinary conjugate, `boundedSiteRho` (the actual comparison-unit map),
  and the exceptional image of the supplied realization eK. The theorem identifies
  this arrow with the existing `affineLinePurityComparison` and asserts its invertibility
  for every retained ordinary finite-Tor origin Ke and every realization eK. This is
  exactly the existing input interface of gamma; the recorded finite-Tor comparison
  equivalence supplies those origins for every pro-etale D^b_ctf input.
- `sourceExponentIso` goes through the specified inverse-limit coefficient line using
  `coefficientTwistIso` at the two exponents. The final equality asserts equality of
  the actual gamma arrows after this canonical source comparison, with arbitrary
  r and r', so no ordering or divisibility of their indices is imposed.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its
  coefficient data; `Sheaf.Paper.AffineLinePurityComparison`: `Ring`,
  `affineLinePurityComparison` and the actual source and augmentation maps reexported
  from `AffineLinePuritySource` and `AffineLinePurityCoordinateMaps`.
- Mathlib `AlgebraicGeometry.Morphisms.FiniteType` and `.Proper`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsProper`.
- Mathlib `AlgebraicGeometry.AffineSpace`: `AffineSpace`; upstream
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`: `ProjectiveSpace`, `ProjectiveLine`.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `Scheme.etaleFiniteTwistPullback`,
  `finiteEtaleTwistPullbackData`; `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`
  reexports the fixed finite signed twist and its inverse-limit normalization.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedLowerShriekOfCompactification` (Dj_! followed by Rq_*).
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`:
  `Etale.exists_ordinaryFiniteP1Adjunction`, with its uniquely normalized transport
  and projective datum selected by the existing projective-trace API.
- Mathlib `CategoryTheory.Adjunction.Basic`: `Adjunction.comp`; `.Mates`:
  `conjugateEquiv`, `conjugateIsoEquiv`.
- `Sheaf.AlgebraicGeometry.AffineTraceConstruction`:
  `affineTraceOpenAdjunction`, `affineTraceLineAdjunction`, `affineTraceLineLeft`,
  `affineTraceLineRight`, and the literal standard compactification reexported from
  `AffineTraceTower`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` reexports the specified
  finite exceptional inverse image; its fixed-coefficient declaration is
  `ProEtale.sfFiniteExceptionalAt` in `FixedFiniteExceptionalAt`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`:
  `Etale.isIso_finiteCompactProjection` and the recorded canonical compact projection map.
- `Sheaf.Paper.VectorIntegrationSiteComparison`:
  `finiteTypeSiteComparison`, `twistCompatibility`, the actual projective/open/tensor
  comparisons, and `boundedSiteRho` reexported from `BoundedSiteAdjunctionTranspose`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`:
  `finiteTorComparisonNoetherian`; upstream finite-type module:
  `AlgebraicGeometry.exists_topologicalKrullDim_le`.

Edge cases checked: empty T (Krull dimension bottom admits a natural bound), zero K,
r=0 (a=1), arbitrary positive coefficient level including n=1, ramified E (ell=varpi*b,
so ell^n=0 without requiring e|n), coordinate tower of dimension zero and identity zero
section, and nonreduced base rings (multiplication by a polynomial coordinate is injective
coefficient by coefficient). No reducedness, smooth base, flat coefficient extension,
independent universe restriction, or exceptional-adjoint admissibility datum is assumed.
The small sites and ModuleCat coefficients retain universe u+1 over Scheme.{u}.

Searches: the sandbox `searches.jsonl` records the actual msearch results. LeanFinder
queries for the normalized affine-line compact-support adjunction and its counit gave
only generic scheme/module adjunctions. Loogle `CategoryTheory.Adjunction.comp,
CategoryTheory.Adjunction.counit` returned `comp_counit_app`, `comp_counit_app_assoc`,
and `comp_counit`; the conjugacy query returned general mate identities. Mathlib grep
`affine.*(adjunction|trace)|TateTwist|kummer` in AlgebraicGeometry found only the affine
scheme module. LeanSearch for the finite torsion affine-line adjunction with normalized
trace returned scheme-kernel/condensed adjunctions and field normalized traces. None
states this node. Direct rg searches of both `lean/WeilConjectures` and `lean/Sheaf`
for the node id and proposed full declaration found no existing statement. Existing
partial constructions above are reused. The missing combined canonical-map interface is supplied in the new definition node below;
no dependency repair is needed.

Validation: compilation and prescribed delivery preflight are recorded by the launcher
wrappers; only the single theorem's expected sorry warning is permitted.

## New nodes

`def-pur-coordinate-line-adjunction-maps` owns
`Sheaf.Paper.CoordinateLineAdjunctionMaps`. It defines the literal transported
composite adjunction, integration and projection arrows, identity conjugate, and
site-compared conjugate used by this theorem. The earlier project supplies the
pieces (`AffineTraceConstruction`, `AffineLinePuritySource` and the site comparison),
but does not define this combined canonical interface. The new module reuses all
those pieces. It also caches tensor source identifications and the ordinary
normalization predicate before coefficient specialization, so that the kernel need
not repeatedly unfold derived-category implementations. Every definition has real
data; there are no new postponed helper theorems.

The source is the first ordinary-adjunction sentences and final transpose paragraph
of `cor-pur-affine-space-zero-section-purity.proof.md`, main-20261015. Blueprint
search for “coordinate-line adjunction” found no matching unit. Project rg searches
for the proposed namespace/maps found none. Mathlib grep `affineTraceLine|coordinateLineAdjunction`
returned zero hits. LeanSearch and LeanFinder on the actual composite trace adjunction
and its Brown conjugate returned generic adjunctions only. Loogle found the generic
`conjugateIsoEquiv`, which is used directly. No canonical map is replaced by an
arbitrary arrow or a mere Nonempty choice. The item adds this node to stmt_deps.

The full theorem proof is postponed. Both modules compile separately in dependency
order through scompile.py; earlier expensive definitional equalities were replaced
by the dependency's published coordinate equalities and generic cached constructors.
The `IsNoetherian T` argument in `NormalizedAdjunction` is quantified in the conclusion
and supplied by the separate `Geometry T` conjunct, not assumed by the theorem.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
