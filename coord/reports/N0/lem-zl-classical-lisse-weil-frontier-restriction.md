## Worker report

The module states the full normalized classical Weil restriction and finite-field frontier
assertion. It proves nothing: the main postponed theorem is
`WeilConjectures.ZlFrontier.classical_lisse_weil_frontier_restriction`, with `sorry` and
the complete six-step natural-language proof in its docstring. Every definition has real data.
The natural-language item statement is unchanged. Five definition nodes own the interfaces, concrete canonical maps and re-exported
local comparison definitions used in its signature; no existing dependency is redefined.

Hypothesis and clause correspondence:

- The finite field, chosen closure and q=p^a are `D : FiniteFieldDatum`; the coefficient
  prime is `l`, `[Fact l.Prime]`, `[Fact (l ≠ D.p)]`. The algebraically closed coefficient
  field is `Ω : Type (u+1)` with `Field`, `Algebra ℚ_[l]`, and `IsAlgClosure` instances.
  Finite classical coefficient fields are actual subfields of Ω, whereas their sf
  versions use the recorded `Coefficient.{u}` and canonical Shrink equivalence.
- `Y₀ : Over (Spec k₀)` with `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`
  is exactly separated finite type. `fiberBase D Y₀` is its actual geometric fibre.
  `supportBase ... reduced` is literally that fibre or its nilradical subscheme;
  `supportInclusion` is the corresponding actual immersion. No reduction of M is assumed.
- `M : sfCommonStageHeart ...` is the recorded heart object. `PartitionData.partition`
  is the recorded finite locally closed partition, and `.reduced` makes every domain
  reduced. `stratumBase` has the induced structure map, not a replacement scheme.
- `PartitionData.classical` is the supplied classical system; `.field` is one common E;
  `.lattice` is its chosen finite-free integral tower regarded in RawRational;
  `.localization` identifies that chosen model with the supplied classical object;
  `.realization` identifies its realization with the actual derived restriction of M.
  `PartitionData.identification` composes these specified identifications.
- `Realization.models` uses the existing inverse-limit/rationalization model bundle;
  `.fullyFaithful` is precisely the given fully faithful Hom assertion.
  `S : CompletedLisse.System` includes the quotient, completion-projection, fraction,
  coefficient and composition normalization equations. `A : LisseRealization.Family`
  includes finite coefficient extension, mixed comparisons, point sections and all
  automorphism transports. `RestrictionComparison` connects them: `coefficient_values`
  fixes continuous coefficients by Shrink pointwise, `sheaf_linear` fixes their action,
  `stage` compares actual model inclusions, and `unit_square` pins the finite pullback
  by the universal ordinary unit. No arbitrary pullback map replaces these constructions.
- The first conjunct of `RestrictionConclusion` quantifies over every m≥1 and every
  `RestrictionModel`: the latter is an actual locally closed map over k_m, with an
  actual locally closed geometric factorization through a supplied stratum, and `hj`
  identifies that map with canonical base-change associativity into Y.
- `WeilRestrictionResult.square` is j g_Y^m = g_V j. `ambientRestriction` is exactly
  inverse c_(gV,j), equality-of-morphisms, c_(j,gY^m), then j*(theta^[m]);
  `constantExtensionWeilIterate` supplies the actual iterate. `WeilLift.realizes` and
  `.realizes_inverse` retain both arrows. No global lisse model of M is used.
- `AutomorphismComparison.unit_normalized` fixes the classical reindexing comparison
  on actual finite-level units and `.algebraic_normalized` rationalizes that integral
  comparison. `FinitePairRepresentation` uses canonical coefficient arrows into one
  enlargement of E. Its `pair : ... ≅ ...` contains both finite inverse equations,
  and `hom_equation` / `inv_equation` identify precisely the given classical maps.
- `WeilRestrictionResult.pointModel` is a finite sf Weil model, and
  `.realizedPointModel` identifies its included Weil structure with the actual
  restricted one. `.finitePoints : ZlClassicalFibreComparison` supplies the equation
  with the **actual** `localFrobeniusCohomology` for every positive iterate and return
  path. `.points` now fixes **that very comparison**:
  `finitePoints.fibre x = finiteRealizationFibreIso ... x ≪≫ R.identifiedFiber ... ρ`.
  Here `ρ` is `V.identification` followed by the underlying inverse of
  `realizedPointModel`. The left bridge is constructed solely from the sf point
  normalization, exact H0/sections/tensor maps, normalized completed pullback,
  `R.models.fiber_integral` and `R.models.comparison` unit. The right bridge is the
  already recorded realization identification. Thus the local-operator square uses
  precisely the normalized realization fibre, without an arbitrary point iso.
  No classical operator is used to define the left bridge. The point field contains
  the finite inverse-pair field. The tautological transported-classical step and its
  recursive iterator from returned head 207f84af1fd9 have been removed entirely.
- The second conjunct handles both supports and has no Weil hypothesis. `Frontier`
  supplies one `degree` and `positive`, reduced `closed` schemes, the whole-reduction
  `start`, empty `finish`, actual closed inclusions and commuting ambient maps.
  Start/finish are isomorphisms over k_m, so `empty_length` permits the length-zero
  chain without requiring syntactic equality of two presentations of the empty scheme.
- `difference_range` makes each difference exactly the complement of the next closed
  subscheme. `count`, `piece`, `piece_into_difference`, `piece_ambient`, `clopen`,
  `cover`, `disjoint`, `nonempty`, `affine`, `smooth_dimension`, `smooth`, and `connected`
  are respectively the finite disjoint nonempty smooth geometrically connected affine
  clopen pieces, with constant natural-number dimension. `zero_dimension` identifies
  each dimension-zero piece with Spec k_m as an object over that same field.
- `Frontier.geometric_piece` identifies the stratum factorization with the actual
  geometric base change of the piece inclusion. `RestrictionModel.lattice` is the
  specified operation on the original E-lattice, and the realization clause uses
  its original localization identification. `SuccessiveRestrictions` compares the
  specified raw compositor with the specified completed derived compositor. Scalar
  operations are the same `S.operation`, with its quotient and fraction normalization,
  and the mixed/field comparisons remain those in A and S.
- The final conjunct supplies a frontier for the unreduced support with the preceding
  `WeilRestrictionResult` for every one of its pieces and the SAME `H.degree`.
  The frontier is chosen before K; it does not assume any stability of the initial
  partition or of a lattice, and rational inverse maps need not preserve a lattice.

Dependency declarations used: `FiniteFieldDatum` (FiniteFieldFiber);
`generalAlgebraicallyClosedConstructibleCategory`, `Coefficient`, `inclusion`
(GeneralAlgebraicallyClosedCoefficients / AlgebraicallyClosedCoefficients);
`sfCommonStageHeart` (SfConstructibleHeart); `FiniteLocallyClosedStratification`
(AlgebraicGeometry.FiniteLocallyClosedStratification); `Scheme.nilradical.subscheme`;
`LisseAlgebraicSheaf`, `LisseRationalSheaf`, `LisseIntegralSheaf`,
`lisseCoefficientDiagramData`, `lisseAlgebraicModelFunctor`,
`lisseAlgebraicModelMap` (LisseAdicSheaves / LisseAdicFiberFunctors);
`AdicLisseCalculusModels` (AdicLisseCohomologyCalculus);
`PerAdic.Base`, `baseNoetherian`, `baseDimension` (AdicHeartPullbackFibres);
`LisseRealization.Family`, `PullNormalized` (LisseRationalRealizationData /
LissePullbackNormalization); `CompletedLisse.System`, `Operation`, `RawRational`,
`rawComp`, `rawIntegral`, `finiteEtaleUnit` (LisseCompletedSystemData);
`commonStageDerivedPullback` (DerivedPullbackTensorHom);
`sfCommonStageWeilComplex`, `sfWeilStageObject` (SfWeilSheafComplex);
`zlPullComp`, `zlFiberMap` (WeilIndSheafCategory);
`constantExtensionDatum`, `constantExtensionModel`, `constantExtensionFiberIso`,
`constantExtensionWeilIterate` (ConstantExtensionWeilHeartEquivalence);
`ZlClassicalFibreComparison`, `zlClassicalOrbitPoint`, `zlClassicalLocal` and their
helpers (ClassicalWeilFiltrationHeartTransport, now definition-owned by
`def-zl-classical-local-fibre-comparison`); `localPositivePower`,
`localFrobeniusCohomology` (LocalFrobeniusTrace);
`smooth_affine_frontier_stratification` (SmoothAffineFrontierStratification);
Mathlib `IsImmersion`, `IsClosedImmersion`, `IsOpenImmersion`,
`SmoothOfRelativeDimension`, `GeometricallyConnected`, `IsAffine`.

Edge cases checked: empty scheme/partition and a zero-length frontier; m=1;
zero-rank lattices and zero M; dimension-zero smooth geometrically connected pieces;
nonreduced Y with both support choices; a partition permuted by Frobenius;
a rational Weil map ell or ell^(-1) which need not preserve the lattice; arbitrary
positive point iterates and field enlargement before/after restriction. The classical
coefficient universe u+1 is retained, and finite sf fields use Coefficient.{u}; no
extra equality of universes is assumed.

Searches: LeanFinder classical lisse Weil restriction/frontier query returned ordinary
scheme restriction results, no match; Loogle scheme immersion query had no match;
Mathlib grep Weil/frontier had no match. The three raw searches attached to the restriction-model/map
nodes use LeanSearch, LeanFinder and grep: profinite inverse limits, ordinary module
pullbacks and no targeted match. Source rg item-id has no hit in WeilConjectures;
project rg finds the separate frontier and filtration results, not this theorem.
Blueprint search `lisse restriction` finds zero blueprint nodes. Existing normalized
model, system-operation and point-comparison notions are reused. No statement correction
or STATEMENT-DISPUTED flag is needed.

## New nodes

`def-zl-classical-lisse-restriction-models` owns
Sheaf.Paper.ClassicalLisseWeilRestrictionData. It assembles the existing inverse-limit
models, finite scalar-realization family and completed-system operations, with an
explicit continuous-coefficient and ordinary-unit normalization bridge. This is input
model data, not a theorem assuming the desired Weil lift or frontier.

`def-zl-classical-lisse-restriction-maps` owns
Sheaf.Paper.ClassicalLisseWeilRestrictionMaps. It gives the actual finite-stage/common-stage
restriction maps, supplied partition/lattice interface, canonical restricted ambient
Weil map, and finite inverse-pair representation. Both nodes cite the existing notions
and include the three search kinds and repository/blueprint duplicate checks. Their
source is BS 6.8.4, 6.8.14, 6.8.15 and blueprint paragraphs 6-7. The item gains these
nodes and the already-landed model, finite extension, compositor and point interfaces
it uses; no cycle to the item exists through any added dependency.


`def-zl-classical-local-fibre-comparison` is an `existing: true` re-export of
`ZlClassicalFibreComparison`, `zlClassicalStep`, `zlClassicalOrbitPoint`,
`zlClassicalSteps`, `zlClassicalLocal`, `zlFiniteFibre`, `zlExtendedFiniteFibre` and
`zlFiniteFibreMap` from Sheaf.Paper.ClassicalWeilFiltrationHeartTransport. The existing
filtration theorem node owned these plain definitions without a definition-node owner.
The new node supplies that owner without copying or changing Lean source. Its source is
the current blueprint paragraph 7, Weil II (1.1.8)--(1.1.10) and BS 6.8.14--6.8.15.
LeanSearch and LeanFinder returned unrelated Witt-vector/isocrystal Frobenius results;
Mathlib grep returned zero targeted hits. Blueprint search `classical fibre` returned
zero nodes. Repository rg found these exact definitions in the filtration module;
DAG rg found only their theorem record. Those raw results are recorded on the new node.

## Returned-delivery repair

Compared the retained item to the current shared main node: its natural-language statement
is identical, and only `stmt_deps` and `lean` differ. The three previous delivery modules
were absent from the read-only shared source at the prior repair; scompile.py validates the repaired sibling
modules in its private overlay against the current published library. This repair changes
the returned head 6dd56bb40cfc, rather than re-pushing unchanged work.

H2: replaced the item's definition-only theorem citations by `def-per-adic-base-stages`,
`def-dl-a1-constant-extension-data`, `def-zl-constant-extension-restriction-local-data`
and the new `def-zl-classical-local-fibre-comparison`. Added the advised
`def-wf-fundamental-representation` and `def-pod-lisse-adic-fibre-functors` citations.
In `def-zl-classical-lisse-restriction-models`, replaced its three theorem dependencies
by `def-per-adic-base-stages`, `def-real-lisse-realization-data`,
`def-real-lisse-pullback-normalization` and `def-per-lisse-completed-system-data`,
including the corresponding textual citations. The exact recorded declarations are used
through their existing modules; no theorem is re-stated as a definition.

H3 of returned head 207f84af1fd9 is repaired by option (a) requested in the return.
`finitePoints.fibre` itself is pinned, so its existing `local_operator` carries
`localFrobeniusCohomology` across the normalized point identification. The former
`normalizedWeilStep` and `normalizedWeilSteps` are deleted, including their new-node
ownership entries. Their classical conjugation could not express Step 5 and was not
an adequate repair. The new bridge is independent of any Weil structure and is not
obtained by conjugating a classical operator.

The retained item was compared to current shared main: its natural-language statement
is still identical, with differences only in stmt_deps and lean. The repair changes
returned head 207f84af1fd9; deliver2.py rebuilds the delivery on current main. The
accepted H2 owner/citation repairs are preserved. Geometry, frontier, finite inverse
pair and successive restrictions retain their accepted statements.

The additional helper theorem statements have real mathematical content and matching
clauses in the new definition nodes: equality of projection-normalized coefficient
transports, membership of the inverse integral coefficient representative, and
uniqueness of the normalized completed point comparison on bounded constructible
representatives. The final module also states the explicit equality between the two
small-coefficient presentations of its completed point-section object. Their proofs are `sorry` and their docstrings give full arguments.
In particular the chosen point comparison comes from a uniqueness characterization,
not an arbitrary isomorphism or a bare Nonempty witness. Every definition still has
real data. Empty schemes, rank zero, m=1, nonreduced Y, dimension zero, permuted
partitions and the u/u+1 universe sizes retain the edge-case checks above.
No statement correction or disputed statement is required.

## Validation

Every delivered module is compiled individually by scompile.py in dependency order.
The prescribed deliver2.py dry run and final push are performed after a clean compile.

## New nodes: repair addition

`def-zl-normalized-finite-realization-fibre` owns
`Sheaf.Paper.NormalizedFiniteRealizationFibre`. Its helpers implement the canonical
sf-to-realization fibre bridge without any Weil structure. The finite sf fibre starts
with the actual rational point fibre; `finiteSfPointIso` applies
`LisseRealization.fibreNormalization`, exact functor H0 comparisons and the literal
raw pullback integral-object identity. `finiteIntegralPointIso` uses the component
uniquely characterized by all normalized good-representative finite projections from
`IntegralCompletedComparison.Comparison`. `finiteTensorComp` is the composite
extension-adjunction mate of the identity restriction comparison, explicitly keeping
coefficient universes u and u+1. `finiteStageIso` is the recorded integral comparison
followed by the fixed coefficient-equivalence counit. Finally the inverse
`fiber_integral`, the coefficient-equivalence unit and the fibre of `finiteStageIso`
give `finiteRealizationFibreIso`. None of these maps depends on the classical Weil
map, the classical return path, or the equation it is used to state.

Searches: msearch leansearch and leanfinder for canonical finite sf/completed realization
fibre comparison returned general adic completion and tensor results; targeted Mathlib
grep returned zero. The verbatim results are in the new node. Source/DAG rg found
`sfAdicRationalFiber` and `ClassicalTwoFibre.AtStage`, whose interfaces do not provide
the required map for `AdicLisseCalculusModels`; the former is a completed fibre functor
with no R comparison, while the latter takes a different continuous realization
family and comparisons as data. `pointRationalNormalization` and the integral
completed-pullback comparison provide the existing canonical pieces reused here.
`blueprint_refs.py search 'finite fibre'` returned eight unrelated finite-morphism
or trace nodes. The new definition is cited by the item. Its dependency declarations
and modules are explicitly imported, with the exact source maps read in full.

The additional Comparison data are owned by the existing definition node
`def-pod-integral-completed-comparison-data` (module
`Sheaf.Paper.IntegralPullbackCompletedComparison`, declaration
`WeilConjectures.IntegralCompletedComparison.Comparison`, with its `integral`,
`completed`, `Complete` and projection helpers); this owner is cited directly.
The existence theorem `integralPullback_completedComparison` is used mathematically
in the proof of the unique point component, rather than cited merely to name a type.
The exactness result of `lem-weil-point-sections-scalar-extension` is used to commute
H0 and sections and fraction-field tensor. `def-real-lisse-realization-data` (through
the restriction-model owner) owns the `fibreNormalization` helper. No new definition
of these functors or their normalizations has been introduced.

## Second reading by N0: repair 207f84af1fd9

Re-read the current item statement and the six-step proof, then the corrected fields.
The first paragraph's normalized point comparisons now render as an equality for
`finitePoints.fibre`; this is the same field used in `finitePoints.local_operator`,
whose left operator is exactly `localFrobeniusCohomology` with carrier lift and scalar
extension. Its source module was read to check the exponent n+1 and all three
factors: sf point transport, return comparison and the pulled-back Weil iterate.
The bridge contains none of these Frobenius operators; its normalization therefore
does not predetermine or trivialize their compatibility with the classical side.
`V.identification` and `realizedPointModel` fix its endpoints as the return required.
Re-read every other hypothesis and conclusion against the clause correspondence:
actual theta^[m], inverse, one coefficient stage, frontier at a common degree,
nonempty clopen pieces, zero-dimensional points, both supports and successive
restrictions are preserved. H2 citation replacements and the eight-declaration
re-export remain in place. No hypothesis has been added to the main theorem.

`def-zl-normalized-finite-fibre-models` owns the component module
`Sheaf.Paper.NormalizedFiniteFibreModels`, separated from the final bridge to retain
the per-file compile limit. It owns the inverse integral representative, coefficient
counits, uniquely normalized completed point component, sf point normalization and
tensor-adjunction comparison. The final bridge node imports it and owns the completed
section object, its equality with `adicCalculusIntegralFiber`, and the fixed
`finiteModelFibreIso` and final composition. The equality helper unfolds only the two
named presentations of the same Shrink field and section construction; its full
source argument is given in its docstring. The sf coefficient model is used consistently as `Coefficient.{u}`. The PBC
field is kept inside the recorded PBC APIs; their presentation equality is explicit
in `finiteCompletedPointFibre_eq`.
Both new nodes carry the actual duplicate
search results and are cited by the item. All helper theorem clauses are explicitly
present in their owning definition statements.
