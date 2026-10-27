## Worker report

The module `Sheaf.Paper.IntegralGeometricComparisonRealization` states
`AlgebraicGeometry.ProEtale.IntegralGeometricComparison.integral_geometric_comparison_realization`.
The only postponed proof is this theorem, with the original nine-step proof and
its dependency IDs in its docstring. All helper definitions contain actual data;
structures package the clauses of this statement, not assumptions on the geometry.
The theorem constructs the tower and integral data. In particular it does not
require the user to provide an invertible exchange or a pre-existing integral
realization, and it does not restrict E to Q_ell.

Hypothesis and clause correspondence:

- `P : PurityFiniteSetting` contains the finite-field datum, its algebraic closure,
  coefficient prime different from the characteristic, and the finite subextension
  E of its chosen coefficient closure. It uses the dependency's valuation ring and
  uniformizer, not a new coefficient ring. The positive finite level in this
  bundled convention does not enter `Result`.
- `X₀`, `Y₀ : Over (Spec k₀)` and the separated, locally-finite-type and
  quasi-compact instances state exactly separated finite type for both schemes.
  `f₀` and the three corresponding instances state separated finite type of the
  model map. `d : ℕ` and `SmoothOfRelativeDimension d (P.frobeniusMap f₀)` state
  the pure-dimensional smoothness after the prescribed scalar extension.
- `Result` uses `P.frobeniusFiber`, `P.frobeniusMap` and
  `P.frobeniusGaloisMap` literally. Its `sq` is the first Cartesian square of
  `schemeGeometricFrobenius_squares`. This is the semilinear geometric automorphism,
  not the scheme-Frobenius arrow. The prime-invertibility and isomorphism instances
  inside `Result` are consequences of the conventions, not added hypotheses.
- `SpExceptionalBaseChange.IntegralCoordinates` supplies the actual simultaneous
  reduction, normalized equivalence, strict scalar/cofinal comparison and total
  limit. `red` and `lim` are the dependency abbreviations; the latter restricts
  scalars before total derived inverse limit. The fixed datum is
  `Scheme.pbcIntegralDatum`, whose coefficient universe is u+1 for schemes in u.
- The existential `b₀`, `o₀`, `q₀`, `x₀`, `c₀` and `a₀` in `Result` choose
  the existing tower operations, one compactification and its prescribed base
  change. `SpTowerMate.Data` includes F_bullet, G_bullet, their adjunctions,
  levels, and the two strict pullbacks. Its beta and mate are the dependency's
  proper/open exchange and counit transpose. No arbitrary replacement is defined.
- `Diagram.pullX`, `pullY : PullLimit` give the two natural isomorphisms on
  normalized constructible towers. `PullLimit.unit` is the reconstruction-unit
  square, using the whole-system `pullReduction` map.
- `Diagram.reindexX`, `reindexY : PurCompletedReindexingAt` include the exact
  completed-module and fixed-ring-tower inverse-image equivalences and their
  inverses along the inverse scheme arrow. They include the ordinary-limit
  comparison fixed by every projection, its derived equation on K-injective
  complexes, the coefficient action, and the reduction/transition equations.
  `injectiveX/Y` and `varyingInjectiveX/Y` additionally assert preservation of
  K-injectivity for actual completed modules, fixed-ring strict towers and
  varying-coefficient strict systems. No preservation by evaluation or scalar
  restriction is asserted.
- `Diagram.image` is F ≅ L F_bullet red. Its components are fixed by
  `s.supportModel.imageComparison`; the support model includes the actual
  quotient-generator, proper/open and reconstruction normalization.
  `IntegralData.rightLimit` and `right_reduction` give G ≅ L G_bullet red,
  and the primed fields give the same on the base-changed compactification.
- `Diagram.smooth/smooth'` use the dependency's entire `Realization` with exactly
  these reduction coordinates, tower adjunctions and levels. The two
  `reconstruction` equations identify their reconstruction package with the
  support models used in the rest of the diagram. The levels on the literal
  composite compactification are transported from the original levels, with
  `HEq` recording that transport. All required quasi-compactness and
  compactification instances are derived internally from the existing data.
  `Diagram.independent` is
  the counit equation for the canonical `rightAdjointUniq` comparison to any
  independently supplied integral exceptional right adjoint of this same F.
- `TateComparison.realization` is H ≅ L H_bullet red, fixed by the
  reconstruction unit and `SourceModel.comparison`. `SourceModel.normalization`
  fixes that entire strict comparison to `nativeComparison` followed by the
  section-normalized cofinal pullback/tensor comparison. The shift data and
  Tate-reduction data retain the actual quotient-unit and signed-line formulas.
  `native_pull_normalization` fixes the native whole-system comparison to the
  actual Roos-normalized pullback model followed by the reduction/limit counit.
  It does not choose a tower map merely from prescribed finite evaluations.
- `Diagram.gamma/gamma'` are natural isomorphisms. Their component equations
  identify them with the dependency's literal unit/limit/gamma word, followed by the
  canonical counit-preserving identification of the reconstructed right
  adjoint. `SmoothGammaRealization` is equality with the reconstruction unit, total limit
  of sourceComparison followed by tower gamma, and inverse reconstruction unit.
  The displayed equality is of entire derived arrows, not of evaluated cohomology.
- The unit fields of `Diagram`, the counit fields of `IntegralData`, and
  `Realization.unit_limit/counit_limit` fix eta and epsilon to the actual
  tower unit and counit and their total-limit realizations, on both copies.
  `HEq` in the two unit fields expresses equality of the same derived arrows
  without asking elaboration to unify their large endpoints prematurely.
- `TateComparison.towerComparison` has components exactly `towerTateWord`:
  exact-pullback shift, tensor pullback, the actual square, and `towerTate`.
  The latter is the whole reduction of
  `FrobeniusCoefficientTwists.integralDerivedLineMap` with the specified
  pullback-reduction comparison and section-realization counit. That line map
  is the published inverse limit of root maps and their tensor powers.
  `TateComparison.comparison` is b; `reduction` identifies it with this whole
  ordered tower word, including the specified source reductions.
- `Diagram.beta` has the required P F ≅ F' Q direction. Its
  `exchange_reduction` is exactly `exchangeReduction`, the canonical ordered
  word of pullback comparisons, support comparisons and `SpTowerMate.beta`.
  `CompletedExchange.equation` identifies this same beta with the actual
  `Scheme.completedCompactSupportExchange` after coefficient transport, for
  every finite generating tuple of the ideal. Its upper compactification map
  is fixed by `gbar_eq` to the actual pullback projection.
  `CoefficientTransport.support`
  is normalized to the proper/open scalar-restriction mate; `pull` is fixed
  by the ordinary comparison, the unique counit-normalized
  `cbcDatumOrdinaryTransport`, and the completion augmentation. The scalar
  equation compares the underlying RingCat morphisms using `adicLisseForget`. Thus these
  transports cannot be rescaled to disguise a different exchange map.
- `Diagram.exceptional` is a natural isomorphism. Its
  `exceptional_reconstruction` and `exceptional_limit` identify its components
  with the reconstructed entire tower mate e_bullet and its explicit adjunction/
  total-limit formula. `exceptional_transpose` identifies those same components
  with `integralTranspose`, the adjunct of beta inverse followed by P(epsilon).
  These equations between components of natural transformations state the entire
  diagram identification, without faithfulness of finite derived evaluation.

Dependency declarations read and used (module followed by declaration):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Sheaf.SixFunctors.SchemeGeometricFrobenius`: `WeilConjectures.PurityFiniteSetting.schemeGeometricFrobeniusComparison`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: `WeilConjectures.finiteTorConstructibleEtale`.
- `Sheaf.Paper.SmoothPurityNormalizedEquivalence`: `AlgebraicGeometry.ProEtale.sp_normalized_equivalence`.
- `Sheaf.Paper.SmoothPurityTowerGluing`: `AlgebraicGeometry.ProEtale.SpTowerGluing.tower_gluing`.
- `Sheaf.Paper.SmoothPurityTowerGamma`: `AlgebraicGeometry.ProEtale.SpTowerGamma.tower_gamma`.
- `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange`: `AlgebraicGeometry.ProEtale.SpExceptionalBaseChange.tower_exceptional_base_change`.
- `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`: `WeilConjectures.FrobeniusCoefficientTwists.rationalWeilTwistingFunctor`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `WeilConjectures.IntegralOnSlice.completedTensor`.
- `Sheaf.Paper.IntegralDirectImageTower`: `AlgebraicGeometry.ProEtale.IntegralDirectImageTower.integral_direct_image_tower`.
- `Sheaf.Paper.IntegralAdjunctionBijection`: `AlgebraicGeometry.ProEtale.SpIntegralAdjunction.integral_adjunction_bijection`.
- `Sheaf.Paper.CompletedCompactSupportExchange`: `AlgebraicGeometry.Scheme.completedCompactSupportExchange`.
- `Sheaf.Paper.PurityCompactSupportTransport`: `WeilConjectures.Purity.finiteCompactSupportWeilTransport`.
- `Sheaf.Paper.PurityTateDatum`: `WeilConjectures.Purity.CondensedStrictWeilDatum`.
- `Sheaf.Paper.PurCompletedReindexingData`: `AlgebraicGeometry.Scheme.purReindexingTestSquare`.
- `Sheaf.Paper.IntegralCompletedCoefficientTransport`: `AlgebraicGeometry.Scheme.integralDetailedTransport`.
- `Sheaf.Paper.ProperIntegralOrdinaryData`: `WeilConjectures.PbcProperIntegralPullbackIdentification` (in the owning definition node's declarations).
- `Sheaf.Paper.IntegralCompactSupportCoefficientData`: `WeilConjectures.PurCompactSupport.completed`.
- `Sheaf.Paper.IntegralCompactSupportCoefficientData`: `WeilConjectures.PurCompactSupport.Coefficients`.

- `Sheaf.Paper.CompletedPullbackTensorComparison`: `WeilConjectures.pullbackTensorIntegralPullbackModel` and its normalization data.
- `Sheaf.Paper.CompletedOpenExchangeTransport`: `AlgebraicGeometry.Scheme.cbcDatumOrdinaryTransport`, the unique counit-normalized comparison to the ordinary inverse image.

Edge cases checked before stating: d=0 uses the coefficient unit and zero shift;
no positive-relative-dimension hypothesis is added. Empty schemes and zero
constructible objects remain admitted. The first tower index n=0 means exponent
one; no zero quotient is mistaken for it. Arbitrary ramification is retained by
the cofinal models, not replaced by e=1. E is not forced to have degree one.
Ideal generators are universally quantified, including the empty tuple when it
presents the ideal. Frobenius is semilinear and the source copies can be retagged;
no k-linearity instance is imposed on either g_T. The full small-site module
universe is u+1 throughout.

Searches performed:

- msearch LeanFinder, `Realization derived inverse limit integral geometric
  Frobenius comparison diagram purity adjunction`: eight unrelated hits,
  including scheme factorization lemmas and `Condensed.profiniteSolidCounit`;
  no exact diagram-realization theorem.
- msearch Loogle, `CategoryTheory.Adjunction, CategoryTheory.NatIso`: the service
  reported unknown identifier `CategoryTheory.NatIso`; this query supplied no
  usable result and is not counted as evidence of absence.
- msearch Mathlib grep, `KInjective|rightDerivedFunctorComp` in CategoryTheory:
  nine hits in Ext and PointwiseRightDerived. These provide generic category
  theory, not the specified integral geometric diagram.
- rg of WeilConjectures and Sheaf for the item ID and integral/geometric
  realization names found the individual interfaces used above, not the combined
  theorem. Further targeted rg/read searches located `IntegralCoordinates`,
  `PullModel`, `IntegralData`, `Realization`, `gammaComponent`,
  `PurCompletedReindexingAt`, `PbcProperIntegralPullbackIdentification`, the
  canonical root-line map and the scalar-restriction support mate. The module
  reuses these rather than defining second copies.
- The DAG records were searched by module and declaration. Six landed definition nodes
  are added to stmt_deps for the extra interfaces used in the signature, together
  with the two existing-declaration ownership nodes described below. The containing
  extension-zero theorem is not a statement dependency.

The original statement, proof, source and proof_deps are unchanged.

## Second reading by ND

A separate rereading by this same dispatcher worker compared the original node
and the module, with both open. The dispatcher explicitly prohibits starting
other agents, so this is not represented as a second independent agent's review.
The maintainer's independent review remains required.

This pass checked each clause listed above. It caught the need to make the
completed-exchange comparison an equality with the actual completed map, rather
than just an invertibility assertion; the coefficient transport and
`CompletedExchange.equation` were added. It also caught that a pointwise
exceptional reconstruction did not yet state naturality; the output now includes
`exceptional` as a natural isomorphism. The varying-system K-injective clause and
the primed purity and unit clauses were added explicitly. The actual geometric
square and the general finite extension are retained; the degree-one restriction
in the older exceptional-base-change theorem is not imported into this statement.

A further source-interface check replaced the initially referenced existential
`integralPullbackSystemComparison` witness by `SourceModel.nativePull`, with an
explicit whole-system normalization to `pullbackTensorIntegralPullbackModel` and
the reconstruction counit. Finite derived evaluation is not used to specify that
map. This is a literal helper for the owning statement, not a second pullback.

The final purity equation is a Prop-valued normalization predicate using
`SpIntegralAdjunction.Realization` directly. No second purity map is defined.
The additional raw-rationalization presentation import was therefore removed.

Validation: `scompile.py ND lem-pur-integral-geometric-comparison-realization
lean/Sheaf/Paper/IntegralGeometricComparisonRealization.lean` completed cleanly
in sandbox mode (23.4 s) and library mode (21.4 s), with no diagnostics.
The delivered module has no profiling options, one named theorem with `sorry`,
and no postponed data. Local irreducibility of `Scheme.residueField` avoids
expanding unrelated residue fields during instance search; no universe equality
or geometric hypothesis was added to improve compilation.

## Returned delivery repair H2

The independent maintainer review of immutable head `dd3cc2a4f21b` accepted the
mathematical clauses and returned only definition ownership. The previous extra
statement dependency `lem-cbc-completed-extension-zero-comparison` has been
removed. Two new definition nodes below own the actual declarations used by
`CoefficientTransport.pull_normalization` and `CompletedExchange.complete`.
Both have `existing: true`; no construction is copied or replaced. The ordinary
node also records the unique-existence theorem that determines its chosen
isomorphism and the two ordinary-functor equality helpers. The existing tower
transport node supplies the generic resolving-counit normalization predicate.
The complete-object node supplies the literal intrinsic-completeness property
on the canonical localization representative. Both nodes are now direct
statement dependencies. The module explicitly publicly imports both owning
modules. The main theorem, all helper bodies, and all mathematical hypotheses
and conclusions are unchanged.

The current shared item was compared with the retained returned packet: the
only existing-node changes remain `lean` and authorized additions to
`stmt_deps`. Delivery tooling rebases the repaired packet onto current main.
The advisory about existential tower packages and the general-E proof obligation
does not request a statement change. The maintainer's independent reading
confirms the clauses, including the edge cases and universes. No second worker
is claimed; the dispatcher still forbids starting another agent.

## New nodes

`def-cbc-completed-ordinary-counit-transport` records the existing
`AlgebraicGeometry.Scheme.cbcDatumOrdinaryTransport_exists` and
`AlgebraicGeometry.Scheme.cbcDatumOrdinaryTransport`, together with
`cbcDatumModulePull_eq` and `cbcDatumModulePullComplex_eq`, in
`Sheaf.Paper.CompletedOpenExchangeTransport`. The construction compares the
ordinary total derived pullback with the datum's exact derived pullback, uniquely
normalized by the resolving counit on every representative. Its source is the
published construction (Stacks 099N, 06YS) and the canonical pullback/reduction
identification used in the latest blueprint integral-adjunction proof,
Bijections/Purity and geometric comparison Steps 4/8. LeanSearch returned generic
`Functor.leftDerivedUnique` and related universal-property lemmas; LeanFinder
returned generic exact-derived factorization comparisons. Mathlib grep found no
specialized ordinary transport. Project grep found the exact published
construction. The DAG declaration-ownership audit found only its theorem-node
record, and `blueprint_refs.py search cbcDatumOrdinaryTransport` returned zero.
This node registers its existing construction without using the containing
extension-zero theorem. No isomorphism assumption on the scheme map and no
completeness assumption is added; the unique normalization rules out rescaling.

`def-cbc-intrinsic-complete-property` records the existing
`AlgebraicGeometry.Scheme.cbcCompleteProperty` in
`Sheaf.Paper.CompletedExtensionZeroComparison`. It evaluates the existing
intrinsic-completion predicate at `DerivedCategory.Q.objPreimage K` with
`DerivedCategory.Q.objObjPreimageIso K`, retaining the chosen ideal generators
and generation equality. Its source is the published predicate and the latest
blueprint integral-adjunction proof's derived-complete normalization/reconstruction
unit. LeanSearch and LeanFinder returned generic derived-category and
cohomological-support predicates, not this completeness construction. Mathlib
grep found no `IsDerivedCompleteIntrinsic` or `cbcCompleteProperty`. Project grep
located the literal definition; the DAG audit found no definition-node owner,
and `blueprint_refs.py search cbcCompleteProperty` returned zero. The empty tuple
is retained when it generates the ideal. Scheme universe t and coefficient/module
universe t+1 are retained. Both new nodes carry the actual recorded searches.

Repair validation: `scompile.py` compiled the repaired module cleanly in sandbox
mode (24.8 s) and library mode (22.3 s), with no diagnostics. The two ownership
records are existing declarations, so they introduce no new Lean modules.
