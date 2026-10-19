## Worker report

The module `Sheaf.Paper.ScalarExtensionTowerCoherence` states the node by its
strict-system, representative, and derived-limit clauses. No mathematical proof
has been supplied: every theorem is a named `sorry` with a source and a full
natural-language proof. Definitions contain actual data. The choices defining
`comparisons` and `derivedSigma` are from uniqueness statements with explicit
normalizations, rather than from an unconstrained existence assertion.

### Hypotheses and objects

* The binders `l`, `[Fact l.Prime]`, `E`, `L`, `[Field _]`,
  `[Algebra ℚ_[l] _]`, `[FiniteDimensional ℚ_[l] _]`, and
  `ι : E →ₐ[ℚ_[l]] L` are the prime and the finite coefficient extension.
  `composition` additionally binds `F`, its field/algebra/finite-dimensional
  instances, and `j : L →ₐ[ℚ_[l]] F`. The inherited quotient maps depend on
  these actual embeddings, with `j.comp ι` for the direct embedding.
* `f : X ⟶ Y`, or `f : W true ⟶ W false`, is the scheme morphism.
  `IsUnit (l : Γ(X, ⊤))` and its target analogue are exactly invertibility
  of the prime. There is no assumption on properness, smoothness, dimension,
  or the ramification of the coefficient extension.
* `coefficientSequenceCommRingSheaf l E W` and the analogous rings for L and F
  are the existing quotient-ring sheaves on the ringed sequence site. This
  site retains the horizontal quotient transitions and vertical restrictions.
  Its natural-number level n denotes the positive quotient exponent n+1,
  following the recorded reduction conventions. The completed coefficient
  ring is the existing `completedIntegralCommRingSheafUnrestricted` underlying
  `scalarReductionSource` and `integralTowerModules`.
* `sfIntegralConstructibleCategory l E Y` is the recorded bounded constructible,
  derived-complete category. In `quotientModels`, P and Q are in
  `integralOperationsGoodComplex.FullSubcategory`; this supplies K-flatness
  and flatness of every term. `_eP`, `_eQ` identify their localizations with
  M and N. There is no flatness hypothesis on the finite coefficient-ring map.
* `CoefficientDerivedSystemCalculus`, `CompletedOperations.Models`, the Roos
  models, and the scalar/tensor realization models are normalized presentations
  of the named operations. They are not arbitrary replacement functors or
  additional geometric hypotheses. `realizationModels` supplies the new
  tensor/scalar presentation data. Their normalizations quantify over every
  simultaneous quotient representative and use the specified cochain maps.
* The original small pro-etale site has object universe u+1 and morphism
  universe u. The explicit universe annotations preserve this difference.
  `sequenceSmall` and `siteSmall` are real existing smallness witnesses,
  selected at these precise sizes to avoid an undetermined auxiliary universe.

### Clauses

* `Complex` is just the existing cochain category of actual sequence-site
  modules. `tensor` is the existing `coefficientTotalTensor`, hence the signed
  direct-sum total with second differential sign (-1)^p. `scalar` and `pull`
  are termwise lifts of the existing quotient scalar extension and pullback.
* `kappa` is the termwise lift of
  `integralComparisonSequenceScalarPullback`, already normalized by the
  scalar-association formula. It is oriented from scalar-after-pullback to
  pullback-after-scalar, as in the displayed square in the node.
* `Comparisons.sigma` and `.c` specialize the recorded ordinary/cochain tensor
  comparison to these actual sequence-site functors. `sigma_formula` is the
  literal equation b tensor (x tensor y) maps to
  (b tensor x) tensor (1 tensor y), in each (p,q) summand. `c_formula` is the
  inverse-image adjunction-unit version of the same local formula, allowing
  every target coefficient b. These conditions uniquely determine the maps.
  This is a normalized adapter to the existing total tensor and actual
  pullback/scalar functors, not a second tensor construction.
* `quotientModels` supplies `CoefficientExtensionReductionData` for E-to-L
  and the E-to-E quotient diagrams. Its unique strict-system isomorphism δ
  sends b tensor (x tensor a) to x tensor (ι(a)*b). `modelSection` reads the
  actual finite tensor section through `directEvaluation`. The reduction
  data already include the actual quotient transitions, normalized coherent
  systems, derived comparison counits, and their completion projections.
* `leftRoute` and `rightRoute` are precisely the two composites in the node's
  displayed square. `square` equates them as natural isomorphisms on whole
  quotient systems. `quotientModels` also specializes that equality to the
  actual representatives of M and N. Equality of isomorphisms includes their
  inverses; sequence-site module morphisms retain all quotient transitions.
* The generator equations in `Comparisons`, together with the defining
  normalization of the existing `kappa`, express the asserted common local
  formula for the two routes. All maps preserve bidegree, so the sign of the
  total differential is retained.
* `unit` states the identity-extension equations after the actual scalar
  action unitors `scalarUnit`. `composition` states both the kappa and sigma
  equations for E-to-L-to-F, under `scalarComp`, the existing multiplication
  associator. These are strict-system natural-isomorphism equations.
* `DerivedSigmaModel` requires the derived scalar/tensor comparison to be
  exactly the localization of `Comparisons.sigma`, using the existing scalar
  derived counits and the recorded tensor model isomorphisms. It also states
  preservation of the flat-term K-flat representative class. Thus
  `derivedSigma` is not an arbitrary derived isomorphism.
* `IsTensorModelNormalized` fixes the completed tensor realization by its
  local finite-tensor formula and its equality with the named
  `integralCompletedTensorComparison` after the normalized Roos bridge.
  The analogous pullback and scalar normalizations are imported unchanged.
* `pullbackReduction`, `scalarReduction`, and `tensorReduction` are actual
  composites of the normalized realizations with the coherent adjunction
  counits. They do not use arbitrary componentwise identifications.
* `scalarExtensionTowerCoherence` states two equations of maps in the derived
  category of whole coherent systems. They identify the reductions of the
  actual named `scalarPullbackCompleted` and `scalarTensorCompleted` with
  derived kappa and sigma under those coherent reduction comparisons.
  Functorial application of total derived limit, the adjunction triangle
  identities and derived completeness give exactly the canonical integral
  comparison maps. This states their actual quotient representatives and
  all transitions, rather than merely existence of isomorphisms with the
  same endpoints. Its existential hF and hT assert the required derived
  completeness of the pullback and completed tensor; they are not assumptions.

### Dependencies used

The original statement dependencies were read with their complete signatures
and docstrings. The modules are imported publicly, with these interfaces:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its actual quotient maps.
* `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `WeilConjectures.integralScalarExtensionOfUniverses`, its comparison, and
  its termwise scalar-extension interpretation. At the common coefficient
  size it is the named `integralScalarExtension` used in the integral maps.
* `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
* `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`:
  `SheafOfModules.changeOfRings_isKFlat_of_flat_terms`.
* `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`:
  `CategoryTheory.CochainPullback.cochainPullbackTensorCoherence`, its
  representative tensor comparison data and coefficient-square calculus.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleSheafInverseImage`; its coefficient pullback interfaces
  are used by the existing sequence-site pullback.
* `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`, used by `coefficientTotalTensor`.
* `Sheaf.Paper.NormalizedDVRTower`:
  `NormalizedDVRTower` and the inherited normalization convention. The
  coefficient-extension data use `IsNormalizedCoefficientSequence`, its
  diagrammatic form for the actual coefficient sequence site.
* `Sheaf.Paper.CoefficientExtensionReductionModel`:
  `coefficientExtensionReductionModel`, `CoefficientExtensionSystems`,
  `CoefficientExtensionReductionData`, including `directEvaluation`,
  strict transitions, normalization and coherent completion counits.
* `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `scalarOperationsOrdinary_tower`, `scalarPullbackCompleted`,
  `scalarTensorCompleted`, and their scalar unitor/composition maps.
* `Sheaf.Paper.SfIntegralConstructible`:
  `sfIntegralConstructible` and `sfIntegralConstructibleCategory`.
* `def-weil-scheme-morphism-properties` is the recorded convention node;
  the Lean hypothesis uses `IsUnit` on the global sections as above.

The item additionally cites already landed nodes supplying interfaces used
in the signature: `def-trf-integral-comparison-sequence-systems`
(`Sheaf.Paper.IntegralComparisonSequenceSystems`, actual sequence maps),
`def-trf-integral-comparison-realization-models`
(`Sheaf.Paper.IntegralComparisonRealizationModels`, normalized Roos,
pullback and scalar realizations),
`lem-coef-derived-system-evaluation-calculus`
(`Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
`CoefficientDerivedSystemCalculus`, `CoefficientReductionPresentation`,
`CoefficientTensorModels`),
`lem-pur-completed-operation-tower-substitution`
(`Sheaf.Paper.CompletedOperationTowerSubstitution`,
`CompletedOperations.Models`), and `def-pur-integral-derived-operations`
(`Sheaf.Paper.IntegralDerivedOperationsOnSlices`). No dependency record is
replaced. The original proof dependencies for K-flat total tensor,
ringed-topos pullback, ordinary tensor, and strict-tower derived limit are
imported as the stage-3 proof plan.

### Edge cases

Read the source blueprint's integral-operations clause and Stacks 03EL/07A4
in the local literature. Checked f=id, L=E, P=Q=the coefficient ring in
degree zero: the equations reduce to the scalar action unitors. Checked
E-to-L-to-F: both scalar routes multiply d*j(b), with direct embedding
j.comp ι. Checked zero complexes and the empty scheme: the equations are
between the unique zero maps. Arbitrary integral cochain degrees are allowed;
no bounded representative is imposed, and the maps preserve (p,q), including
negative p and the Koszul sign. Checked a ramified quadratic extension of
Q_l: A_m-to-B_m need not be flat, and the Lean has no such assumption;
flat-term K-flat change of rings gives the required derived interpretation.
The positive quotient indexing includes every nonzero quotient level; the
exponent-zero quotient is zero and has its unique compatible maps.

### Searches

* `msearch.py ... leanfinder "strict quotient tower scalar extension pullback tensor coherence"`:
  ordinary scalar association (`ModuleCat.extendScalarsComp_hom_app_one_tmul`),
  tensor quotient/pushout material; no full node.
* `msearch.py ... loogle "TensorProduct, CochainComplex.mapBifunctor"`:
  zero matches.
* `msearch.py ... grep "scalar.*coherence|coherence.*scalar" CategoryTheory`:
  zero matches.
* `msearch.py ... leansearch "scalar extension tensor pullback strict inverse system cochain complex coherence"`:
  generic pullback/scalar material, not this strict quotient tower statement.
* `rg` of scalar/tower/coherence names in the upstream `WeilConjectures` and
  the shared `lean/Sheaf`: the named integral scalar comparisons and the
  sequence/realization interfaces above are constituents, not the mixed
  strict square with normalized quotient representatives.
* Exact item-id search in upstream: no declaration. Exact item-id search
  in shared Lean: references in consumer docstrings, not a declaration of
  the item. The full statement is not already in Mathlib or the project.

No statement correction, disputed statement, new independent definition node,
or dependency-module repair is needed. All added declarations are adapters or
normalization clauses of the owning node and carry its blueprint/source tag.

## Second reading by Q55

A separate self-audit compared every hypothesis, the direction of each map,
and every clause against the node and source. The strict square is stated
before localization, and inverse compatibility follows from equality of
isomorphisms. The audit caught the need to pin the tensor realization to the
legacy named completed tensor comparison, and the need to state the actual
balanced quotient association; both are explicit in the delivered interface.
It also checked that identity and successive extensions are equations under
the action unitor and scalar associator, and that no finite-level flatness is
assumed. The dispatcher explicitly forbids starting another agent; this
section records my second pass, and the maintainer supplies the independent
review specified in the worker brief.

Additional catalog/name check: `rg` of `ScalarExtensionTower` and
`scalarExtensionTowerCoherence` in `dag/lean_names_upstream.json`, upstream
`WeilConjectures`, and shared Lean found no name collision. The shared
`CategoryTheory/FlatScalarTowerCoherence` concerns exact scalar extension of
module objects on a fixed braided category; it assumes exactness for its
derived clauses and does not provide the pro-etale mixed pullback/tensor
square, ramified derived extension, or normalized quotient-limit model here.

Validation: the final file passed prescribed `scompile.py` sandbox and actual
library-name compilation with no errors or warnings. The library-name Lean
invocation took 52.7 seconds, within the unchanged 60-second file limit.
