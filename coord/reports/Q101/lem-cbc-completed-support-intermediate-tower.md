## Worker report

The delivered module is `Sheaf.Paper.CompletedSupportIntermediateTower`. All public
names are in `AlgebraicGeometry.Scheme.CompletedSupportIntermediateTower`. It defines
the actual ordinary, completed and strict compact-support operations and states the
intermediate-object assertion. Every theorem proof is `sorry`; definitions contain
actual functor, unit, mate, localization or isomorphism-composition data.

The statement is distributed across the declarations in `lean.declarations`, with
`completedSupportIntermediateTower` assembling the intermediate-object and finite-origin
clauses. `exchangeSubstitution`, `twoSubstitutions`, `strictFiniteCoherence` and
`reconstructionNormalization` are essential parts of the recorded assertion.

Hypotheses and objects:

* `A : Type (t + 1)`, `[CommRing A]`, `d : AdicCoefficientDatum A` retain the datum's
  Noetherian, finite quotient, finite generation and perfect quotient hypotheses.
  Positive quotient exponent n in the prose is represented by index `n : ℕ` and
  exponent `n + 1`; the node's recorded coefficient interface uses that convention.
* Schemes have universe `t`, while their small pro-etale sites have object universe
  `t + 1` and morphism universe `t`. No equality of those universes is imposed.
* The main theorem binds separated, locally finite type, quasi-compact f and h,
  followed by the supplied `Compactification.Triangle f h`. In this existing
  interface `T.cf.Z` is U, `T.cf.i` is c, `T.cf.g` is p_Y, `T.cfg.Z` is Xbar,
  `T.cg.Z` is Ybar, `T.q` is b, `T.p` is p, and `T.cg.g` is q. Its `isPullback`,
  `i_q`, `p_g`, and compactification factorization equations are precisely the
  cartesian ambient tower and the equations bc=a and p_Y c=f. The two explicit
  quasi-compact-open instances are the node's supplied quasi-compactness. Properness
  and openness are inherited from the compactifications.
* `K : d.derived X` is over the actual inverse-limit completed ring, and
  `hK : d.TowerComplete X K` is the specified quotient completion unit condition.
  The imported `AdicCoefficientDatum.towerComplete_iff_intrinsic` identifies it with
  the intrinsic Koszul condition for every generating family and representative.
* `W n : FiniteEtaleOriginWitness X (PbcQuotient d n) ...` retains L_n in D+ and
  alpha_n in its constant-ring presentation, with the canonical finite
  constants-to-functions transport. There is no uniform lower bound. The maps are
  constructed for arbitrary families of witnesses; compatible supplied witnesses
  are included. Their compatibility is retained through the canonical strict tower
  maps, not encoded by choosing a new tower from evaluations.

Clauses and their Lean rendering:

* `res d T`, `rho d T`, `ringCompletionRestriction` and `ringSupportRestriction`
  implement restriction and the constant/completed comparison. `reduction d T`,
  `rlim T`, `completion d T` and `unit d T` are the dependency's actual strict
  reduction, total limit, completion and augmentation-normalized unit. In particular
  `rho` identifies M with the restricted original completed reduction tower.
* `openExtension` is the dependency's exact localized `moduleJ` derived termwise;
  `ordinary`, `tower`, and `completed` are B, F and C B. `ringSupport` constructs H
  over the completed ring, by actual completed-ring open extension, proper push and
  quotient completion. Its restriction is Bhat Res(K) by `ringSupportRestriction`.
* `properCompletedOpen` is C applied to Rp eta_(J K), followed by the inverse target
  unit. `limitCompletedOpen` uses the inverse open-tensor mate and the normalized
  proper/limit conjugate. `reconstructionNormalization` identifies their composite
  with `mu`, which is defined exactly as L(theta) eta_H. `completionUnits` asserts
  invertibility of both presentations, theta and mu, and completeness of Hbar.
* `finiteAndIntrinsic` and the main theorem state intrinsic completeness of H and
  finite comparisons. `finiteComparison` is a natural transformation in actual
  P_n modules: inverse reduced completion unit, counit-tensor proper projection,
  then inverse open-tensor mate. Its invertibility is explicitly stated before
  scalar restriction.
* `finiteAntecedent` is exactly Rp_et* c_et! L_n, using the existing D+ exact-open
  and right-derived-proper functors. `finiteOriginSupport` is the canonical proper
  etale mate after the exact open comparison and the original alpha_n.
  `retainedOrigins` and the main theorem retain an output witness whose complex is
  that exact antecedent, and whose alpha satisfies the equation with
  `finiteComparison`, `finiteScalarSupport` and `finiteOriginSupport`. This fixes
  the specified witness, rather than an unrelated isomorphism to the same object.
* `ringTheta` is a morphism of derived strict towers over the actual completed
  coefficient ring, constructed before evaluation. `strictFiniteCoherence` states
  its invertibility, its unit normalization, and that its evaluated maps are exactly
  the restrictions of the P_n-linear finiteComparison. It also states that its
  restriction through rho is exactly the constant theta. Thus quotient transitions
  and augmentations are attached to one actual strict morphism.
* `ordinaryReduction` is t_f: the diagram-site proper counit-tensor mate followed
  by strict open tensor descent. `theta` is its composite with the inverse reduced
  target completion unit. `reconstructionNormalization` states the exact theta
  normalization as an equality of natural transformations, not only of evaluations.
* `strictExchange` is the ordered proper mate and proper image of the normalized
  open-unit mate. `ordinaryExchange` uses the corresponding ordinary mates.
  `completedExchange` completes that ordinary exchange and identifies both endpoints
  with the displayed completed objects via `sourceInsertion` and `targetInsertion`.
  In particular its target is completed; it is not defined to be the limit of e.
* `pullReduction` is the inverse reduced completion unit followed by the inverse
  normalized strict reduction/pullback map. `exchangeSource` and `exchangeTarget`
  specify all endpoint identifications. `exchangeSubstitution` states that the
  completed ordinary map, with these identifications, equals L of the specified
  strict exchange. The endpoint maps and pullReduction are asserted invertible.
* `twoSubstitutions` states both of the node's final equations as equalities of
  natural transformations. `firstSource`/`firstTarget` include theta_f to identify
  R(Hbar) with F_f M in x_h(H). `secondSource`/`secondTarget` include mu_h' and
  theta_f' to identify Bhat_h'(x_f). The right sides are precisely whiskered e_h
  and F_h' e_f followed by Rlim. It also states that the shared intermediate
  endpoint descriptions agree. All four pullback squares, arbitrary base-change
  maps and the open/proper properties are explicit. This generic statement
  specializes directly to the supplied ambient tower and any induced base change.
* Naturality is built into all displayed natural transformations, including theta,
  mu, the strict exchanges and their whiskered substitution equations. These
  declarations apply on ambient complexes where possible and hence on the complete
  inputs of the node. Neither ordinary j! completeness nor an arbitrary j!/Rlim
  interchange is asserted.

Dependency declarations used (module followed by the principal interface):

* `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedReductionTower`, `completedReductionEvaluation`, `reductionDerivedChange`.
* `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`:
  `exists_compactifiable_compatible_tower`, with the upstream
  `AlgebraicGeometry.Compactification.Triangle` used for the supplied data.
* `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemExact`, the localized extension underlying moduleJ.
* `Sheaf.Paper.IntrinsicCompletionCompleted` and `Sheaf.Paper.IntrinsicCompletion`:
  `IsCompletedIntrinsicallyDerivedComplete`, `IsDerivedCompleteIntrinsic`;
  `Sheaf.Paper.CompletedPullback`: `AdicCoefficientDatum.towerComplete_iff_intrinsic`.
* `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness` and its imported
  `Sheaf.Paper.RingedEtaleOriginWitness`: `FixedEtaleOriginWitness`,
  `FiniteEtaleOriginWitness`, `finiteOriginToConstant`, `etaleOriginComparison`.
* `Sheaf.Paper.ConstantCompletionEquivalence`: `ConstantCompletion.equivalence`;
  `Sheaf.Paper.CompletedPullbackAdjunction`:
  `ConstantCompletion.completedPullbackAdjunction`. Their normalized original-site
  consequences are reused through the recorded original-site OrderedExchange API.
* `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`: `Towers`, `G`, `R`, `adj`;
  `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `moduleJ`, `moduleJAdj`, `J`,
  `jAdj`. These are reused directly, with no copied notion of a strict tower.
* `Sheaf.Paper.SfCbcExtensionZeroCompletion`: `sfCbcExtensionZeroCompletion`;
  its source's tensor and unit normalization is used in `openTensor` and `strictUnits`
  on the original site at the full coefficient universe.
* `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`:
  `ringedTowerPushforwardLimitComparison`; the normalized actual original-site
  `OrderedExchange.directLimitIso` is used in limitCompletedOpen.
* `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`:
  `normalizedProperOpenCalculus`, `exchange`, `beta` and `moduleSquareG`.
* `Sheaf.Paper.ProEtaleConstantReductionTower`: `OrderedExchange.reduction`,
  `rlim`, `unit`, `reductionPullIso`, `directLimitIso` and `projection`.
* `Sheaf.Paper.CompletedPullbackUnitTower`: `completedPullbackUnitTower`;
  `pullReduction` preserves its unit-normalized order on the actual original site.
* Added already-landed statement dependencies, not new nodes:
  `lem-cbc-completed-open-endpoint-limit-transport` gives
  `Sheaf.Paper.CompletedOpenEndpointLimitTransport.cbcEndpointOpen`, its ordinary,
  derived and tower scalar comparisons and its strict reduction comparison;
  `lem-weil-pbc-ordered-exchange-coefficient-comparison` gives
  `Sheaf.Paper.OrderedExchangeCoefficientComparison`'s `res`, `rho`, `lambda`,
  `chi`, `restriction_complete`; `def-cbc-finite-constant-coefficient-transport`
  gives `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`'s `HD`, `hJ`,
  `hR` and scalar realization. Their records were checked before adding the edges.
  Every recorded statement dependency is public-imported, and every recorded proof
  dependency with a Lean module is imported (deduplicated).

Searches (no exact existing statement found):

* `msearch.py ... leanfinder "Completed compact support intermediate object strict
  reduction tower and exchange substitution"`: eight unrelated supported-complex or
  adic strict-mono results; none states this node.
* `msearch.py ... loogle "CategoryTheory.Functor, CategoryTheory.NatIso"`: zero hits;
  the tool reported unknown identifier `CategoryTheory.NatIso`.
* `msearch.py ... grep "completedSupport|completed_support|compactSupport"
  CategoryTheory`: zero hits.
* `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `intermediateTower|intermediate_tower|completedSupport|CompletedSupport`: zero hits.
  Broader compact-support and finite-origin searches found the existing operations
  and comparisons listed above, which are reused. No new definition node is needed:
  all helpers are constructions belonging to this node's specified maps.

Edge cases checked: identity maps and identity compactifications retain their original
adjunction units; the empty open uses the existing exact localized zero extension;
zero input and the zero quotient ring remain permitted; I=0 and I=A are not excluded;
no nonempty scheme, connectedness, common lower bound, regularity, smoothness or
properness of f or h is imposed. Individual opens are only quasi-compact, and the
proper legs and their arbitrary base changes are explicit. No restriction on an
arbitrary ambient strict tower is used to assert open/limit interchange.

The current node already contains the stage-1 correction to completed compact support.
This delivery makes no statement correction and preserves its statement_change record.
The older blueprint proof's ordinary j! completeness assertion is not used. The node's
corrected map construction is what the delivered declarations express.

Validation: the completed module was compiled with the prescribed server scompile.py;
the final delivery preflight and compile are recorded by deliver2.py. No global build,
local Lean build, upstream write or direct Git mutation was performed.

## Second reading by Q101

The dispatched-worker brief reserves the independent review to the maintainer and
forbids starting other agents. This is therefore a self-audit, not a claim of an
independent second worker. With the node and file open I checked the matching above,
in particular the full coefficient universe, the completed open target, the order of
proper/open mates, and the unit normalizations. I corrected the initially missing
reduced-unit IsIso instance, made the finite P_n-linear map explicit, fixed retained
origins to the specified proper/open comparison, and added strictFiniteCoherence so
that finite maps are evaluated from one actual strict comparison. I also expanded
both substitutions to include all endpoint maps. The maintainer's independent reading
remains the review specified by this dispatch.
