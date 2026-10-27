## Worker report

The module states this node, with six postponed theorem declarations and real helper
constructions. There are no proofs, new nodes, dependency repairs, or statement changes.
The current blueprint source read was
literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, paragraph (2), and its statement file.
The node expands the domains needed to transpose those maps.

Clause-by-clause correspondence:

- The standing field is `D : FiniteFieldDatum`; the prime is `[Fact ell.Prime]`
  with `ell ≠ D.p`. Schemes and morphisms use `Over (Spec (.of D.k))`;
  separatedness, locally finite type and quasi-compactness of their structure maps
  state exactly separated finite type over k. No smoothness is assumed on v.
- Finite coefficients are arbitrary `A : Type (u+1)` with `CommRing`, `Finite`,
  and an existential positive ell-power annihilator. The fixed-module universe is
  the existing small-pro-etale size convention, with no equality of site object
  and Hom universes. Every finite ring has a representative at this universe.
- `Etale.FiniteSmoothPurity.IsCtf` is the published intrinsic constructibility,
  finite cohomological interval, and universal finite Tor amplitude predicate.
  Its use does not impose an etale-origin witness. `proCategory` and `proPullback`
  are the recorded ordinary, uncompleted fixed-coefficient localization and pullback.
- `finite_models_and_pullback` first asserts existence of P,a,b, ordered interval,
  zero terms outside it, flat constructible terms, and `Q(P) ≅ K`. It then universally
  quantifies over every supplied P,a,b satisfying exactly these conditions.
- The universal conclusion asserts flat constructible pulled-back terms,
  `quasiIso.kFlat` of that actual pulled-back complex, `Q(v*P) ≅ v*K`, zero
  terms outside exactly [a,b], membership of v*K in IsCtf, Tor amplitude [a,b],
  and an isomorphism `H^i(v*K) ≅ v*H^i(K)` for every integer i. Equality here is
  categorical identification by isomorphism, as required by the stage convention.
  `HasFixedCoefficientProEtaleTorAmplitude` tests all degree-zero sheaves using
  the existing derived tensor, so it contains precisely the stated tensor vanishing.
- `stratification_local_models` takes every supplied positive finite stratification
  with lisse finite-stalk restrictions. It asserts the same property on its actual
  `S.pullback v.left`. Its second conclusion preserves every supplied finite module M
  and trivialization along every weakly etale t, on the actual double fibre product.
  This applies to each term and each cohomology sheaf in the preceding theorem.
  `pulledBackTrivializingCover` is Mathlib's actual base-changed pro-etale cover,
  retaining its index set. No choice of a replacement cover/model is used.
- `towerPullback` transports the recorded exact inverse image through the
  section-preserving realization of the original strict tower category. The
  `SpTowerShriek.Geometry` fields constrain its ordinary functor, finite evaluation,
  scalar transitions and monoidal comparison to the canonical construction.
- `tower_bounds` assumes constructible finite-Tor levels, one common ordered
  cohomological interval [c,e], and one common ordered Tor interval [a,b'].
  It concludes those same three clauses with exactly those endpoints after pullback,
  and the evaluation isomorphism to finite derived inverse image. No normalization
  predicate or invertibility of any reduction map occurs.
- Natural index n is the paper's positive exponent n+1. The actual coefficient
  `SpTowerShriek.R ell E n` is O_E/(ell^(n+1)). `towerResidueTransport` uses
  `b.ideals n` and `quotientTransport`, identity on O_E modulo the equal ideals,
  to identify it with A_(E,r(n+1)). It never uses exponent n+1 instead of r(n+1).
- In the finite smooth clause f has `SmoothOfRelativeDimension d` with d : Nat;
  all four schemes are separated finite type over k, and the square is `IsPullback`.
  `finiteOmega` is the specified exceptional functor at `finiteGeneralRingUnit`.
  `finite_smooth_domains` asserts IsCtf of both displayed sources, with the
  hypothesized isomorphism e1 exactly as in the node. The HasCompactification
  instances only expose the existing compact-support/exceptional construction;
  these exist for separated finite-type maps over a field, including f'.
- `finiteComparison` is explicitly `leftDerivedUpperStarTensorIso`, followed by
  `tensorIso` of the inverse canonical square comparison and e1. Hence it is an
  actual canonical isomorphism of the two sources, not Nonempty of an arbitrary map.
- For towers `tower_unit` states the rank-one coefficient object is in the uniform
  category. `towerOmega` applies the given restricted right adjoint to this unit
  and realizes it in the original system derived category. The adjunction is
  supplied as `SpTowerGluing.support ... ⊣ G`, so G is not an arbitrary functor.
- `tower_smooth_domains` gives membership of both displayed tower tensor sources,
  transported back by the fixed realization. Its hF/hF' arguments expose the
  restriction of the recorded compact-support functor; adj/adj' supply exactly
  the existing restricted adjunctions. These are the adjunction data that the
  statement says to use, not a replacement exceptional operation or a stronger
  preservation axiom on a new functor.
- `towerComparison` explicitly composes the recorded `tensorPullback` and
  `tensor.mapIso` of the inverse `SpTowerShriek.square` and e1, in the actual
  ordinary system derived category before evaluation. Fullness and the supplied
  adjunction give the stated transpose domains. No lift from finite-level maps,
  completed category, or normalization hypothesis is involved.

Dependency declarations read and used (the convention node fixes no declaration):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-scheme-morphism-properties`: `None`, `None`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `AlgebraicGeometry.ProEtale.FiniteCoefficientModules`.
- `def-weil-proetale-constructible-sheaf`: `Sheaf.Paper.ProEtaleFixedModuleConstructible`, `AlgebraicGeometry.Scheme.IsConstructibleProEtaleFixedModuleSheaf`.
- `def-weil-proetale-tor-amplitude`: `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`, `AlgebraicGeometry.Scheme.HasFixedCoefficientProEtaleTorAmplitude`.
- `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`, `WeilConjectures.commonStageDerivedInternalHom_existsUnique`.
- `def-weil-derived-tensor`: `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`, `AlgebraicGeometry.ProEtale.derivedTensor`.
- `sk-def-sp-coefficient-towers`: `Sheaf.Paper.SmoothPurityCoefficientTowers`, `AlgebraicGeometry.ProEtale.spCoefficientTowers`.
- `det-sp-coefficient-towers-abelian`: `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`, `AlgebraicGeometry.ProEtale.sp_coefficient_towers_abelian`.
- `sk-def-sp-normalized-towers`: `Sheaf.Paper.SmoothPurityNormalizedTowers`, `AlgebraicGeometry.ProEtale.spNormalizedConstructibleTorTowerCategory`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `det-sp-finite-general-ring`: `Sheaf.SecSmoothPurity.FiniteGeneralRing`, `AlgebraicGeometry.ProEtale.finiteGeneralRingSmoothPurity`.
- `det-sp-tower-gamma`: `Sheaf.Paper.SmoothPurityTowerGamma`, `AlgebraicGeometry.ProEtale.SpTowerGamma.tower_gamma`.
- `def-pur-co-smoothness`: `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`, `AlgebraicGeometry.ProEtale.IsCohomologicallySmoothFiniteCompared`.
- `det-sp-tower-gluing`: `Sheaf.Paper.SmoothPurityTowerGluing`, `AlgebraicGeometry.ProEtale.SpTowerGluing.tower_gluing`.

The generic constructibility record publicly retains its ringed predicate; its
fixed-module predicate is used above. The general Tor-amplitude record's exact
fixed-module specialization is used above. The finite smooth maps underlying the
recorded general-ring purity module supply `IsCtf`, `proCategory`, `proPullback`,
`exceptional`, and `finiteGeneralRingUnit`. The tower-gamma module supplies
`originalUnit`, `exceptional`, `realization` and the tower-calculus coordinates;
no second definition of any coefficient category or tensor is introduced.
All recorded statement modules and all stated proof modules are imported directly;
Mathlib Smooth and Topology.IsConstructible.preimage are used through their owning
modules. The proof docstrings reproduce the six steps of the DAG argument,
including the no-normalization and actual-tower-map points.

Edge cases checked: empty schemes and empty strata are allowed; the stratification
keeps its positive index count, allowing empty pieces. The zero ring and zero object
satisfy the predicates; arbitrary integers and a=b are retained. Covers may have empty
indices on an empty stratum, with the same zero/finite module model. All positive
tower levels, including exponent one, are present; r may exceed one. d=0, identity
base change and arbitrary non-smooth/non-flat v are included. The two uniform
intervals are independent and are never replaced by enlarged existential intervals.
No `STATEMENT-DISPUTED` finding.

Searches for an existing combined statement:

- msearch.py leanfinder: "Derived pullback preserves bounded constructible finite
  Tor amplitude complexes and ordinary varying coefficient towers"; eight hits
  (`Functor.mapDerivedCategory`, IsGE/IsLE and unrelated localization facts), no match.
- msearch.py loogle: "SheafOfModules.pullback"; twelve underived pullback and
  composition hits, no combined finite/tower/smooth-source theorem.
- msearch.py grep: "pullback.*(TorAmplitude|Constructible)|(TorAmplitude|Constructible).*pullback";
  zero Mathlib hits.
- msearch.py leansearch: "Exact proetale inverse image preserves bounded flat
  constructible complexes and uniform Tor bounds for coefficient towers";
  eight hits in module flatness/exact functors and scheme flat restriction, no match.
- rg of lean/WeilConjectures and lean/Sheaf for the item id, theorem names,
  flat constructible models and pullback Tor preservation: upstream FlatModel and
  PullbackTorAmplitude provide parts, not the combined statement. All are reused
  through recorded dependencies. No existing declaration duplicates the module.

Validation: scompile.py compiles every declaration in required module mode;
all delivered theorem proofs are `sorry`, and all helper data are genuine terms.
Final dry-run and delivery results are supplied by deliver2.py.

## Second reading by Q09

Self-check with the node and complete module open; no separate agent was started,
as directed in the dispatcher brief. Independent review is the maintainer's delivery
review. The finite section retains each representative hypothesis, each of the
seven representative/pullback conclusions, every degree, and every local model.
The initial draft did not name the cover base change and ramification transport;
these are now real definitions with the actual fibre product and equal ideals.
The tower section retains exact endpoints, positive levels and non-normalized
inputs. Both smooth sections assert membership of both sources; their canonical
comparisons explicitly use the specified three factors. The coefficient unit is
proved only by a named postponed theorem, never by `sorry` inside a definition.
All variables/universes are explicit; no local notation/private helper or diagnostic
commands remain. No node text was changed and no dependency was redefined.
