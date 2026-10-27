## Worker report

The module `Sheaf.Paper.FiniteReductionTowerResolvingModel` states
`WeilConjectures.FiniteReductionTower.finite_reduction_tower_resolving_model`.
Its conclusion is `Nonempty (ResolvingModel l E g)`, where the concrete structure
packages the clauses below. The theorem has exactly one `sorry`; the structure
has real fields and contains no construction from a mere existence choice.

The previous worker confused the Q140 stage-1 merge with a stage-2 landing.
The current node has a reviewed eight-step split but no Lean record. The Q140
review explicitly says what stage 2 should do about coefficient presentations.
This delivery supplies that missing statement; it does not resubmit the split.

Hypotheses and objects, clause by clause:

- The prime is `l : ℕ` with `[Fact l.Prime]`. The finite extension is `E : Type u`
  with `[Field E]`, `[Algebra (Padic l) E]` and `[FiniteDimensional (Padic l) E]`.
  The actual integer ring, fixed uniformizer and positive quotient rings are
  those of `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`
  and `coefficientExtensionRing`, reached through the recorded imports.
- The schemes are `X Y : Scheme.{t}` and the morphism is `g : X ⟶ Y`; these are
  T' and T. `_hX` and `_hY` require that `l` is a unit in every stalk, exactly
  scheme-level invertibility. This includes empty schemes.
- `u` and `t` are independent. The original small pro-etale site has object
  universe t+1, Hom universe t, and the module universe is max(u,t+1).
- `CompletedTowerIndependent.Modules` is the module category of the actual
  completed constant coefficient limit. Its specified projections and quotient
  transitions are reused. `Towers` is `ℕᵒᵖ ⥤ Modules`; index n means exponent
  n+1, equivalently the positive-integer indexing of the node.
- `pull l E g` is G, the canonical ringed module pullback fixed by the adjunction
  to direct image with the projection-induced coefficient map. No assertion of
  its exactness or of invertibility of that coefficient map is made.
- Cochain complexes are indexed by all integers. `DerivedCategory.Q` is the
  unbounded localization. `integralOperationsGoodComplex` is exactly the
  conjunction of K-flatness and flatness of every term.
- B_g^0 is literally `integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X`.
  `homotopy`, `shift` and `cone` express preservation of chain homotopies,
  integer shifts and mapping-cone complexes before localization.
- `quasiIso` says that every quasi-isomorphism between good complexes maps to
  a quasi-isomorphism at every level of that actual finite pullback tower.
- `B : DerivedPair ...` gives the everywhere-defined functor B_g, its natural
  counit beta, the universal `IsLeftDerivedFunctor` property, and invertibility
  of beta on every good complex. `beta_naturality` writes the requested square.
- `sourceTower` is H(P) = P tensor Q_n, with the recorded P-first total tensor
  and transition id_P tensor (t,1). `targetTower` is P tensor S_n[0], with its
  actual quotient transitions. `comparison` is id_P tensor epsilon_n. These
  are the recorded definitions, not private copies.
- `augmentation_quasiIso` localizes a quasi-isomorphism of entire strict tower
  complexes; `source_good` supplies good source levels. `augmentation_naturality`
  is the strict square for the existing `sourceTowerMap` and `targetTowerMap`.
- `normalizationIso` identifies total tensor with the recorded ordinary
  scalar-extension reduction complex. `normalization` fixes this isomorphism
  on the actual sheafified total-tensor generators: x tensor s maps to s tensor x.
  This is the usual balanced scalar-extension presentation and fixes the map;
  it is not an arbitrary isomorphism between the two models.
- `reductionIso` is the computation QF(P) ≅ R(QP) in the whole derived tower
  category. `reduction_computation` fixes it by the published reduction counit
  and the preceding normalized strict isomorphism. `reduction_naturality`
  supplies its chain-map naturality.
- V_g and epsilon^V are exactly `derivedPull` and `derivedCounit` of the
  recorded independent-universe specialization. `tower_computation` says
  epsilon^V is invertible on H(P); `augmentation_invertible` supplies the
  inverse of the localized strict augmentation used in the formula.
- `chi` is an isomorphism from V_g(R(QP)) to QG H(P) in D(Towers), not a
  family of isomorphisms in the separate finite-level derived categories.
  `chi_formula` is V_g(reductionIso.inv followed by (Qa_P)^(-1)) followed by
  epsilon^V_H(P). After the specified reduction identification this is precisely
  epsilon^V_H(P) composed with V_g(Qa_P)^(-1), with the composition order of
  the node. `chi_naturality` is the full strict-tower naturality equation.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, importing the actual
  coefficient constructions and `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, importing
  `completedIntegralCoefficientSheafUnrestricted`, `integralCoefficientSheafSystem`
  and its actual limit projections; also `integralConstantToCompletionOfUniverses`.
- `Sheaf.Paper.IntegralOperationsWellDefined`: `integralOperationsLevelPullback`,
  `integralOperationsPullbackGenerator`, `integralOperationsPullbackTowerFunctor`
  and `integralOperationsGoodComplex`. The tower's transitions are the
  unit-generator characterized transitions in that module.
- `Sheaf.Paper.PrincipalKoszulStrictReplacement`: `residue`, `projection`, `koszul`,
  `multiplication`, `augmentation`, `sourceTower`, `targetTower`, `comparison`,
  `sourceTowerMap`, `targetTowerMap`; the completed uniformizer and tensor order
  are exactly those of these definitions.
- `Sheaf.Paper.AdicCoefficientDatum` and `Sheaf.Paper.PbcQbarCompletedPullback`
  remain imported by the published specialization module, preserving the
  recorded general interfaces. Its datum-indexed categories use coefficient
  universe t+1; they are not imposed directly on the independent extension E.
- `Sheaf.Paper.IntegralCompletedTowerPullbackUniverses`: `Modules`, `Towers`,
  `transpose`, `DerivedPair`, `reductionComplex`, `reductionPair`, `pull`,
  `towerPull`, `derivedPull` and `derivedCounit`. This existing definition node
  is added to stmt_deps to cite the precise published specialization.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `coefficientTensorGenerator`,
  the actual sheafification-unit and summand-inclusion tensor generator. Its
  existing definition node is added to stmt_deps for the normalization formula.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` supplies the
  recorded independent-universe sheaf tensor. The total complex is the recorded
  `CochainComplex.mapBifunctor` from `Mathlib.Algebra.Homology.BifunctorShift`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`. The convention-only
  def-weil-scheme-morphism-properties has no declaration of its own; the schemes
  and their stalks are the existing AlgebraicGeometry definitions.

The module imports the available proof modules for change-of-rings K-flat
quasi-isomorphisms, finite constant exactness, flat-term K-flat resolutions,
K-flat total tensor, fixed-factor tensor invariance, strict diagram replacement,
and the universal resolving-class derived-functor theorem. The normalization
lemma `lem-sfb-integral-quotient-resolution-normalization` has no recorded Lean
module and therefore supplies no proof import at this stage. The theorem's
docstring includes all eight proof steps and their dependencies. No import of
the consumer `FinitePullbackStrictTowerComparison` is introduced: its existing
helper constructions are expressed here using their underlying definition nodes,
so the consumer can later import this module without an import cycle.

Edge cases checked from the actual definitions: P=0; P=R[0]; exponent one (Lean
n=0); arbitrary positive levels and all integer degrees; identity g; empty
source or target schemes when a morphism exists; genuinely unbounded good P;
arbitrary structural c_g without a flatness or isomorphism assumption; and u
independent of t. Reindexing n to n+1 preserves every transition and loses no
positive level. The counit formula has source V_g R(QP), first transports along
reductionIso.inv, then inverts Qa_P, then applies the universal counit, so all
arrows are in the stated order.

Searches actually made:

- msearch leanfinder: "The strict finite reduction tower and pullback have an
  unbounded left derived functor computed on flat term K flat complexes, with
  natural Koszul tower resolution and universal derived counit". Eight results,
  including the generic total-left-derived universal instance and Tor. None
  states this finite-tower/Koszul computation.
- msearch loogle: "CategoryTheory.Functor.IsLeftDerivedFunctor,
  HomologicalComplex.Homotopy". It reported unknown identifier
  HomologicalComplex.Homotopy and no hits. The actual type is `Homotopy`;
  source inspection confirmed the generic `Functor.mapHomotopy`.
- msearch grep: "IsLeftDerivedFunctor|mapHomotopy|mappingCone" in
  Algebra/Homology. Twenty-five hits, including generic additive homotopy and
  cone constructions. No specialized whole-tower theorem.
- rg of lean/WeilConjectures and lean/Sheaf for the item id and the resolving-model
  names found no existing statement. The concept search found
  `FinitePullbackStrictTowerComparison`, the consumer, which states a stronger
  comparison using this resolving step, not this statement. Its helper signatures
  and the complete existing `Comparison` structure were read.
- rg for integralOperationsPullbackTower, principal Koszul towers and completed
  tower pullback found the dependency constructions cited above. A DAG search
  found the already-landed independent-universe definition node, so none was
  recreated. Source searches for total-tensor/single normalization found no
  separate existing normalization map applicable here; its balanced formula is
  written explicitly as a field of the statement rather than as a new notion.

No new nodes or dependency repairs. No statement correction and no disputed
mathematical clause. Only lean and the addition of the two existing definition
nodes to stmt_deps change in the item.

Validation: scompile.py compiled both its sandbox check (46.5 seconds) and the
named library module (42.0 seconds), with no errors or warnings. The prescribed
deliver2.py --no-push completed with OK: its commit passes the server preflight
and compiles. The packet contains exactly the module, item node and this report.

## Second reading by Q124

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer fix (independent review of 908e3239)

The delivered `shift` field was a free `CommShift` structure, and `cone` was a bare
`Nonempty` isomorphism of cone objects. Both are weaker than the node: step 1 says the
shift comparison is the identity on reindexed terms, and the cone identifications commute
with inclusions and projections. The fix adds two Prop definitions.
`ShiftNormalization` pins the shift at every level and degree to the standard termwise
shift `mapCochainComplexShiftIso` of the additive finite-level functor. This is the same
equation the landed consumer uses as `FiniteShiftNormalization`. `ConeNormalization`
makes the cone comparison an isomorphism of standard cone triangles: it commutes with
`inr` and, through the pinned shift, with the connecting map `(triangle f).mor₃`.
`cone` is now data inside the structure. The theorem signature is unchanged.
