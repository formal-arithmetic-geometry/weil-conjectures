## Worker report

The delivery states `WeilConjectures.shriekComposition_frobenius` in
`Sheaf.Paper.ShriekComposition`. Its natural isomorphism is on the actual common-stage
constructible category used by compact support and `sfCommonStageWeilComplex`, with
an explicit Frobenius commutativity equation. All theorem proofs are `sorry`.
Every auxiliary postponed theorem has a source and proof docstring. The auxiliary
maps belong to this item's module and are listed in `lean.declarations`.

Hypotheses and clauses, read against the node and its main-20261015 proof:

- The standing finite-field data are `D : FiniteFieldDatum`; `l`, `Fact l.Prime`,
  and `hl : l ≠ D.p` are precisely the coefficient conventions. The independent
  universe `v` of the algebraic closure `Ω` is retained. `Field Ω`,
  `Algebra (Padic l) Ω`, and `IsAlgClosure (Padic l) Ω` express Qbar coefficients.
- The three k0-schemes are `X₀ Y₀ Z₀ : Over (Spec (.of D.k₀))`. For each structure
  morphism, `LocallyOfFiniteType` together with `QuasiCompact` means finite type;
  `IsSeparated` means separated. These are the node's separated finite-type schemes.
- The composable k0-morphisms are `f₀ : X₀ ⟶ Y₀` and `g₀ : Y₀ ⟶ Z₀`.
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on each underlying map
  render exactly separated finite type. The order `f₀ ≫ g₀` is g after f.
- `cf`, `cg`, and `cfg` quantify presentations by compactifications over k0.
  These are presentations of the recorded compact-support construction, available
  for every morphism in the statement by Nagata, rather than new geometric
  restrictions. The theorem holds for every such presentation.
- `ShriekGeometricAction` is an abbreviation of the already recorded
  `SfCompactSupportCoefficientAction`, applied to the actual base-changed
  compactification. `shriekGeometricCompactification` has real middle scheme,
  open map, and proper map; only its three named property lemmas are postponed.
  `Sf`, `Sg`, and `Sfg` exist in the conclusion: no existence or Frobenius
  equivariance is imposed as an additional hypothesis.
- `β : Sfg.system.functor ≅ Sf.system.functor ⋙ Sg.system.functor` is the
  functorial isomorphism R(gf)! ≅ Rg!Rf! on the geometric fibres. `NatIso`
  includes invertibility and naturality for all objects and maps, not just stalks,
  cohomology groups, or finite-stage objects.
- The final equality, quantified over every common-stage object `K`, says
  `ψ_gf(K) ≫ β(F_X*K) = F_Z*(β(K)) ≫ ψ_g(Rf!K) ≫ Rg!(ψ_f(K))`.
  Here each `ψ` is `shriekGeometricFrobeniusComparison`, a specified canonical
  map, not an arbitrary supplied isomorphism. Composing this equality with the
  image of any input Weil structure gives exactly the fixed-pair morphism
  equation in `sfCommonStageWeilComplex`. Inverting β gives the same condition
  for its inverse. No condition that the input Weil structure descend to a
  finite-stage lattice is introduced.

Canonical comparison helpers: `shriekAutomorphismPullSquare` is formed from the
recorded inverse-image compositors and the actual commutation equation.
`shriekAutomorphismProperMap` is its counit mate;
`shriekAutomorphismOpenMap` is its inverse unit mate. Their invertibility for
scheme automorphisms is a named theorem, not an arbitrary choice of data.
`shriekAutomorphismAmbient` pastes the proper comparison and inverse open
comparison. `shriekAutomorphismIntegral_existsUnique` specifies the unique
constructible lift by its full ambient component, using the normalized Roos
pullback and compact-support realization. The Qbar existence-and-uniqueness
statement fixes every finite-stage component to the rationalization of that
integral component. Thus the two following definitions choose only uniquely
determined objects. The geometric specialization uses the three literal
geometric-Frobenius automorphisms and `zlFrobenius_naturality` for the model
compactification's open and proper parts. This supplies the portion of the
canonical Frobenius exchange construction needed for this item's statement,
without introducing a second independent definition node for the existing
`def-weil-frobenius-square-exchange` notion.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, its
  `geometricFiber` and `geometricFrobenius`.
- `Sheaf.Paper.PbcQbarCategory`: `AlgebraicGeometry.Scheme.pbcQbarCategory`,
  imported as recorded. As the reviewed node's proof explicitly requires, its
  separate pbc pair category is not identified with the common-stage category.
- `def-weil-pbc-scheme-conventions` is a convention node: the scheme hypotheses
  are the Mathlib classes just listed, rather than a nonexistent extra datum.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `Stage`, `inclusion`,
  `stageSystem`, and its actual common-stage functor construction.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`; through its imports,
  `sfCompactSupportFiniteIntegralFunctor`, `PurCompactSupport.completed`,
  `pull`, `push`, `image`, `geometricPullComposition`, `completedPull_comp`,
  `openDerivedAdjunction`, and `proEtaleRingDerivedAdjunction`.
- `Sheaf.Paper.CompactSupportCoefficientAction`:
  `SfCompactSupportCoefficientAction`, including `system`, normalized
  `integralBeta`, `rationalBeta`, `finite_eq`, and `value_eq`.
- `Sheaf.Paper.CompactSupportFiniteFieldIndependence`:
  `sfCompactSupportFiniteFieldIndependence` supplies normalized actions without
  extra assumptions; used by the main theorem's proof description.
- `Sheaf.Paper.FieldShriekCompositionQcqs`:
  `sfFieldShriekCompositionIntegral_existsUnique`, its rational version and
  `sfFieldShriekCompositionQbar_existsUnique`. The main theorem adds the
  Frobenius square to their already normalized composition comparison.
- `Sheaf.Paper.AdicMiddleExtensionConstructible`: `adicPullComparison` and
  `adicOrdinaryPull`, with their Roos-unit/augmentation normalization.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilPrimeInvertible`,
  `sfCommonStageWeilFrobeniusPullback`, and `sfCommonStageWeilComplex`.
- `Sheaf.Paper.WeilCompactSupportCohomology`: `zlCompactificationMiddle`,
  `zlCompactificationOpen`, `zlCompactificationProper`, and the geometric-fibre
  over-base, finite-type, quasi-compact and morphism-property interfaces.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlFiberMap` and
  `zlFrobenius_naturality`.
- `Sheaf.Paper.ImmersionWeilLocalBehavior`: retained published geometric-base-change
  instances `immersionWeilOverPullback_locallyOfFiniteType` and
  `immersionWeilOverPullback_quasiCompact`. These resolve the actual bundled
  `Over.pullback` structure maps when projecting the action system. The node
  now records the later `ZlImmersionWeilLocalBehavior` module; the earlier
  module and its exact helper declarations remain published and are reused.
- Mathlib: `Compactification`, `Functor.associator`, `Functor.isoWhiskerLeft`,
  `Functor.isoWhiskerRight`, `mateEquiv`, `TwoSquare`, `eqToIso`, and `asIso`.

Added statement dependencies are existing landed nodes owning the coefficient
action, its existence, field composition, geometric compactification model,
normalized pullback comparison, geometric-fibre instance transport, and
common-stage coefficient category. There
are no new nodes, dependency repairs, or changes to the node's mathematical
statement. The unstated `lem-fix-weil-operations` is not assumed as a Lean
hypothesis: the needed canonical maps are supplied explicitly in this module,
and equivariance of composition is the conclusion being stated.

Edge cases checked mathematically: empty source and zero complexes give the
unique zero-map comparisons; identity f or g gives the identity/composition-unit
case; an open followed by a proper morphism is the defining compactification
case; a point target gives compact-support cohomology. Frobenius is semilinear
over k, and is used only as a scheme automorphism with its actual naturality
squares, never as a k-linear automorphism. No separatedness assumption is added
to a compactification's middle structure morphism. Arbitrary Weil structures
and independent coefficient-closure universes remain allowed.

Searches (2026-10-18):

- `msearch.py leanfinder`, query `Composition of exceptional direct images on
  bounded constructible l-adic Weil complexes is compatible with Frobenius`:
  eight ordinary module pushforward/pullback comparison results, no match.
- `msearch.py loogle`, query `"shriek"`: zero hits.
- `msearch.py leansearch`, query `composition of exceptional pushforward
  functors on l-adic Weil complexes`: eight ordinary site/module results,
  no match.
- `msearch.py grep`, query `lowerShriek|[Ss]hriek|[Ee]xceptional.*[Cc]omp`,
  Mathlib `CategoryTheory`: zero hits. Query `shriek|Shriek|exceptional`,
  `AlgebraicGeometry`: zero hits.
- `rg` in upstream WeilConjectures for `lem-zl-shriek-composition` finds only
  the formal-steps reference. The upstream names index and current source of
  `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` give
  `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_comp_iso`, but
  that is on the derived category of Weil sheaves, a different category from
  the recorded fixed pairs. It cannot serve as an exact existing attachment.
- `rg` in side Lean sources for compact-support, composition, and Frobenius
  finds the recorded normalized coefficient action, the field compositor,
  `adicPullComparison`, and the geometric-fibre interfaces reused above.
- `msearch.py leanfinder`, query `canonical compact support direct image
  comparison with scheme automorphisms normalized by proper counit and open
  unit`: eight unrelated ordinary AG results.
- DAG searches and `tools/blueprint_refs.py search 'Frobenius compact support
  comparison'` (zero blueprint-reference hits), followed by broader DAG
  searches, found `def-weil-frobenius-square-exchange` and
  `lem-coef-frobenius-exchange-equivalence`, both without a usable recorded
  Lean interface. The helpers here explicitly construct the required
  proper/open mate specialization in this item's owning module.
- `rg` of side Lean and upstream for `shriekAutomorphism`,
  `shriekGeometricFrobenius`, and `ShriekGeometricAction`: no existing names.

No STATEMENT-DISPUTED finding.

## Second reading by Q144

I reread the complete node, its main-20261015 statement and expanded proof,
the dependency signatures, and the delivered module. This is the dispatcher's
single-worker self-check; no independent reviewer is claimed. The maintainer
performs the independent delivery review.

The principal mismatch avoided was using the upstream derived category of
Weil sheaves or the pbc coefficient pair category for the common-stage fixed
pairs. Another was permitting an arbitrary Frobenius comparison: the delivered
helpers instead specify the counit/unit maps and their unique realizations.
The Lean direction is R(gf)! to Rg!Rf!, with the square checked in the same
composition convention as the node's displayed Weil-morphism equation.
The three `letI` clauses in the main signature only expose the existing
composition instances for the underlying `Over` maps; they add no hypotheses.
The geometric compactification is the actual base change of the model, so
its Frobenius structure is specified, and not additional chosen equivariance
data. All declarations bind universes and parameters explicitly; all auxiliary
theorems retain their full natural-language proof and source in docstrings.
