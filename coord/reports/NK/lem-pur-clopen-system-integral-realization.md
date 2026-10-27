## Worker report

The module `Sheaf.Paper.ClopenSystemIntegralRealization` states
`WeilConjectures.PurityFiniteSetting.clopenSystemIntegralRealization`, with its proof
postponed by `sorry`. Its conclusion is a record of the actual strict-system square,
its transported comparison and its integral functorial image. The record is assertion
data, not a hypothesis. The small helper definitions contain real functor data; the
ordinary and tower instances route the existing exactness and pointwise functor instances.

Hypotheses and conventions:

- `P : PurityFiniteSetting.{u}` supplies the algebraic closure of the finite field,
  the prime distinct from the characteristic, and the finite extension of the
  corresponding p-adic field. The existing `clopenSystemRing` and
  `clopenSystemUniformizer` supply the lifted valuation ring and uniformizer.
  `clopenRealizationLevel P n` replaces only the positive level by `n + 1`.
- `X Y : Over (Spec (.of P.field.k))`, and the locally-finite-type and quasi-compact
  instances on `X.hom` and `Y.hom`, express finite-type k-schemes. The morphism
  `g : X ⟶ Y` is a k-morphism; its three instances express separated finite type.
  There is no separatedness hypothesis on either structure morphism to k.
- `{I : Type w} [Finite I]` permits every finite index set. The `Xi`, `j`, open and
  closed immersion instances, `_hdisjoint` and `_hcover` express exactly the
  partition. No nonemptiness assumption occurs. The fixed `c` is the compactification
  of `g.left`; every component compactification is literally `c.precomp (j i).left`,
  so the proper factor is shared.

Clauses and their Lean rendering: `ClopenSystemIntegralRealization.transport` holds
`ClopenSystemIntegralTransport`, while `.limits` holds `ClopenSystemIntegralLimit`.
The transport record further groups `core`, `maps` and `finite`; the fields below
are grouped in these records, the limit record and the final realization record;
this factors elaboration without changing any assertion.

- `S`, `G`, `Si`, `Gi` are the actual strict étale compact-support systems and their
  right adjoints. `strict : StrictClopenExceptionalComparison ...` retains the
  counit-normalized system comparison and its evaluations.
  `supportNormalization` retains the actual open compositor, the adjunction-unit
  normalization, and the same-proper-part site comparison.
- `CX`, `CY`, `Ci`, `CYi : ClopenSystemComparison ...` use the recorded ordinary and
  derived coefficient-system comparison and the canonical sequence-site realization.
  `sameDirect` fixes the common target input functor. `site : ClopenSystemSquare ...`
  retains the canonical underlying sheaf square, coefficient linearity, strict
  transition compatibility, termwise localization and the exact derived square.
- `transported` is the square followed by the component exceptional comparison.
  `transported_map` gives precisely `q` followed by the inverse-image image of rho.
  `clopenRealizationTransported` expresses this on all actual derived pro-étale
  systems via the sequence-site equivalence. `sequenceComparison_map` is equality with the composite of whiskered natural
  isomorphisms from that equivalence unit, transported site square and common
  target equality.
- `finiteBound`, `finiteBoundI` give the bounded-below condition needed for the actual
  finite counits on bounded constructible inputs. `finiteInsertion_unit` fixes the
  canonical open adjunction unit; `finite_counit` is the normalized counit equation
  for `finite`. `finiteEvaluation`, `finiteEvaluationI`, `restrictionEvaluation`
  identify the evaluated functors; `finiteEvaluation_map` identifies the evaluation
  of the already constructed system arrow with that finite comparison on
  constructible inputs. These are actual natural isomorphisms, not a family of
  unrelated derived maps asserted to lift.
- `system` has source and target the existing `clopenExceptionalSystem` functors.
  `system_sequence` says that its map is the preceding sequence comparison applied
  to the actual derived reduction functor from
  `coefficientDerivedSystemEvaluationCalculus`, after the constructible inclusion.
- `scalarRestriction` expresses commutation with the exact scalar-forgetting functor
  `coefficientSequenceDerivedRestriction` (DU). `clopenCompletedOrdinary` fixes the existing ordinary restriction at its actual global module category; `clopenCompletedTowerOrdinary` is
  pointwise ordinary completed-module restriction, and
  `clopenCompletedTowerRestriction` is its exact derived functor.
- `ordinaryLimitRestriction_projections` fixes the compatible-family limit map by
  every limit projection. `totalLimitRestriction` commutes restriction with
  `coefficientConstantTowerLimit`, the actual total right derived inverse limit.
  `totalLimitRestriction_normalized` fixes the map on localized complexes by the
  ordinary comparison, the two localization-factor isomorphisms and the actual
  right-derived-functor units. `limitRestriction_map` composes this with DU.
- `integral`, `integralI` take values in the existing integral constructible
  categories. `integralFormula` and `integralFormulaI` identify their inclusions
  with the common-compactification system construction followed by
  `coefficientSequenceLimit = DU ⋙ Rlim`.
- `restrictionComparison_map` fixes the integral restriction arrow as the image of
  `system` under that actual total-limit functor, using the formula comparisons.
  `reductionRestriction` states commutation with each actual derived positive
  reduction and `finiteDerivedPullback`.
- `completedComparison` is the existing canonical open completed-restriction
  comparison, including its quotient-tower, constant-section, projection,
  augmentation and signed Roos normalization. `completed_isIso` applies its canonical
  `kappa` to all integral constructible complexes. `integralComparison` uses the
  actual `integralDerivedPullback`; `integralComparison_map` is exactly kappa inverse
  followed by the realized restriction comparison. This also supplies the asserted
  reconstruction compatibility on complete objects via the existing Comparison
  record. Every comparison is a natural isomorphism: its inverse equations and
  naturality on derived morphisms are part of its type.

Dependency declarations used (their source signatures and docstrings were read):

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- Mathlib `Morphisms.Proper`, `Morphisms.FiniteType`, `OpenImmersion`, and
  `Morphisms.ClosedImmersion`: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsOpenImmersion`, `IsClosedImmersion`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, and the existing
  `Compactification.precomp` construction used by these interfaces.
- `Sheaf.Paper.ClopenCounitAdjointComparison`:
  `clopenCounitAdjointComparison_finite`, `clopenCounitAdjointComparison_system`,
  `ClopenCounitBound`, `clopenFiniteCounit` in the purity namespace.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`:
  `SheafOfModules.coefficientSystemDerivedComparison` and its existing image records.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `WeilConjectures.ConstructibleExceptionalCoefficients.System`. The existing
  `ClopenStrictSystemComparison` helpers supply the explicit common-compactification
  reduction/DU/limit expression needed in this item; no duplicate exceptional
  operation is introduced.
- `Sheaf.Paper.FiniteClopenDerivedDecomposition`:
  `PurityFiniteSetting.finiteClopen_constructible_equivalences`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback` and the actual
  `integralDerivedPullback` exposed through its slice operations.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory` (derived completeness and uniformly bounded
  constructible positive reductions).
- Added already-landed statement dependencies: `def-pur-clopen-strict-system-comparison`
  (`ClopenSystemSquare`, `StrictClopenExceptionalComparison`,
  `StrictClopenCompactSupportNormalization`, `ClopenSystemComparison`,
  `clopenExceptionalSystem`); `lem-pur-open-completed-restriction-identification`
  (`OpenCompletedRestriction.ordinary`, `derivedRestriction`, `Comparison`, `kappa`);
  and `lem-pur-clopen-strict-system-support` (the already repaired scalar interface).
- Existing sequence-site APIs `coefficientSequenceDerivedRestriction`,
  `coefficientSequenceDerivedEvaluation`, `coefficientConstantTowerLimit`,
  `coefficientSequenceLimit`, and the actual derived reduction calculus are used
  without redefinition. Mathlib pointwise exactness and derived localization
  supply the helper functors and their instances.

Edge cases checked: an empty index type makes the component conclusion vacuous and
covering forces X empty; an empty component is retained without a nonempty instance;
a singleton identity component gives the same compactification; several disjoint
components use the same proper factor. The first finite level is n=0 in sequence
indexing, hence exponent 1, never the zero quotient exponent. No separatedness of Y
over k was introduced. The scheme site and coefficient categories use the existing
u/u+1 convention, with no equation imposed between distinct site universes. Zero
objects and zero morphisms remain in the exact functors and natural isomorphisms.
The theorem is not marked STATEMENT-DISPUTED; no source statement correction is made.

Searches performed for this stage-2 delivery:

- `msearch.py ... leanfinder`, query “clopen restriction exceptional inverse image
  strict etale systems site comparison integral limit”: eight unrelated algebraic
  étale-presentation hits, including `StandardEtalePair` APIs; no match.
- `msearch.py ... leansearch`, query “clopen component exceptional inverse image
  commutes with integral coefficient derived inverse limit”: eight unrelated
  profinite/ordinary inverse-limit hits; no match.
- `msearch.py ... loogle`, query `Functor.isoWhiskerLeft, Functor.isoWhiskerRight,
  Functor.mapIso`: unknown-identifier response, no usable result.
- `msearch.py ... grep`, query `clopen.*(limit|[Rr]ealiz)|restriction.*[Ii]nverse[Ll]imit`
  in CategoryTheory: no match.
- `rg` in upstream WeilConjectures and in Sheaf for clopen/integral/realization,
  and `grep -rn` for the item id in upstream: existing clopen definition and
  comparison interfaces, but no declaration of this item. The downstream
  `FiniteClopenExceptionalRestriction` theorem combines this result with other
  coefficient stages; it is not reused as a prerequisite.
- `rg` of the new declaration names in upstream, Sheaf and the DAG upstream-name
  index: no prior declaration of these helpers or this statement.

The module has one newly postponed theorem, with its complete eight-step
natural-language proof and source in the docstring. No definition uses sorry data.
Compilation and the required preflight are run through the launcher wrappers only.

## Returned-delivery repairs

This packet repairs the independent review of immutable head `86cf50ae93af`.
The saved packet was first checked with the prescribed `deliver2.py --no-push`;
it passed the mechanical checks. The substantive changes below are new work.

1. `ClopenSystemIntegralLimit.ordinaryScalarRestriction` is pinned on sections.
   Its equation transports through the recorded ordinary sequence evaluations,
   ordinary inverse evaluation and module-underlying comparisons and the normalized
   graph-coprojection `setRestriction.sheafIso`. At every tower level it is the
   unchanged section over the composed site object. `scalarRestriction_normalized`
   pins DU commutation at `CX.sequence.derived.functor.obj (Q.obj H)` by the
   existing `mapDerivedCategoryFactors`, sequence factors and termwise ordinary
   comparison. The equivalence and localization extend this to all derived inputs.
   Negating DU would negate one side of this fixed equation. The integral comparison
   remains exactly its previously recorded total-limit composite.
   `reductionRestriction_normalized` now identifies each reduction arrow with
   scalar reduction of the canonical `kappa` followed by `purAdicPullbackReduction`.
2. `clopenCanonicalFiniteEvaluation` builds the finite evaluation component from
   the recorded direct/inverse evaluations, `integralExceptionalCoordinatesFixed`,
   `integralExceptionalCoordinatesInvFixed`, normalized derived site comparisons,
   and the compact-support right-adjoint mate. The core identifies the coordinate
   functors with these actual canonical coordinates. `finiteEvaluation_normalized`
   and `finiteEvaluationI_normalized` equate the two comparison isomorphisms with
   this composite at every derived input. `restrictionOrdinary_sections` fixes the
   ordinary level restriction through its faithful underlying section map;
   `restrictionDerived_normalized` is its full Q-factorization equation.
   `clopenCanonicalRestrictionEvaluation` then uses these level maps, the recorded
   system inverse evaluations and fixed-coefficient coordinate comparisons, and
   the actual `purAdicFinitePullbackPresentation`. `restrictionEvaluation_normalized`
   equates restriction evaluation with that composite at every input. Thus the
   finite-evaluation-map equation cannot absorb an arbitrary automorphism.
3. `def-pur-open-completed-restriction-data` owns the already published definitions
   by an `existing: true` record. It cites their existing module and declarations;
   no definitions are copied. The item, transport-data and tower-restriction nodes
   now cite this definition node instead of the theorem asserting existence and
   invertibility of these normalized data. Their imports read the same module.
4. The unused `lem-pur-clopen-strict-system-support` statement dependency was
   removed. Its sandbox node and replay module were removed entirely, retaining
   the landed Q16 record exactly and making no delivery change to that node.

These are normalizations of the stipulated canonical maps, not extra hypotheses
of the item theorem: every field is part of its asserted conclusion data. The
item's mathematical statement and proof plan remain unchanged. The old support
replay described in the returned report is withdrawn.

## Second reading by NK

No second reading by another worker: the dispatched human brief requires direct
worker delivery and the maintainer's independent review. I reread the statement and
the conclusion record clause by clause, checked the positive-level indexing, common
proper factor, map normalization and empty cases, and repaired only elaboration
and functor-instance issues. This is a self-check, not an independent review.

## New nodes

`def-pur-clopen-system-realization-data` owns `Sheaf.Paper.ClopenSystemRealizationData`.
It introduces the assertion-data package for the canonical site transport, finite
counit normalization and precomposition by actual integral reduction, together with
the exact ordinary/tower restriction helpers. These are real structures and functor
definitions, not existence assertions or chosen comparison maps. Existing
`ClopenSystemSquare` and all strict coefficient images remain fields of the new
record. This part is factored into its own definition module to keep the single-file
compile within the fixed limit. The source is the latest section-invariant final
sentence and retained finite-clopen steps 8-9. The LeanFinder, LeanSearch, Mathlib
grep, project/upstream/DAG rg and blueprint-reference searches are recorded verbatim
in substance in the node; none supplied this combined data notion. No theorem is
postponed in this definition module.

`def-pur-clopen-completed-tower-restriction` owns
`Sheaf.Paper.ClopenCompletedTowerRestriction`, factoring the actual ordinary and
pointwise strict-tower restrictions and their exact localization from the transport
data. Its definitions reuse `OpenCompletedRestriction.ordinary`, with no new
mathematical operation. The already recorded searches found no prior declaration
for this fixed-category strict-tower extension. It is cited by the new transport
data node, which is cited directly by the item. This compile boundary retains every
normalization equation.

`def-pur-clopen-system-finite-realization` owns
`Sheaf.Paper.ClopenSystemFiniteRealization`. This extracts the positive-level
boundedness, canonical insertion-adjunction unit, finite counit equation and
evaluation of the actual system comparison from the transport definition. The
record assumes transport data but asserts no existence. It is a separate definition
compile boundary, cited by the item. The normalized-clopen-system searches recorded
for the transport data explicitly included finite counit comparison data and finite
evaluations; the same results rule out a prior definition of this specialization.
The source is retained step 8, and all finite operations are the published intrinsic
ones. `ClopenSystemIntegralTransport` in the item's module combines the core, maps
and finite records.

Final module organization: `ClopenCompletedTowerRestriction` holds only actual
restriction functors and their existing exactness instances;
`ClopenSystemRealizationData` holds the core and map records;
`ClopenSystemFiniteRealization` holds the finite counit/evaluation record;
`ClopenSystemIntegralRealization` holds their combined assertion, total-limit and
integral records, and the item theorem. The mathematical conclusion is the same
recorded composite after this factoring. The previously supplied support replay is withdrawn.

Validation of the repair is recorded after the fresh per-file compilation and
required dry run below. Only launcher wrappers are used.

`def-pur-open-completed-restriction-data` is an existing-definition binding to
`Sheaf.Paper.OpenCompletedRestrictionIdentification`. It records ordinary and exact
restriction, the coefficient, quotient-tower, Roos and localization-normalized
comparison data, and `kappa`. It asserts no existence or invertibility. New
LeanFinder and LeanSearch queries returned only ordinary structure-sheaf open
restriction lemmas; Mathlib grep found no completed-coefficient comparison.
Project search found exactly these published definitions, carried by the existing
theorem node rather than a definition node. The new record therefore reuses them.
The blueprint-reference search returned zero matches for completed restriction.
Its node includes the actual tool outputs, source place and dependency citations.

The canonical evaluation constructions are factored into two further definition
modules to retain the prescribed per-file compile limit:
`def-pur-clopen-canonical-finite-evaluation` owns the explicit finite exceptional
composite in `ClopenCanonicalFiniteEvaluation`; and
`def-pur-clopen-canonical-restriction-evaluation` owns the explicit restriction
composite in `ClopenCanonicalRestrictionEvaluation`. Both are cited by the finite
assertion-data node. They retain the same canonical factors described in repair
point 2, have real definitions only, and use the recorded normalized-clopen-data
searches plus declaration-name searches showing no prior composite. This factoring
introduces no new existence claim or mathematical assumption.

Additional implementation details of the repair self-check: `coordinatesX`,
`coordinatesXInv`, `coordinatesY`, `coordinatesI` and `coordinatesYi` specify the
existing exact canonical coordinate functors, realizable by the ordinary coordinate
equivalence and its exact derived equivalence. `setRestriction` is the existing
`Scheme.ProEtaleObjectRestrictionComparison (Scheme.ProEt.mk j) (Type (u+1))`;
its graph-coprojection and sheafification equations fix the set-valued comparison.
This uses the generic site-object interface, which applies to sets, rather than
an abelian-only upper-star interface. The additive and zero-map instance fields
in the finite record merely cache properties of the already stipulated exact
functors; they are conclusions and introduce no new mathematical condition.

The normalization edge cases were rechecked: at n=0 the coefficient exponent is
one; on empty components the section maps and derived comparisons are the unique
maps in the zero category; for the identity inclusion the ordinary section
normalization is the identity and its derived factorization is the recorded one.
The empty partition remains allowed, and no separatedness of Y was introduced.
A nonzero scalar twist violates the fixed ordinary section or Q-normalization
equations. The formerly free reduction comparison now uses the existing canonical
pullback-reduction arrow for every integral constructible input.

`def-pur-clopen-restriction-evaluation-data` owns the extracted
`ClopenSystemRestrictionEvaluation` record. It groups the same ordinary section,
exact localization and canonical evaluation equations of repair point 2, preserving
all their fields while reducing elaboration cost. The finite record now holds this
as `restriction`, and its map equation uses `restriction.evaluation`. The same
recorded three-kind searches for normalized clopen comparison data apply; it is
not a second restriction construction or an additional existence assertion.

`def-pur-clopen-ordinary-restriction-realization` owns the ordinary portion of
that interface, `ClopenSystemOrdinaryRestrictionRealization`. The derived record
holds it as `ordinary` and uses its exact same section-normalized comparison.
This further compile boundary preserves the normalization fields verbatim.
The source and searches are the normalized-clopen-system searches already recorded
for these data; no existing project or Mathlib record supplies this specialization.

Fresh repair validation: the eight delivered modules passed `scompile.py`
separately in dependency order with no errors or warnings. The final integral
module passed in approximately 26 seconds; the largest helper passed in
approximately 47 seconds. The only postponed proof in the delivery remains the
item theorem. No definition contains sorry data. The required repaired-packet
dry run is performed after this compile and before delivery.

Final repair module ownership: completed-tower restriction; transport core/maps;
canonical finite evaluation; canonical restriction evaluation (including the
transparent level-isomorphism type); ordinary section-normalized restriction
realization (including the explicit exact-localization normalization predicate);
derived restriction-evaluation assertion data; finite counit/evaluation assertion
data; and the item integral-realization module. Each new module is owned by its
own new definition node, except the final module owned by the item. The existing
open-completed-restriction definition binding adds no module and no duplicated data.

The exact derived restriction normalization is the exposed definition
`IsClopenRestrictionDerivedNormalized`: it quantifies over every cochain complex
and states the original full factorization equation, with cached additive/zero-map
instances supplied by the ordinary data. Thus factoring the equation out of a
structure field does not hide or weaken its mathematical condition. A final search
of all new declaration names in the read-only project's DAG, Sheaf, upstream Lean
and upstream-name index returned no prior declaration.

Preflight identified a DAG cycle from citing `def-pur-adic-purity-objects` for its
general helper definitions. `def-pur-pullback-reduction-realization` now gives an
existing-definition binding to `purAdicPullbackReduction` and
`purAdicFinitePullbackPresentation`, both defined before any finite-field/purity
hypotheses in the published module. It cites their general coefficient, morphism,
derived-operation and coherent reduction-calculus definition nodes. The item and
finite/restriction definitions cite this general definition node instead of the
downstream adic-purity-object node. No Lean declaration or map changed. Searches
found these exact two existing maps, no general definition-node owner; the new
node records the fresh three-kind search outputs. Their source is the stipulated
canonical reduction/limit counit and exact finite pullback composition maps.

Required repaired-packet dry run: `deliver2.py NK
lem-pur-clopen-system-integral-realization --no-push` returned
`OK (dry run): commit a10a5260fca passes the preflight and compiles; nothing pushed`.
All four maintainer return points are repaired. The landed support record and
module are absent from the delivery delta. No item statement correction was needed.
