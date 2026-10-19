## Worker report

This delivery states `lem-pur-rational-weil-naturality-mate` in
`Sheaf.Paper.RationalWeilPurityNaturalityMate`, with one coefficient-twist dependency repair and a new canonical-realization definition.
All proofs remain `sorry`. Definitions have real data; every choice is from a theorem
that determines the chosen map by its representative or generator normalization, or a
unique orientation by its finite traces. No arbitrary exchange or purity isomorphism
is an input. There is no statement correction and no STATEMENT-DISPUTED finding.

Hypotheses and clauses of the item:

- The finite field and coefficient datum is `P : PurityFiniteSetting`; its fields are
  `P.field`, `P.coefficients.l`, `P.extension`, and `P.coefficients.Qbar`. The coefficient
  datum supplies the primality instance and `P.coefficients.different`. Coefficient
  universes follow the recorded datum. Scheme, small-site object and morphism universes
  are retained by the existing operations; no equality of site universes is added.
- `X₀ Y₀ : Over (Spec (.of P.field.k₀))` with `LocallyOfFiniteType`, `QuasiCompact`
  and `IsSeparated` on the structure maps are exactly separated finite-type models.
  `f₀ : X₀ ⟶ Y₀` is a morphism over the base, with those three properties on `f₀.left`.
- `zlFiberMap P.field f₀` is the actual base change, and
  `[SmoothOfRelativeDimension d (zlFiberMap P.field f₀)]`, `d : ℕ`, is smooth pure
  relative dimension d≥0. Prime invertibility on both geometric fibres is inherited
  with `sfWeilPrimeInvertible`, never assumed as an extra geometric restriction.
- `c₀ : Compactification f₀.left` and `zlGeometricCompactification P.field f₀ c₀`
  enforce precisely the descended compactification required by the item.
- `S : ConstructibleExceptionalCoefficients.System ...` specifies the normalized
  constructible operations and their adjunction. F, G and the counit in the theorem
  are the fields of its operation at that compactification and the rational or closed
  stage. They are not independently chosen functors or adjunctions.
- `sfWeilFrobeniusPullback` and `sfCommonStageWeilFrobeniusPullback` are the actual
  semilinear geometric-Frobenius pullbacks. No k-linear substitute is used.
- `RationalWeilPurity.H` and `CommonWeilPurity.H` are Lf*(-)(d)[2d]. Their normalized
  presentation is the shifted d-th coefficient line on the left tensor factor and
  Lf*K on the right. The existing tensor symmetry and shift comparison identify this
  with the source notation K(d)[2d]; the fixed comparisons retain those identifications.
- `rationalWeilPurityGamma` and `commonWeilPurityGamma` specialize the canonical
  realization families described below, using the specified coefficient mates.
- The first conjunct of `PurityNaturalityMate` is `∀ {K L} (a : K ⟶ L),
  (γ K).hom ≫ G.map a = H.map a ≫ (γ L).hom`. This is exactly naturality for every
  localized rational arrow or common-stage arrow, not only integral arrows.
- `RationalWeilPurity.b` explicitly composes canonical pullback/tensor comparison,
  shift comparison, root-line Frobenius comparison, pullback composition and the
  equality `zlFrobenius_naturality`. `CommonWeilPurity.b` uses the same factors in
  the literal finite stage and `zlFrobeniusSquare`. Thus b is the specified canonical b.
- `integralExchange` uses the actual open/proper mate comparison
  `zlCompactSupportFrobenius`, fixed completed-to-ordinary lambda and
  `sfQcqsCompactSupportRealization`. `rationalExchange` is its localization, with
  equality of the localized hom as its normalization. `beta` transports this to S.F
  using `S.ring.rationalLeft`. The common-stage beta includes the actual field-stage
  exchange through `S.common.commonComparison.q` and the published Frobenius-stage
  identifications. Its naturality is stated for every common-stage arrow.
- `purityFrobeniusConjugate` is literally `(PX.mapIso (γ K)).symm ≪≫ b K ≪≫ γ(PYK)`.
  The second conjunct is `F.map e.hom ≫ counit(PYK) =
  β.inv.app(GK) ≫ PY.map(counit K)`, exactly the requested counit characterization of
  the right adjunction mate of inverse exchange. The direction is inverse beta.
- The final theorem is the conjunction of that same property in the E category and
  in the common-stage Qbar category. Naturality quantifies all arrows and therefore
  includes the hom of every rational Weil isomorphism PYK≅K. No lattice or stability
  witness is a theorem parameter.

Dependency declarations used (full modules and principal names):

- `Sheaf.Paper.SfWeilSheafComplex`: `WeilConjectures.sfWeilComplex`,
  `sfWeilFrobeniusPullback`, `sfCommonStageWeilFrobeniusPullback`,
  `sfWeilPrimeInvertible`, `sfWeilStagePullbackIdentification`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `AlgebraicGeometry.SmoothOfRelativeDimension`.
- `Sheaf.SixFunctors.SchemeGeometricFrobenius`:
  `WeilConjectures.PurityFiniteSetting.schemeGeometricFrobeniusComparison`;
  the underlying actual scheme maps are `FiniteFieldDatum.geometricFrobenius`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `rationalDerivedTensor`, `commonStageDerivedPullback`, `commonStageDerivedTensor`,
  and their recorded object formulas. The integral operations are the existing strict
  reduction/Roos constructions, not copies defined in this delivery.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `WeilConjectures.sfQcqsCompactSupportRealization`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `WeilConjectures.ConstructibleExceptionalCoefficients.System`, its operations,
  `rationalLeft`, rationalization comparisons, field and common-stage comparisons.
- `WeilConjectures.Compactification.Refinement`:
  `AlgebraicGeometry.Compactification` and `.Refinement`.
- `Sheaf.Paper.SmoothPurityMap`: `PurityFiniteSetting.smoothPurityMap` is the
  finite canonical diagonal purity used by the finite trace normalization; the
  existing finite integration packages expose its inverse and exceptional counit.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv` and its
  counit characterization. We state the node's equivalent counit equation directly.
- The unusable coefficient-twist binding is repaired below. The recorded upstream
  rational-purity binding is retained; the new definition node owns its realization interface. The imports give the
  statement dependencies and the actual canonical constructions used here. The
  proof-only dependencies remain in the unchanged DAG proof plan; modules are
  not imported solely to prepare future stage-three proofs.


Edge cases checked: d=0 gives the unit/shift-zero constraints, not a dropped case;
the identity morphism uses the same normalized counits; the empty scheme and zero
object make both equations well-typed identities. Torsion lattices are permitted:
`representativeTor` covers every object of the actual rational localization. An
isomorphism given by multiplication by ell or ell inverse need not preserve the chosen
lattice but is among the quantified rational arrows. Different common-stage objects
and arbitrary enlargement of their finite coefficient field are covered by the
published coefficient associators and comparison maps, including identity transitions.
The semilinear Frobenius square is used throughout, even over Spec k₀.

Searches made: `msearch.py NA <item> leanfinder` with “smooth purity naturality rational
coefficients geometric Frobenius adjunction mate” found eight unrelated general
naturality/mate declarations. Loogle `CategoryTheory.mateEquiv` found the generic mate
calculus but no geometric statement. Mathlib grep
`purity.*naturality|naturality.*purity|frobenius.*mate` found three closed-monoidal
functor occurrences. The actual tool results are in `searches.jsonl`. Searches of
`WeilConjectures/`, project `lean/Sheaf`, the DAG records and the upstream declaration
index found the existing operations and the insufficient upstream realization interfaces, and
no exact instance of the item's statement. The dependency notions use the existing
coefficient lines, tensor, inverse-image and stage machinery; no second coefficient
category, twist object or derived tensor was introduced. The return explicitly authorizes the new canonical-realization definition below.

## New nodes

`def-pur-canonical-rational-purity-realization`, in the item's chapter and unit,
defines the canonical sf realization of the transported purity family. Its module
is `Sheaf.Paper.RationalSmoothPurityCanonical`; the primary declaration is
`WeilConjectures.RationalSmoothPurityCanonical.rationalIso`, with `commonIso`
and its trace transports listed in `lean.declarations`; the source transports
are owned by the separate definition below. This is the
new definition expressly permitted by the maintainer's H13 return. It leaves
the existing PBC purity theorem and its statement dependencies unchanged.

The datum P and finite-type separated smooth domain are the module's explicit
section variables. `c` and `S` are the compactification and normalized operations
of the item. `orientation`, `IsNormalizedTrace`, and the new comparison theorems
fix the reconstructed coefficient-unit orientation by the finite smooth-purity
trace. `integralTraceTransposeOfOrientation` and `integralMap` give the specified
projection/trace adjoint on each integral input. `representative` retains the
actual integral representative, without a Weil-stability assumption.
`rationalSourceComparison` supplies inverse localization shift followed by the
published object formulas; `rationalIso` localizes the specified integral map
and applies the exceptional coefficient mate. `sourceScalar` retains the
canonical tensor, line, pullback and coherent shift factors. `commonIso` uses
the literal finite stage, the small-field equivalence and the common-stage
exceptional comparison; `selfStageUnit` retains identity transitions.
`rationalIso_scalar` states the actual finite-extension equation.

Source: the current blueprint prop-weil-operations proof sentences 3--4 and
rational-purity proof Steps 1--2. `blueprint_refs.py ancestor` returns
`prop-weil-operations`; `blueprint_refs.py search 'canonical rational purity'`
returns zero matches. Mathlib LeanSearch and LeanFinder returned unrelated
smoothness declarations; Loogle returned no declaration for the queried shift
name; Mathlib grep returned zero hits. The JSON records the exact tool queries
and returned names/notes from `searches.jsonl`. Source-tree and DAG searches
found the existing existential adic reconstruction and PBC transport theorem,
plus `AdicPurityScalarNaturality` for a separately supplied operations system;
none supplies these canonical maps at the item's sf endpoints. The existing
`lem-pur-tower-trace-purity-comparison` is a comparison theorem about families,
not a definition of this data. The source helpers are therefore assigned to
the new definition, and no existing coefficient category, line, tensor,
localization, shift or adjunction is redefined.

`def-pur-canonical-purity-source-transports` owns the rational/common-stage
source functors and their scalar/stage comparisons, together with the strict
completed-to-ordinary tensor source comparison. Its module is
`Sheaf.Paper.PuritySourceTransports`; the primary declaration is
`WeilConjectures.RationalSmoothPurityCanonical.rationalSource`. The realization
node cites it. Its first part is `rationalSource`, `sourceScalar`, `commonSource`
and the literal-stage comparisons; its second part is the strict quotient
augmentation, its descent and `tensorToOrdinary`. All definitions use existing
coefficient objects and operations; the chosen comparisons are uniquely pinned
on tensor generators or all good K-flat presentations. This is source data for
the preceding canonical-realization definition, not a second purity theorem.
The same exact Mathlib, project and DAG searches recorded above found no source
functor/comparison interface at these endpoints. The distinct existing
`def-pur-adic-purity-reduction-source` constructs finite reductions, not these
rational/common-stage source and ordinary tensor transports. Source is the same
blueprint proof sentences 3--4. The supplied node records the self-contained
source formulas, every cited dependency, and the exact search results.

## Dependency modules

`def-weil-frobenius-coefficient-twists` is repaired in
`Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`. The upstream
`AlgebraicGeometry.WeilSheaf.nonempty_equiv_cohomology_tateTwistSheaf` is a
cohomology equivalence, rather than the canonical coefficient-line structure or
Weil twisting functor required by the node. The module retains the genuine
clauses 1--5: root-tower map, signed tensor/evaluation comparisons, normalized
ordinary-to-completed comparisons, finite/integral/rational/common-stage line
maps, heart membership, and the actual tensor-defined functors on fixed pairs.
It now ends immediately after `FrobeniusCoefficientTwists.commonWeilSheaf`.
It contains no rational-purity source or purity-family declaration. Its node
changes only `lean`, with the reason and repaired interface in `lean.note`.

## Repair of L return at 23d934df8b9f

H5, rational shift: removed `rationalSourceComparison_existsUnique`, whose
heterogeneous identity assertion required an unjustified equality of shifted
objects. `rationalSourceComparison` now has actual data: apply rational tensor
to the inverse localization `commShiftIso (2*d)` on the coefficient line and the
identity on the pullback factor, then transport by `rationalIntegralSource_eq`.
That equality uses the published integral tensor/pullback object formulas with
an integrally shifted line; it asserts no equality of rational and integral
shift functors. The localization is pinned only at one, and its coherent
comparison is used at `2*d`, including zero.

H5, scalar shift: the general scalar comparison is pinned only at degree one.
It is a definition used explicitly by `sourceScalar`, not another registered
instance. The common-stage line comparison uses the landed
`GeneralAlgebraicallyClosedCoefficients.transitionCommShift` instance. Both
are normalized by the same degree-one integral comparison; shift coherence
provides every integer shift. No all-integer heterogeneous identity is assumed.

H13, purity ownership and dependency inversion: withdrew the sandbox dependency
node `thm-pur-rational-and-qbar-purity` and its module assignment. Its published
upstream record is retained unchanged. The declarations formerly in
`RationalSmoothPurityCanonical.lean`, and the
purity-source helpers formerly in the Frobenius-twist module, now belong to
`def-pur-canonical-rational-purity-realization` and its source-transport
definition `def-pur-canonical-purity-source-transports`. Each module is owned by
exactly one new node and lists every authored declaration in `lean.declarations`.
These declarations are the canonical realization
of the stated purity in its sf rational/common-stage categories. They do not
rebind the PBC purity node to an sf statement. The item explicitly cites the
landed `cor-pur-adic-and-rational-smooth-dualizing-complexes`, which owns the
coefficient/root-line and field-model helpers, and the adic reconstruction node.
The dependency direction is item -> new definition -> corollary -> upstream purity;
there is no reverse dependency of upstream purity on the corollary.

The realization map is fixed by the reconstructed coefficient-unit orientation
and the projection/trace transpose. `finitePullUnit` and `finiteUnitSource`
construct the finite source identifications from the existing constant-unit
pullback, site comparison, shift reassociation, and tensor left unitor.
`finiteIntegration_smoothPurityMap` identifies the actual integration used in
normalization with the counit transpose of the recorded `smoothPurityMap` at
the coefficient unit, after these explicit comparisons. All arrows in that
equality are specified constructions; no arbitrary source or target iso occurs.
`orientation_eq_adic` identifies the chosen unit orientation with an adically
reconstructed one satisfying these finite trace equations.
`integralMap_eq_adicTraceTranspose` then identifies the map on every integral K
with the projection/trace transpose of that reconstructed orientation. The
finite trace premise is used only for the rank-one unit, where it determines
the orientation; no uniqueness of general coherent lifts is asserted.
`rationalIso` is its actual localization through the counit-preserving
coefficient mate, and `commonIso` uses its literal finite-field transport and
the specified common-stage comparison. Thus the finite canonical map is
connected to the family used in the main theorem by equations of maps.

H13, advisory dependency audit: the item now cites
`def-zl-frobenius-compact-support-comparison` and
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, as requested. It also
cites the landed shift-data and smooth-trace nodes used in the source and
counit comparisons. No statement, proof plan, or dependency-node non-lean
field changes. The new definition owns the previously missing canonical realization data;
its hypotheses and coefficient categories are exactly those of the item.

## Second reading by NA

The dispatch brief requires self-delivery and prohibits additional agents.
This is my self-check; the maintainer supplies the independent reading.

I compared the saved packet with the return and current shared node records,
then rebased the node copies by retaining current non-delivery fields. I read
the current blueprint proof sentences 3--4 and the upstream adic/rational
realization statements through `scompile.py --source`. Those upstream theorems
package normalized-system reconstructions and do not themselves expose the
canonical sf family, which is why the family has its own realization-definition
node. The dependency-node purity statement is not rebound.

The main theorem retains all finite-field, coefficient, geometric descent,
smoothness, separatedness and compactification hypotheses. Its first conjunct
quantifies every rational arrow. Its second conjunct uses
`(PX.mapIso gamma).symm`, then b, then gamma at PYK, and the counit equation
uses inverse beta. Both rational and common-stage coefficient categories are
present, without a stable integral Weil lattice. The shift comparison was read
against the actual scalar-localization triangulation: only the shift at one
has an identity normalization, so the repaired source uses commShiftIso at 2d.
The finite unit comparison retains the zero-dimensional and identity cases.
Purity-source helpers have been removed from the twist dependency record.
The upstream purity record and its statement dependencies are untouched.

## Validation

All compilation and delivery use the prescribed launcher wrappers. No global
build, direct git command, edit to a shared/live source, launcher-script edit,
or compiler bypass was performed. Per-file compiler and dry-run results are
recorded below after validation of this repair.

The first unsplit repair compile reached the 60-second limit in the item
module (`scratchpad/repair-first-compile.log`). Source transports and the
realization family were then assigned their own definition modules. Superseded
compiles were interrupted. The final four-module wrapper run is recorded in
`scratchpad/repair-four-module-compile.log`; every delivered module is compiled
separately, in dependency order, at the original limit.

The first four-module dry run diagnosed a missing inferred transition-shift
instance and a class-definition reducibility warning in the source module.
The source now uses the fully qualified landed transitionCommShift explicitly;
`scalarShift` has `@[instance_reducible]` and remains a definition, not a
registered instance. The next run passed those source declarations and reached
the realization module. A specialized finite-unit probe reached its limit, so
`finitePullUnit` and `finiteUnitSource` were rewritten for an abstract finite
coefficient datum Q with explicit result types. Their specializations keep the
same maps. They are marked irreducible to avoid downstream expansion of their
comparison data. No shift normalization or map was replaced by an arbitrary
choice. The current full wrapper run is
`scratchpad/repair-generic-family-compile.log`.

## Resumed packet self-check (2026-10-18)

Read the saved packet and compared its repair with the returned version. The
source comparison uses inverse localization commShiftIso at 2d; the general scalar
comparison is normalized only at one and does not register another transition
instance. The new realization and source nodes own the purity helpers, and the
upstream rational-purity binding remains unchanged. The finite integration theorem
relates its map to smoothPurityMap, and the orientation/trace-transpose equations
retain the adic reconstruction normalization. The main statement quantifies every
rational/common-stage arrow and retains the inverse-exchange counit equation.
Compared the delivered node copies with current shared records: the item differs
only in lean and allowed added stmt_deps; the twist dependency differs only in lean.
Self-check found a repeated public import modifier in the main module; reduced it
to the single intended public import without changing any declaration.

## Resumed validation result

Three prescribed deliver2.py --no-push attempts were made on 2026-10-18.
The first overlay failed at the read-only shared DerivedPullbackTensorHom
prerequisite (60 seconds); server confirmation then timed out in the read-only
ProEtaleConstantReductionTower prerequisite. The next two runs again reported
that overlay failure, and their server confirmations progressed through cached
prerequisites but both timed out in Sheaf.Paper.DerivedPullbackTensorIso at
60 seconds. Logs: scratchpad/resumed-packet-dry-run.log and
scratchpad/resumed-packet-dry-run-2.log. The first run compiled the repaired
FrobeniusCoefficientTwistsCanonical module before the prerequisite failures.
No successful final four-file compile, preflight OK, or push is claimed. The
wrapper and read-only published modules were not modified or bypassed, and
the limit was not raised. The remaining blocker is the prescribed compile
service repeatedly failing on published prerequisites, before final validation
of this packet. The repaired sandbox and the import cleanup are retained.

## Continued repair self-check (2026-10-18)

The required initial dry run reached the saved realization module and timed out
on both overlay and server confirmation. An isolated finite-unit probe and a
reduced-heartbeat diagnostic located expensive kernel checks in the comparison
unit and tensor-unitor constructions. The repair reuses the existing published
ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso from
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison.
The tensor unitor is assembled through tensorUnitFromPresentation over an
abstract monoidal category and then specialized to the existing finite tensor.
These are the same canonical factors as before; no new choice or axiom is used.
The isolated four-helper probe compiled cleanly through scompile.py in 17.0 s
and server confirmation in 9.1 s (scratchpad/finite-existing-repair2.log).
The new helper declarations are recorded under the existing realization node.

The item copy was compared to the current shared node: only lean and additions
to stmt_deps differ. The coefficient-twist dependency's non-lean fields remain
unchanged. The item retains d=0, both coefficient cases, every rational arrow,
the order inverse pulled-back gamma, b, gamma at PYK, and inverse beta in the
counit equation. The smoothPurityMap equation and adic trace normalization
remain in the realization module.

## Continued validation and record repair (2026-10-18 UTC)

The prescribed saved-packet dry run reached preflight after its four-file
compilation check. Preflight reported 16 record issues: grouped bracket
citations were not recognized as individual dependency citations, and the two
new nodes recorded an empty grep output as an empty string. Each dependency
now has its own bracket citation; the recorded empty output is explicitly
reported as "No matches (empty grep output)." The three level-specialized
finite-operation helpers are also included in the realization node's declaration
list. No Lean signature or mathematical statement changed in this record repair.

Self-check of the saved repair confirms the degree-one scalar-shift pin,
commShiftIso at 2d in rationalSourceComparison, the finite smoothPurityMap
transpose equation, and the adic unit trace normalization. The twist dependency
owns only its original Frobenius clauses; the two new nodes own the source
transports and the purity family. Comparison with current shared node files
found only the authorized lean change for the dependency and lean plus added
statement dependencies for the item.

The repaired packet passed deliver2.py --no-push: commit aff8ddbc85 passes
preflight and compiles all four delivered files. Log:
scratchpad/resume5-record-repair-dry-run.log. The final push is performed by
the prescribed deliver2.py wrapper after this successful check.

## Repair of L return at 7d346b1c1aa7

The saved packet first passed the required deliver2.py --no-push check
(commit c6f4f2a392). That success predates this return repair.

H2: removed cor-pur-adic-and-rational-smooth-dualizing-complexes and
thm-pur-adic-reconstruction from the item's stmt_deps. The former was used
only via the abbreviation AdicSmoothDualizing.fieldStage; the latter supplied
no declaration used by the item. The theorem now writes `.rational ⟨P.extension⟩`
in all three operation endpoints, exactly the data of that abbreviation.
Updated lean.statement verbatim from the theorem signature. Added
def-pur-canonical-purity-source-transports to the item's stmt_deps, since
RationalWeilPurity.H, CommonWeilPurity.H and CommonWeilPurity.b use its
rationalSource, commonSource and commonShiftedLine. The earlier report's
claims that the item cites the dualizing corollary and reconstruction theorem
are superseded by this correction. The realization node retains its accepted
source and normalization dependencies; no mathematical statement or proof
plan is changed. The advisory suggestion of an additional existing definition
node is unnecessary for the requested direct field-stage rendering.

Self-check of this repair: read the current item and the source-transport
node and module, and compared the saved records with current shared records.
The item differs only in lean and added stmt_deps; the twist dependency
differs only in lean; both source/realization definition nodes remain new.
Read fieldStage's definition: it is exactly `⟨P.extension⟩`. Thus the
replacement retains the rational coefficient field and the same F, G and
adjunction. H retains the canonical source functors and b retains the shifted
common-stage line. All hypotheses and both naturality/mate conjuncts are
unchanged, including d=0, identity transitions, every rational arrow and
the inverse-beta counit equation. No earlier accepted substance repair was
reverted. The dispatcher's prohibition on additional agents makes this a
self-check; the maintainer supplies the independent review.

## Validation of the 7d346b1c1aa7 return repair

The prescribed scompile.py four-file run completed cleanly. The library
checks took 16.6 s (FrobeniusCoefficientTwistsCanonical), 32.8 s
(PuritySourceTransports), 37.0 s (RationalSmoothPurityCanonical), and 22.3 s
(RationalWeilPurityNaturalityMate); the corresponding sandbox checks also
passed within 60 seconds. There were no errors or unexpected warnings.
The record self-check verified exact lean.statement equality, JSON formatting,
the corrected dependency set, and unchanged non-delivery fields against the
current shared records. Final preflight and push use deliver2.py below.
