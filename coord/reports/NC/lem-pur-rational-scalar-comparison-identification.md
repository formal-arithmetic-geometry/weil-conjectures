## Worker report

The module `Sheaf.Paper.RationalScalarComparisonIdentification` states the item as
`rationalScalarComparisonIdentification : Result D C f d S I`.
The only postponed proof is this theorem. All helper definitions have actual data;
`Result` is the existential-and-equational conclusion, not an extra assumption of the theorem.
The result is quantified over the supplied simultaneous integral datum `I` and
the specified exceptional coefficient system `S` used in that datum.

Hypotheses and objects, clause by clause:

- `D : FiniteFieldDatum` and `C : D.CoefficientDatum` bind the finite-field and
  coefficient datum, including the prime distinct from the characteristic and
  the fixed algebraic closure. `Field D C` is the existing finite-subfield index.
- `X Y : Scheme.{u}` with `Over (Spec (.of D.k))`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` on their structural morphisms are exactly
  separated finite-type k-schemes. The morphism `f` is a k-morphism (`IsOver`),
  separated and finite type, and `SmoothOfRelativeDimension d f` with `d : ℕ`
  states the smooth pure nonnegative relative dimension. These are the same
  geometry binders as the recorded integral data; no noetherianity, nonemptiness,
  unramifiedness of coefficient extensions, or coefficient-universe equality is
  added as a new hypothesis.
- The integral category is the dependency's `Cat D C E W`, namely
  `finiteTorConstructibleIntegralCategory`. The rational category `RCat` is the
  existing `sfRationalConstructibleCategory`, the raw Hom localization in the
  intrinsic coefficient presentation. `Q` is precisely the system's recorded
  `ConstructibleExceptionalCoefficients.rationalization` (the finite-Tor inclusion
  followed by raw localization). This uses the established intrinsic presentation
  of the categories, rather than another category definition or a Karoubi envelope.
- `I : AdicPurityScalarNaturality.Data D C f d S` is the complete supplied
  hypothesis: actual integral functors, exactness and linearity, purity `gamma`,
  canonical `a`, counit-mate `b`, completion identifications, and all coherence.
  Integral `source`, `target`, `scalar`, `associator` and `scalarUnit` are reused.
- `T` is the existing `sfRationalScalarExtension` along the actual inclusion
  `IntermediateField.inclusion h`. `scalarLocalization` identifies `Q_F C` with
  `T Q_E` by a natural isomorphism; `scalarNormalization` fixes its component to
  the actual `scalarBridge` (the quotient completion chi followed by the
  system's strict-tower realization). `HEq` here records equality across the
  existing strict-versus-ordinary endpoint presentations; it is equality of
  the arrows, not mere existence of an isomorphism.
- `alpha`, `unit` and `tShift` are the existing rational tensor associator,
  tensor unitor and integral-normalized shift. `scalarUnitNormalization`,
  `scalarCompositionNormalization`, and `scalarLocalizationShift` retain their
  integral normalizations. `scalarExact` records exactness for those shifts.
  A repeated extension is normalized through this unitor; it is not replaced
  silently by a literally equal functor.
- `H` is `RationalSmoothPurityCanonical.rationalSource`, the existing line-first
  tensor presentation of `Lf_E^*(-)(d)[2d]`, with its canonical tensor symmetry
  and shift convention. `O` is the system's rational operation and `G := O.G`
  is its specified exceptional inverse image. `hLocalization` and the fixed
  `gLocalization` identify the integral operations after `Q`; since these are
  natural isomorphisms, their object and map actions are both included.
  `SourceLocalizationNormalization` additionally pins every source component to
  the actual integral twist/tensor/symmetry/shift/completion construction,
  through the defining rational pullback/tensor object equalities.
  `hLocalizationShift` and `gLocalizationShift` retain the prescribed shifts.
  `hExact` is exactness of the identified source functor.
- `eta` is a natural isomorphism `H ≅ G`. `etaLocalization` gives exactly the
  localized `I.gamma` components through the two operation identifications.
  `etaShift` supplies its shift equation.
- `a` is a natural isomorphism `H_E ⋙ T_X ≅ T_Y ⋙ H_F`. Its component is fixed
  by `aCanonical` to the existing canonical `sourceScalar`, whose data are
  rational pullback/tensor/Tate-line/shift comparisons. This is equality of
  isomorphisms in their existing endpoint presentations, not a new comparison.
- `b` is defined directly as the existing
  `S.fields.rationalComparison(...).b`. It is never chosen using `eta`.
  `c` is that same system's compact-support comparison. `coefficientTranspose`
  is the actual adjunction Hom bijection applied to
  `c.inv ≫ T_Y.map(counit_E)`; `counitMate` identifies `b` with this transpose.
- `aLocalization` and `bLocalization` state the two localized integral comparison
  equations. `LocalizesComparison` spells out the equality of the two paths
  using the four localization identifications. Its parameters are actual
  functors/isomorphisms; it introduces no additional mathematical assumption.
- `aShift` and `bShift` use the explicit inherited composite `CommShift`
  structures. They make the comparisons exact natural isomorphisms between
  the stated exact functors, with these particular shifts.
- `puritySquares` uses `PuritySquares`, whose first conjunct is the first displayed equation in the node, using Lean's
  left-to-right `≫`: `T_X.map eta_E.hom ≫ b.hom = a.hom ≫ eta_F.hom`.
  The second conjunct is exactly its second displayed equation:
  `b.inv ≫ T_X.map eta_E.inv = eta_F.inv ≫ a.inv`.
- All isomorphisms are natural on the entire raw rational categories, not just
  on integral arrows or a collection of lattices. The two squares quantify over
  every rational `K`. Naturality of their composites follows from their being
  functors and natural transformations. `aUnit`, `bUnit`, `aComposition`,
  `bComposition`, and the shift fields provide identity, successive-extension,
  and shift compatibility for the square; inverses inherit these same equations.

Dependencies read and used (module; declaration):

- `Sheaf.Paper.PurityFiniteSetting`; `PurityFiniteSetting`, `FiniteFieldDatum`
  and its coefficient datum (the latter are the actual binders).
- Mathlib smooth morphisms; `SmoothOfRelativeDimension` and `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, scheme `Over` / morphism `IsOver`.
  The scheme-properties node is a collector; its concrete property classes are
  used directly, rather than inventing a Lean declaration for the collector.
- `Sheaf.Paper.SfIntegralConstructible`; `sfIntegralConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites` / its imported `FiniteTorAmplitude`;
  `finiteTorConstructibleIntegralCategory`.
- `Sheaf.Paper.PbcRationalCategory`; `Scheme.PbcRationalDerivedCategory` and
  raw scalar localization; the operation system uses the established intrinsic
  `sfRationalConstructibleCategory` presentation of those coefficient categories.
- `Sheaf.Paper.DerivedPullbackTensorHom`; `rationalDerivedPullback` and
  `rationalDerivedTensor`, through the canonical source definition.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`;
  `sfRationalTwistingCoefficient` and the integral twist, through that same source.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`;
  `ConstructibleExceptionalCoefficients.System`, its actual operations,
  `rationalizationComparison` and `rationalComparison`, with their counits.
- `Sheaf.Paper.AdicPurityScalarNaturality`; `Data`, `source`, `target`, `scalar`,
  `scalarBridge`, `scalarUnit`, `associator`, `composeShift`, `ShiftCompatibility`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`;
  `integralScalarExtensionOfUniverses` (the strict integral construction used by
  the recorded scalar system; not independently reimplemented here).
- `Sheaf.Paper.PbcScalarExtension`; `Scheme.pbcCoherentScalarExtension`, with
  its already-recorded intrinsic `sfRationalScalarExtension`, scalar associator
  and unitor as used by the exceptional system and canonical source transports.
- Added already-landed dependency `def-pur-canonical-purity-source-transports`:
  `Sheaf.Paper.PuritySourceTransports`;
  `RationalSmoothPurityCanonical.rationalSource`, `sourceScalar`, `scalarShift`.
  This avoids reconstructing the canonical source map in this delivery.

Edge cases checked before finalizing the statement: `E = F` uses the actual
unitor rather than an omitted identity case; chains `E ≤ F ≤ L` include repeated
fields; no unramified coefficient hypothesis excludes ramified extensions;
`d = 0` retains the zero twist and shift without positivity; empty schemes and
zero objects are not excluded; all rational morphisms, including scalar multiples
and sums with denominators, are covered by the natural transformations; shifts
range over ℤ through `CommShift`, not only nonnegative degrees.

Searches for an exact existing statement:

- `msearch.py leanfinder`, query “Localizing smooth purity natural isomorphisms
  and coefficient scalar comparisons preserves counit mates and coherent inverse
  equations”: generic adjunction localization hits, no exact geometric statement.
- `msearch.py loogle`, query `CategoryTheory.Adjunction.localization_counit_app`:
  the generic counit lemma only, not this coherent coefficient identification.
- `msearch.py grep`, `localization_counit_app|natTransExtension`, subdirectory
  `CategoryTheory`: generic localization declarations, no exact match.
- `msearch.py leansearch`, “Localization of integral smooth purity isomorphism
  and counit normalized exceptional scalar mate”: generic localization results
  and unrelated algebra localization results, no exact match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `rationalScalarComparisonIdentification|rational.*[Pp]urity|[Pp]urity.*[Rr]ational`:
  no existing theorem giving the present statement. The upstream module
  `WeilConjectures/EtaleCohomology/Purity/Smooth/Rational.lean` only packages an
  arbitrary realized lattice isomorphism through rationalization, explicitly
  disclaiming the full rational purity statement. The canonical source transport
  module gives the maps, and is reused, rather than duplicated.

The current blueprint was read at `literature/blueprint/latest`, especially
`sk-thm-purity-transport.proof.md` Steps 2--4 and the rational adjunction proof.
No statement correction, new node or statement dispute. The compile-interface dependency
repair is described below.

## Second reading by NC

The dispatcher requires this worker to deliver directly and forbids starting
other agents; the maintainer supplies the independent review. This section
records the author's second clause-by-clause reading, not a second worker's
independent review. I checked the directions and endpoints of both purity squares,
the inverse comparison, the counit transpose, repeated-field and three-field
associator equations, and every explicitly supplied shift. The same system `S`
is used in the integral datum, rational operations and coefficient comparisons.
The categorical helpers `LocalizesComparison`, `PuritySquares`, `UnitEquation`
and `CompositionEquation` only abbreviate their fully displayed component equations. No maps are postulated as unconstrained hypotheses.

Compiler elaboration originally expanded the completed-coefficient category
inside component equations. Explicit functor signatures and a generic categorical
path-equality helper preserve the statement while avoiding that expansion.

## Returned delivery repair: H3

The independent review of immutable head `78685dae61c9` found that
`hLocalization` had no component normalization. Its shift and scalar equations
allowed simultaneous replacement of it and `eta` by their negatives. This
changed the intended localized integral purity map. The repair pins the source
identification itself, before the existing equation transporting `I.gamma`.

- `lineComplex` is the actual single complex of `integralTwistLine`, whose
  derived object is the existing `sfIntegralTwistingCoefficient`.
- `twistToShiftedTensor` composes `siteSheafTensorRightIso`, the inverse
  component of `curriedBraidingNatIso`, `mapBifunctorSingle₁Iso` inverse, and
  `mapBifunctorShift₁Iso` inverse. Thus it sends the actual termwise twist to
  the tensor with the shifted Tate line first. It introduces no arbitrary map
  or comparison isomorphism.
- `shiftedLineLocalization` uses `DerivedCategory.Q.commShiftIso` and
  `DerivedCategory.singleFunctorIsoCompQ` to identify that shifted complex
  with the shifted integral coefficient object. The inclusion shift comparison
  then identifies it with the underlying object of the shifted constructible line.
- `integralSourceComparisonOnGood` starts with any good representative of
  the actual integral pullback. It composes the termwise exact-functor
  factorization, derived localization shift, the preceding chain comparison,
  `RationalSmoothPurityCanonical.tensorAugmentation`, inverse
  `integralCompletedTensorComparison`, and the representative isomorphisms.
  Its direction is the integral source to completed tensor with the shifted
  line first. Each factor is existing actual data.
- `sourceObjectIdentification` uses exactly the object clauses of
  `rationalDerivedPullback_existsUnique` and
  `rationalDerivedTensor_existsUnique`, together with the inverse localization
  shift comparison on the Tate line, not a chosen automorphism.
- The new conjunct `SourceLocalizationNormalization ... (hLocalization E)`
  equates each component, after this object identification, with the raw
  rationalization of `integralSourceComparisonOnGood`. It quantifies over
  every good representative and every representative isomorphism; the
  shifted single line is asserted good, so this test is not conditional on
  an unavailable line model. Good resolutions of the pullback exist by the
  recorded good-complex localization. Hence the normalization fixes all
  integral components, and naturality fixes the rational map action.

The unchanged `etaLocalization` equation now says that `eta` is the transport
of `Q(I.gamma)` through these pinned source components and the already fixed
exceptional comparison. A sign change of `hLocalization` violates the new
equation (except on zero objects, where there is no distinct sign change).
The shifts are still fixed through the same source localization shift square.

Consumer audit: `thm-pur-rational-and-qbar-purity` Step 2 obtains the actual
localized integral purity; `lem-pur-rational-normalized-purity-diagrams` Step 3
and `lem-pur-rational-purity-exchange-endpoints` Step 3 retain that same
normalization. No DAG statement changed and no citer needs editing.

Repair searches: `rg` in `PuritySourceTransports`,
`DerivedPullbackTensorHom`, `CoefficientTwistsDetailed`,
`IntrinsicCoefficientTwistsUnrestricted`, `IntegralDerivedOperations`,
`IntegralAmbientOperationModels`, and the Mathlib/FromJoel homology sources
and `TensorColimitsIndependentCoefficients` for `single`, `Shift`, `twist`,
`mapHomologicalComplex`, `braiding`,
`tensorOperationUnit`, and the two rational-operation existence-and-uniqueness
declarations located the existing factors listed above. The new helpers
package only the normalization of this item's comparison. They do not
define another tensor, twist, pullback, or localization.

Edge checks for the repair: the tensor symmetry is applied while the line
is in degree zero; the shift then moves onto the first tensor factor using
the actual unsigned first-factor constraint. This retains the sign convention
for all input complex degrees and all integer shifts. At `d = 0` it uses the
actual zero twist and zero shift; no positive-dimension assumption is added.
Empty schemes, zero complexes, repeated fields, ramified extensions and
coefficient towers remain admitted by the same geometry and coefficient
binders. The new goodness assertion is a conclusion about the fixed locally
free single line, not an additional hypothesis.

The shared-main node was compared directly with the retained returned packet:
its statement, proof, proof dependencies and existing statement dependencies are
unchanged; the packet only adds its Lean record and the already accepted landed
`def-pur-canonical-purity-source-transports` dependency. The six new helper
declarations are listed in `lean.declarations`. They belong to the source
identification already asserted by this item, so they require no new definition
node. The separately retained compact-support compile repair is described below.

## Current upstream and delivery scope

The live upstream projection-formula module now reuses the canonical derived
pullback/pushforward aliases and shortcut instances. The earlier split experiment
is archived under `scratchpad/previous-split-delivery/` and is not delivered.
This packet contains the item, the compact-support dependency repair, and the
finite-exchange opacity repair with its finite-proper consumer. All four modules
are under `lean/Sheaf/`, with their four node records and this report.

Against current main the item changes only `lean` and adds the already landed
statement dependency `def-pur-canonical-purity-source-transports`. Its statement, proof, and proof dependencies
are unchanged. The compact-support dependency changes only `lean`. All recorded
signatures are copied verbatim from their files. The item and compact-support
module each have exactly their matching theorem as their only postponed proof;
the additional dependency modules preserve their existing proofs. There are no data sorries,
diagnostic commands, auto-bound variables, or lines over 100 characters.

## Dependency modules

`def-sfb-finite-proper-exchange` retains the canonical mate construction with
`@[no_expose]` to avoid the downstream kernel timeout. Its signature and data
are unchanged. `det-thm-sfb-proper-base-change-finite` removes only the redundant
local irreducible attribute on that now opaque exchange. Its existing theorem
signatures and proofs are unchanged; details and validation appear below.


`det-prop-int-brown-construction` is included with a Lean-only repair of
`Sheaf.SixFunctors.IntegralLocalizingCompactSupport`. Its old literal total
left/right derived functor abbreviations repeatedly synthesized the full
canonical monoidal/K-flat/K-injective structures, exceeding the file limit.
The replacement `pull` and `push` abbreviations use the existing, definitionally
equal `AlgebraicGeometry.ProEtale.moduleDerivedPullback` and
`moduleDerivedPushforward` from `Sheaf.Paper.ModuleProjectionSectionArrows`.
The canonical shortcut instances for the module and sheaf categories are reused;
the existing internal-Hom construction is kept irreducible during elaboration.
The actual maps, adjunctions, functors, hypotheses, and all theorem clauses are
unchanged. There is no new arbitrary choice, data sorry, or additional hypothesis.
The module compiled cleanly in sandbox and library modes (32.5 s and 23.6 s).
Its own node changes only `lean`, with a note explaining the unusable compile
interface; the item imports its module non-publicly. This node is already in the
prerequisite closure through proof dependency `lem-coef-rational-operations`;
it is not an item statement dependency. This follows the return's authorization to repair a definition
and adapt its users in the same packet; no upstream source path is delivered.
The theorem signature in its node is now the exact multiline source signature.

The first fresh final-item run passed the previously failing projection module
but timed out while rebuilding this compact-support module. Its redundant
confirmation pass was stopped after the concrete repaired module passed both
compile modes. The final packet is being validated with both modules supplied,
in dependency order. Earlier split experiments remain archived and undelivered.


## Final validation

The combined dependency-order compile passed the complete transitive chain and
then found two stale local reducibility attributes on `sourceShift` and
`scalarShift`, whose live declarations are now opaque. Removing only those
attributes restored compatibility with the current API; no statement or map
construction was changed. Both delivered signatures and declaration lists were
regenerated from the final source. The final per-file compile, dry run, and
push outcomes are recorded below.


Final `scompile.py` completed with exit 0 and no diagnostics for both delivered
modules. The compact-support dependency passed in 32.5 s (sandbox) and 23.6 s
(library); the repaired item passed in 44.2 s (sandbox) and 46.8 s (library).
The supplied dependency and every rebuilt transitive consumer compiled within
the unchanged per-file limit. Full output: `scratchpad/final-repair-compile.log`.


`deliver2.py --no-push` printed `OK (dry run)` at `cd72b5d9725`:
all five packet files passed server preflight and compilation. The final packet
contains the item H3 repair and the compact-support definition-interface repair;
no archived split module or upstream `WeilConjectures` path is included.


## Returned delivery repair: H2 (e965812339fa)

Removed `det-prop-int-brown-construction` from the item's `stmt_deps` and changed
its `IntegralLocalizingCompactSupport` import to a non-public import. The theorem
node is already a prerequisite through `lem-coef-rational-operations`; the item
uses none of its declarations in its statement. Its Lean-only compile repair
remains in this packet, as expressly accepted by the return. The genuine source
notion `def-pur-canonical-purity-source-transports` remains a statement dependency.
The H3 source normalization, all maps, hypotheses, equations, and theorem
signatures are unchanged from the reviewed head. Relative to current main, no
existing statement dependency is removed: the theorem dependency was an addition
in the returned packet. The correction is substantive relative to e965812339fa.

The earlier validation above records the returned packet. Fresh compilation,
dry-run and delivery for this H2 correction are recorded below.

### Additional dependency compile repair

Fresh validation against the current committed server sources reached a kernel
`deterministic timeout` in the published private proof
`ProperOpenBoundaryZero.boundaryVanishing_finite`. Its finite proper exchange
expanded the exposed unit-square-counit derived-adjunction mate during kernel
conversion. The delivery therefore also retains the existing real definition
`AlgebraicGeometry.ProEtale.CondensedRing.finiteProperExchange`, owned by
`def-sfb-finite-proper-exchange`, with `@[no_expose]`. Its body and signature are
unchanged. Consumers need its named canonical arrow, not reduction of its mate
body; the source docstring still specifies exactly that construction.

`det-thm-sfb-proper-base-change-finite` receives a Lean-only consumer repair:
remove `finiteProperExchange` from its local `irreducible` list, because the
imported declaration is now opaque. All its theorem signatures and published
proofs remain unchanged. These two nodes are already in the prerequisite
closure; neither is added to this item's statement dependencies. The test
passed `ProperOpenBoundaryZero`, `ProEtaleProperOpenInterchange`, and the
compactification coherence/composition consumers that previously failed.
The two dependency records change only `lean`, with exact multiline signatures
and explanatory notes. No theorem is newly proved and no data is postponed.

Fresh H2 repair compilation succeeded (exit 0) for all four modules, with no
warning or error. Sandbox/library times were 14.8/20.8 seconds for the exchange,
24.5/22.0 seconds for compact support, 25.2/28.5 seconds for finite proper base
change, and 37.1/33.7 seconds for the item. Every delivered file stayed within
60 seconds. Full validation output is `scratchpad/h2-exchange-repair3.log`.
The earlier duplicate-import errors were resolved by the refreshed server
snapshot; no duplicate API or import workaround is included in this packet.

The prescribed dry run could not complete: its server compiler raised
`OSError(28, 'No space left on device')` while rebuilding dependencies and began
its automatic confirmation. A separate prescribed scompile retry independently
failed in `Sheaf.Paper.AmbientPullbackTensorCoherence` with
`resource exhausted (error code: 28, no space left on device)` (38.4 seconds).
The earlier complete four-file compile passed, as recorded above. No delivery
was pushed. Logs: `scratchpad/h2-final-dry-run.log` and
`scratchpad/h2-post-storage-compile.log`. Server storage cleanup is outside this
worker's writable sandbox and no cache, launcher, or live-library file was edited.

### Resumed retry after server-storage failure

The retained H2 changes were compared with current main: the item's only added
statement dependency is `def-pur-canonical-purity-source-transports`, no base
statement dependency is removed, the compact-support import is non-public,
and every delivered signature matches its node record. No prior delivery or
compile process remained active.

The resumed four-file scompile and two prescribed dry-run attempts again failed
with the same server-side diagnostic in AmbientPullbackTensorCoherence:
`resource exhausted (error code: 28, no space left on device)`.
To distinguish a source problem from storage/cache state, a scratch probe of
that module was compiled through scompile, then the exact current server source
was compiled through scompile: both passed (the exact source took 25.7/25.5
seconds). Neither probe is part of the packet. The unchanged four-file packet
still returns the identical 38.4-second storage-failure output, and both dry
runs explicitly report `nothing pushed`. This is a server compiler cache/storage
failure, not a Lean source error; no launcher or server cache was edited.
Logs: `scratchpad/retry2-compile.log`, `scratchpad/retry2-storage-exact.log`,
`scratchpad/retry2-fresh-compile.log`, `scratchpad/retry2-dry-run.log`, and
`scratchpad/retry2-dry-run2.log`. All repair files are retained for the retry.

### Successful resumed compilation

The subsequent retry against the refreshed server state passed all four files
in sandbox and library modes with exit 0 and no diagnostics. The item took
30.0/29.8 seconds; finite proper base change took 20.8/26.3 seconds.
The H2 correction and retained dependency repairs were unchanged. Full output:
`scratchpad/retry3-compile.log`. The earlier storage failures above are retry
history, superseded by this successful compile.


The first resumed dry run compiled successfully and found a metadata extraction
error: the signature search for `finiteProperBaseChange` matched the prefix of
`finiteProperBaseChange_of_coefficientIso`. The node record now contains the exact
full signature of its recorded declaration, selected with a declaration-name
boundary. No Lean source or mathematical statement changed for this correction.

The corrected packet passed `deliver2.py --no-push`: `OK (dry run)` at
`4ed7d68b928`, with all four modules compiled and server preflight passed.
Full output: `scratchpad/retry3-dry-run2.log`.
