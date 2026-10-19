## Worker report

This repairs the returned H3/H8/H11 defect. The old equations were naturality and
inverse identities, and did not express the asserted coherences. They have been
removed. The replacement `PointFibreDerivedTensorComparisonData` contains an
actual source `MonoidalCategory`, its specified tensor bifunctor and coefficient
unit, a `Functor.Monoidal` structure on the fibre, a source `SymmetricCategory`,
and a braiding square against the canonical Koszul braiding of the module derived
category. Thus associativity and both unit diagrams are genuine monoidal diagrams.
The extracted `tensorIso` has exactly the direction in the item; `unitIso` has
source the fibre of the coefficient object and target the actual tensor unit.
The structure alone deliberately makes no claim of canonicity.

The final theorem asserts a simultaneous family at the four stages together with
`PointFibreDerivedTensorCanonical`. That second record supplies canonical model
normalizations and actual changes of coefficient, as detailed below. Its fields
are part of the conclusion, rather than extra assumptions on the input.

Hypotheses and stages:

- `D : FiniteFieldDatum.{u}` retains the prime p, positive exponent a, cardinality
  p^a, finite field and its chosen algebraic closure k. The base is `Spec (.of D.k)`.
- `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` retains the distinct coefficient prime.
  The helper invertibility theorem only supplies the resulting residue-field
  instances; it does not add a hypothesis.
- `Ω`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]` retain the fixed
  algebraic coefficient closure. Finite extensions E and coefficient levels are
  quantified in the simultaneous family. Quantifying over all finite extensions
  is the usual presentation-independent version of choosing them inside Ω.
- The finite field `finite` uses the exact `finiteTorConstructible` full
  subcategory, exponent `n + 1`, its inclusion, `finiteIntrinsicDerivedTensor`,
  and the recorded `pointFiniteSections.mapDerivedCategory`. Its source
  constraints are restricted from `finiteIntrinsicClosed.monoidal` by a strong
  inclusion whose tensor and unit maps are the specified equality transports.
- The integral field uses `finiteTorConstructibleIntegral`, its actual inclusion,
  `constructibleIntegralTensor` (the completed tensor), and
  `pointFibreIntegralAmbient`. Its prescribed unit is the degree-zero completed
  coefficient sheaf. The target tensor is the ordinary derived tensor of modules
  over the same lifted O_E used by the recorded fibre; completion is not used as
  the target tensor definition.
- The rational field uses `rationalDerivedTensor` and `pointRationalFibre` followed
  by the finite-dimensional target inclusion. Its unit is the localization of
  the integral coefficient unit.
- The closed field uses `commonStageDerivedTensor` and `pointQbarFibre` followed
  by the recorded Ω-module realization. Its unit is represented at
  `Padic.finiteCoefficientBase` by the rational unit there.

Canonicity and the last two sentences of the item:

- Finite normalization is `PointFiniteTensorCanonical`: for every K-flat pair
  with finite-Tor constructible images, the comparison is conjugate via
  `finiteIntrinsicTensorModels.iso` and the exact-functor factors to the chain
  isomorphism sending every sheaf total-tensor generator to the tensor of its
  actual final-object sections. This pins the map on all resolutions.
- Integral normalization is `PointIntegralTensorCanonical`. Its `completion`
  map is specified on both coordinates of the actual Roos complex: `first`
  sends a tensor to the tensor of its two finite quotient units at every level,
  and `second` is zero. Its `comparison` equation identifies its localization
  with the inverse tensor comparison using `integralCompletedTensorComparison`.
  This does not choose an unspecified map into an inverse limit. `unit_model`
  normalizes the coefficient unit by the actual `pointIntegralSectionMap`.
- `PointFiniteTensorReductionData.square` uses two different levels m and n,
  the recorded quotient-calculus tensor comparison, the two stage tensorators,
  and a universal derived extension of ordinary coefficient modules. It includes
  m=n. The tensor arrow is the one whose closed transpose is the recorded
  `finiteIntrinsicReductionHom`; it is not the naturality of one tensorator.
  Its `fibre_model` is fixed on every K-flat quotient model by 1 tensor x.
  The integral `first` equation uses the same finite quotient units and tensor
  generators, and specifies the integral-to-finite reduction square before
  localization, including its tower projections.
- `PointIntegralTensorScalarSquare` uses the recorded `scalarTensorChain`, on
  the actual scalar-extended good complexes, and the completion maps over E and
  L. It is the chain representative of `scalarTensorOrdinary`, including both
  Roos coordinates. Its generator formula multiplies the two new scalars.
  `scalarTensorChain` itself is the diagonal Roos map of the recorded finite
  scalar tensor maps, so this also retains their finite-level compatibilities.
- `PointModuleScalarTensorData` retains the universal derived counit, strong
  monoidality, and the balanced representative formula a tensor (x tensor y)
  maps to (a tensor x) tensor (1 tensor y). Exact localization, field and stage
  scalar extensions have their counits fixed to `mapDerivedCategoryFactors`.
- `PointRationalTensorCanonical` identifies the rational tensor comparison with
  the localized integral comparison through `pointRationalLargeNormalization`.
  `PointFibreLiftTensorData` fixes the coefficient/carrier lift tensorator on
  pure tensors. `PointRationalTensorScalarSquare` is the actual square through
  `rationalTensorScalarComparison` and `pointRationalFibreScalarIso`; the latter
  includes the recorded `pointFibreTensorLiftIso`. The rational unit equation
  uses the same localization and coefficient/carrier lift.
- `PointQbarTensorCanonical` fixes the closed comparison at EVERY common finite
  stage L containing the compositum of the two input stages. Its formula uses
  `commonStageTensorComparison`, `StageSystem.isoToStage`, the rational
  comparison at L, canonical scalar tensor, and the prescribed point fibre on
  stage arrows. This retains `pointStageTensorSquare` through the recorded
  stage-fibre scalar comparison. It includes the identity-stage case. The
  closed unit formula is the scalar extension of the normalized rational unit
  at the actual base stage.
- Naturality is supplied by `Functor.Monoidal` and functorial tensor. Actual
  associators, both unitors and braiding occur in that structure and the
  displayed symmetry square. No compatibility field merely repeats hom or inv
  naturality, and no inverse identity is called a coefficient-unit constraint.

Dependency declarations used (the three original statement dependencies):

- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFiniteSections`,
  `pointFibreIntegralAmbient`, `pointRationalFibre`, `pointQbarFibre`,
  `pointFibreModuleLift`, `pointRationalFibreObjIso`,
  `pointRationalFibreScalarIso`, and `DerivedCategory.pointFdQbarRealization`.
  The scalar dependency imports supply `pointFibreTensorLiftIso`,
  `pointStageTensorSquare`, and the canonical field scalar tower.
- `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible`,
  `finiteTorConstructibleIntegral` and their full subcategories.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteIntrinsicDerivedTensor`,
  `finiteIntrinsicClosed`, `finiteIntrinsicTensorModels`,
  `finiteIntrinsicReductionHom`, `constructibleIntegralTensor`,
  `rationalDerivedTensor`, `rationalTensorScalarComparison`,
  `commonStageDerivedTensor`, and `commonStageTensorComparison`. Its recorded
  coefficient calculus supplies quotient models and tensor maps. Its integral
  dependencies supply the tensor tower, Roos complex, good representatives,
  `integralCompletedTensorComparison`, and `scalarTensorChain`.
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`: the universal
  fixed-second-factor ordinary module derived tensor, used for quotient rings.
- `DerivedCategory.perfectTraceCanonicalBraiding`: the existing canonical
  Koszul braiding, reused rather than chosen from an existence assertion.
- Mathlib: `Functor.Monoidal`, `SymmetricCategory`, derived exact-functor
  comparisons, module scalar extension, signed total tensor, single complexes.

Edge cases checked: exponent one is n=0; all identity quotients and identity
field embeddings are included; every common extension above the compositum is
included, without discarding the original representative. Zero complexes and
zero cohomology are permitted. Source site objects and arrows retain universes
u+1 and u; coefficient and module carrier lifts follow the recorded functors.
No equality of site universes, flatness assumption on finite quotient rings,
choice of an arbitrary comparison, or additional geometric hypothesis is added.

Searches:

- Retained packet searches in the node's `mathlib_searches` include LeanFinder
  queries on geometric fibre/derived tensor and exact monoidal derived functors,
  Loogle on fibre/tensor and mapDerivedCategory, and grep in Mathlib Sites and
  upstream WeilConjectures. Results were Tor, underived fibre monoidality,
  exact derived functors, and unrelated condensed declarations, not this item.
- This repair's `msearch.py` LeanFinder query on the canonical symmetric monoidal
  derived geometric-point fibre returned eight related underived tensor results;
  no four-stage statement. Loogle `"Monoidal", "mapDerivedCategory"` returned
  zero hits. Grep for fibre/monoidal/derived tensor in Mathlib Sites returned no
  matching four-stage interface. Results are retained in `searches.jsonl`.
- `rg` in the project and upstream located the exact dependency declarations
  above and the reusable `perfectTraceCanonicalBraiding`; none states the item.
  Current StageSystem source was read through `scompile.py --source` where the
  older local checkout lacked it.

No source statement correction or STATEMENT-DISPUTED issue is claimed. The node's
mathematical statement and proof remain unchanged.

## Second reading by Q62

This was a dispatcher-started worker with an explicit prohibition on starting
other agents. The self-check therefore does not claim an independent reviewer.
The returned head's vacuous coherence fields were checked against their exact
Lean types and removed. The new unit is an actual coefficient-unit comparison;
associativity and symmetry use monoidal constraints; reductions compare different
levels; scalar conditions use different fields and the recorded canonical maps.
Canonicality is tested against all representative models and all common stages.
The report no longer calls naturality or hom-inv identities these coherences.

## New nodes

The retained repair's helper interfaces are now split into six owned definition
modules so that every file is checked separately within the fixed compilation
limit. These nodes only define the data and predicates occurring in the item's
conclusion. They assert none of the comparison-existence results.

`def-sf-point-fibre-tensor-system` owns
`Sheaf.Paper.PointFibreDerivedTensorBasic`. Its primary definition is
`PointFibreDerivedTensorSystem`; the module also defines the strong symmetric
comparison data, extracted tensor and coefficient-unit maps, and the specified
four stage inputs. Its source is the constraints and coefficient constructions
in the item's source. The new record spells out the source tensor, coefficient
unit, strong functor, braiding square, and simultaneous family.

`def-sf-point-fibre-tensor-models` owns
`Sheaf.Paper.PointFibreDerivedTensorModels`. Its primary definition is
`PointIntegralTensorCanonical`. It defines the two-coordinate Roos normalization
from proof steps 3–5 of the item, including the actual coefficient unit.
The integral comparison equation is written as the inverse tensorator equalling
the fully conjugated completion map, using the inverse exact-sections factors
and the inverse recorded completed-tensor model. This is the same diagram after
composition with those isomorphisms. `HEq` retains equality across the two
recorded presentations of its endpoints.

`def-sf-point-fibre-tensor-reduction` owns
`Sheaf.Paper.PointFibreDerivedTensorScalar`. Its primary definition is
`PointFiniteTensorReductionData`. The module defines the universal module
scalar-extension data and the actual finite cross-level diagram, normalized on
K-flat quotient models. The source is the balanced quotient calculation in proof
step 9. The named `pointFiniteReductionTensor` has explicit endpoints and is the
recorded quotient-calculus tensor comparison used in the definition of
`finiteIntrinsicReductionHom`; it supplies no new tensor or arbitrary map.

`def-sf-point-fibre-tensor-rational-compatibility` owns
`Sheaf.Paper.PointFibreDerivedTensorRational`. Its primary definition is
`PointRationalTensorCanonical`; its other predicates specify the carrier lift,
unit, and cross-field square. The source is proof steps 6 and 9. It uses the
actual `rationalTensorScalarComparison` and `pointRationalFibreScalarIso`,
whose definition retains `pointFibreTensorLiftIso`.

`def-sf-point-fibre-tensor-common-stage` owns
`Sheaf.Paper.PointFibreDerivedTensorQbar`. Its primary definition is
`PointQbarTensorCanonical`; it also normalizes the common-stage coefficient
unit. The source is proof steps 7 and 9. Every common finite extension above the
compositum is quantified, using the recorded stage morphisms and their actual
point-fibre images, including `pointStageTensorSquare` in the stage-fibre map.

All six new nodes cite the original coefficient, finite-Tor and tensor
interfaces, together with their earlier helper interfaces where needed. Their
blueprint ancestor is `thm-sf-kunneth-relative`, with this item as the intermediate
node. Each new definition has real data or is an explicit predicate.

Searches for these missing interfaces were shared because they are the six
parts of the same canonical fibre-tensor comparison. The exact searches are in
each new node's `mathlib_searches`: LeanFinder on canonical finite/completed
point-fibre tensor comparison normalized on K-flat/Roos representatives returned
eight scheme residue-field tensor hits; Loogle on `"Monoidal", "mapDerivedCategory"`
returned zero hits; Mathlib Sites grep on point/fibre/derived tensor canonicality
returned zero hits. Project and upstream `rg` for the new system and canonical
predicate names returned no match. `blueprint_refs.py search 'point fibre tensor'`
returned zero blueprint nodes. Existing strong monoidal functors, derived tensor,
exact localization, scalar extension and coefficient constructions are reused;
none of the six source-specific predicates was already defined.

`def-sf-point-fibre-tensor-finite-models` owns
`Sheaf.Paper.PointFibreDerivedTensorFiniteModels`. Its definition
`PointFiniteTensorCanonical` is the finite K-flat generator normalization from
proof step 2. It was separated from the integral normalization to keep the
per-file check below the fixed limit. Its source and searches are the same
K-flat/point-fibre representative searches recorded above. The comparison used
in both normalization modules is the extracted strong tensorator, with explicit
source and fibre endpoint types in `pointFiniteTensorComparison` and
`pointIntegralTensorComparison`. These helpers change no map.

Self-check of the final split packet: all seven modules have exactly one owning
node; every primary signature is verbatim, and the declaration lists cover all
named declarations. The new nodes' bracketed citations match their statement
dependencies, every module explicitly disables auto-implicit variables, and all
lines fit the limit. Comparing the item with the shared node changes only `lean`
and the added helper `stmt_deps`. Finite targets are viewed in their ambient
module derived category through full inclusions; this does not assert that every
bounded finite-cohomology complex over a finite quotient ring has finite Tor
amplitude, or that the whole finite-cohomology category is monoidal.

## Retained-packet validation on 2026-10-17

The saved repair was retained, rather than replaced by the returned head's bare
isomorphism interface. In `PointFibreDerivedTensorComparisonData`, `strong` is
Mathlib's `Functor.Monoidal`: its inherited `associativity`, `left_unitality`,
and `right_unitality` fields contain the actual associator and unitor diagrams.
The separate `symmetry` field contains the source and target braidings. This
is used at all four stages. `PointFiniteSourceConstraints` additionally fixes
the finite source constraints through the recorded `finiteIntrinsicClosed`.
The comparison's coefficient unit is `unitIso`, with target the actual derived
module tensor unit.

The dry run diagnosed typing errors in the final integral scalar square. The
scalar variables now range over sections of the actual completed coefficient
sheaf at the final pro-etale object, as required by
`integralOrdinaryTensorSection`; both total-tensor generator maps now specify
their source complexes and use their underlying module linear maps explicitly.
The fraction-field extension functors now specify all three carrier universes
as u+1, consistently with `pointFibreRationalAmbient` and the rational model
predicate. These are presentation repairs: the canonical scalar square and
localization counit remain the same, and no assumption was added.

The cross-level square uses `pointFiniteReductionTensor`, which is exactly the
quotient calculus tensor map whose transpose defines
`finiteIntrinsicReductionHom`. The rational square uses
`rationalTensorScalarComparison` and `pointRationalFibreScalarIso`; the latter
is normalized through `pointFibreTensorLiftIso`. The closed comparison is
required at every common finite stage via `pointTensorQbarSourceNormalization`
and `pointTensorQbarInputNormalization`, whose stage maps use the recorded
fibre and hence `pointStageTensorSquare`. Canonicity is imposed on every K-flat
finite presentation, on both Roos coordinates integrally, through localization
rationally, and at every common finite extension for closed coefficients.

The integral model's five record fields now refer to named definitions in the
same owning module: `pointIntegralTensorCompletion`, `PointIntegralTensorFirst`,
`PointIntegralTensorSecond`, `PointIntegralTensorComparison`, and
`PointIntegralTensorUnitModel`. Their formulas are the original field types
verbatim. This factors elaboration without splitting the module, changing any
condition, introducing a theorem, or choosing any new map. All five helpers
are listed in the model node's `lean.declarations`.

## Resumed packet self-check

Retained the saved seven-module repair and reread its actual types against the
returned H3/H8/H11 diagnostic. The comparison data now contain the associator
and both unitor diagrams inherited from `Functor.Monoidal`, an explicit braiding
square, and a coefficient-unit isomorphism. The canonical predicate requires the
finite K-flat, integral Roos, rational localization, and every-common-stage
normalizations. The finite reduction square uses two coefficient levels and the
recorded quotient tensor comparison; the rational and closed squares retain the
recorded scalar and stage transports. These conditions are conclusions of the
theorem. They are absent from the rejected bare-isomorphism formulation.

Checked the six helper nodes against their owning modules and the item against
the current shared node. All seven primary signatures are verbatim, all seven
modules disable auto-implicit variables and satisfy the line limit, and the JSON
layout is unchanged. The item's only field changes are `lean` and the added
helper statement dependencies. The original mathematical statement is retained.
This is a self-check, not a claim of an independent second reviewer.

The required initial dry run compiled the six helper modules cleanly and found
two unavailable `DerivedCategory.fieldScalarExtension` references in the final
module's counit equations. Reading `FieldComplexScalarExtension` shows that
`fieldDerivedScalarExtension` is exactly
`(ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory`. Both counit equations
now use that actual ordinary functor's `mapDerivedCategoryFactors.hom`; their
canonical maps and mathematical conditions are unchanged.

After this repair, `scompile.py Q62 lem-sf-point-fibre-derived-tensor` compiled
all seven delivered modules cleanly, separately in dependency order. The final
module passed both sandbox and library checks (14.2 s and 12.5 s), within the
unchanged 60-second per-file limit.

The next dry run passed compilation and reported six missing LeanSearch records,
one for each new definition node. Ran `msearch.py leansearch` with the query
"geometric point fibre functor preserves derived tensor with strong symmetric
monoidal coherence and canonical K-flat Roos completion reduction scalar extension
comparisons". Its eight results were underived point-fibre functors, presheaf
tensor, and flat scalar-extension limit preservation. None supplies these derived
four-stage predicates. The exact logged result is now in every new node's
`mathlib_searches`, alongside the retained LeanFinder, Loogle and grep records.

The retained integral model was factored through the named declaration
`pointIntegralCanonicalComparison`, which is exactly the composition of the
localized completion map, exact-sections inverse, and recorded completed-tensor
comparison. `PointIntegralTensorComparison` still equates the inverse tensorator
with this canonical composite; the factoring only avoids repeated elaboration.

## Continuation self-check on 2026-10-18

Retained the seven modules and six helper nodes described in the maintenance
handoff. Against the current shared node, the item's only changed fields are
`lean` and the six added helper `stmt_deps`; none of the seven modules or six
helper nodes is already present in the shared checkout. The cited immutable
validation log is no longer available at its stated local path, so this check
does not claim a fresh byte comparison with that commit. The normal delivery
wrapper performs compilation and server preflight on the retained source.

Read every retained module against the return: genuine monoidal constraints,
the coefficient units, K-flat and two-coordinate Roos normalizations, finite
cross-level reduction, rational scalar squares, and every common finite stage
remain explicit conclusion data. Preserved the integral comparison refactor.
Added its missing source and owning blueprint citation to the docstring of
`pointIntegralCanonicalComparison`; its definition and all signatures are unchanged.
