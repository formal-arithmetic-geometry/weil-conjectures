## Worker report

The module `Sheaf.Paper.LocalizedTopChern` states
`WeilConjectures.PurityFiniteSetting.localized_top_chern`. It asserts existence
of one family of supported morphisms, with the four properties of the node.
The family is quantified simultaneously over schemes, bundles and sections so
base change and direct sums compare the same family. No definition extracts
an object from this mere existence theorem. All definitions have explicit data.
Named proof obligations give the integer degree and Tate-presentation equalities
and the unique realizations of the explicit canonical comparisons in the
published Hom coordinates. Each has its natural-language proof in its docstring.

Hypothesis and clause correspondence:

* The chapter's fixed finite coefficient setting is `P : PurityFiniteSetting.{u}`:
  the fixed algebraic closure of the finite field, ell different from its
  characteristic, the finite coefficient extension and positive quotient level.
  No ramification divisibility hypothesis is imposed.
* A separated finite-type k-scheme is `T : Scheme.{u}` with structure morphism
  `a : T ⟶ Spec (.of P.field.k)` and `IsSeparated a`,
  `LocallyOfFiniteType a`, `QuasiCompact a`. The explicit structure map is
  required by the recorded regular-section and Chern-class interfaces.
* The rank-r vector bundle is `F : T.Modules`, `r : ℕ`,
  `[F.IsFiniteLocallyFreeOfRank r]`. A section is the actual `s : F.sections`;
  regularity is the recorded `IsRegularSection P T a F r s`.
* Its zero scheme and immersion are `regularSectionZeroScheme` and
  `regularSectionZeroProjection`, exactly the recorded fibre product of s
  with the zero section of Spec Sym(F dual). Closedness is concluded, not
  assumed as an extra geometric restriction.
* The displayed arrow is `FunctorialCupH true i (2 * (r : ℤ)) r`. Unfolding
  this is Hom from the underived pro-etale direct image of the coefficient
  unit, placed in degree zero, to the signed Tate sheaf in degree zero,
  shifted by 2r. It is the supported cohomology of the two recorded support
  nodes and does not introduce another cohomology theory.
* (L1) is `LocalizedTopChernLaws.line`. It concludes Cartierness of the zero
  scheme, and equality with `divisorProEtale i (D.homClassOf i hI)` for the
  relative-torsor-normalized `DivisorEtaleClasses` family. The normalization
  is `DivisorEtaleNormalized T a D`, the same one used by `divisor_class`.
  This retains the specified section off the divisor, not merely its
  ordinary Picard or support-forgetting class.
* (L2) is `base_change`. It quantifies over every morphism g between the
  schemes in the chapter and every realization of g*F by a bundle isomorphism.
  The equality on every open U fixes s' to the image of `1 tensor s` under
  that isomorphism, using the existing `tensorPullbackSection`. Regularity
  of s' is precisely the stated condition. The canonical Cartesian square
  of zero schemes is concluded, and `functorialCupPullback true` is the
  actual supported inverse-image map. In particular no flatness, smoothness,
  etaleness or finite-type hypothesis on g itself is introduced. Identity
  and arbitrary isomorphic realizations are retained. For a tautological
  section all base changes satisfy the regularity condition: on an affine
  frame they are polynomial variables over the new coefficient ring,
  including rank zero and a singular base. Thus the universal quantifier
  includes the stated arbitrary-base-change special case.
* (L3) is `direct_sum`. The hypothesis is the recorded
  `IsTransverseDirectSum`, with the two individual regularities named so
  their classes can be evaluated. It concludes the rank and regularity of
  the actual product module with paired section `regularSectionSum`.
  `regularSectionSumZeroComparison` identifies its zero scheme with the
  scheme-theoretic intersection. `functorialCupChangeSupport` carries its
  class to that intersection, and the resulting class is the internal
  `functorialCup true` of the two individual classes. HEq here transports
  only the equal integer degree/twist expressions 2(r+e) and 2r+2e,
  and the canonical support expressions; no arbitrary comparison is chosen.
* (L4) is `forget_support`. Its map is precisely `functorialCupForget true`,
  induced by restriction from the coefficient unit to the closed support.
  The right side `localizedChernOrdinary` is the recorded
  `ordinaryFiniteChernClass a F r r`, composed with explicit canonical
  tensor/shift comparisons. `localizedChernTwistMapEtale` recursively uses
  `cupSingleTensorMap`, `cupTensorShiftIso`, and the normalized
  `functorialCupTwistProduct`, followed by the exact site comparison.
  The class is never redefined via the localized family.
* The construction restriction is documented in the theorem's eleven-step
  natural-language proof: bottom-degree gluing on the universal zero-section
  pair, then supported pullback along s; splitting and the ordinary
  projective-bundle relation identify the support-forgetting value. No
  exceptional purity or descent of derived objects is used.

Dependency declarations read and used:

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Coefficient`, `constantEtale`, `constant`.
* `Sheaf.Paper.PurityRegularSection`: `AlgebraicGeometry.IsRegularSection`,
  `IsTransverseDirectSum`, the zero-scheme/projection constructions,
  `regularSectionSum`, `regularSectionSum_rank`, and the canonical sum-zero
  comparison with its projection equation.
* `Sheaf.Paper.PurityChernClasses`:
  `WeilConjectures.PurityFiniteSetting.ordinaryFiniteChernClass` and
  `ordinaryFiniteCohomology`; these are the signed projective-bundle coefficients.
* `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `AlgebraicGeometry.ProEtale.derivedSupportSections` and
  `supportHypercohomology` fix the kernel-of-restriction support convention.
* `Sheaf.Paper.SupportedCohomologyHom`:
  `AlgebraicGeometry.ProEtale.supported_cohomology_hom` identifies these
  supported groups with the displayed derived Hom.
* `Sheaf.Paper.SupportedCup`: `AlgebraicGeometry.ProEtale.cupSingleTensorMap`,
  `cupTensorShiftIso`, and `supportedCup` supply the published tensor comparisons.
* `Sheaf.Paper.SupportedCupFunctoriality`: `FunctorialCupH`,
  `FunctorialCupOrdinaryH`, `functorialCupPullback`, `functorialCupChangeSupport`,
  `functorialCup`, `functorialCupForget`, the single and twist objects and
  normalized twist products. These existing definitions are owned by the new
  `def-pur-supported-class-operations` node in stmt_deps. The functoriality
  theorem remains in proof_deps.
* `Sheaf.Paper.PurityDivisorClass`: `DivisorEtaleClasses`,
  `DivisorEtaleNormalized`, `divisorProEtale`, and `divisor_class`.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` reexports the recorded
  coefficient-twist conventions, including `diagonalTwistEtale`,
  `diagonalTwist` and `diagonalExponent` used by the finite Chern coordinates.
* `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSection` fixes the ordinary
  pulled-back section. This already-landed definition node is added to
  stmt_deps; its interface is used without another section construction.

Already stated proof dependencies are imported without `public`. The following
proof dependencies have no recorded declaration yet and therefore no import:
`lem-pur-cartier-class-agreement`, `lem-pur-flag-local-comparison`, and
`lem-pur-flag-localized-product`. They are proof prerequisites only; no missing
statement notion or canonical map is replaced by an assumption.

Edge cases checked before drafting and on rereading: r=0 (zero bundle, full
support, empty product, c_0=1); r=1 (actual Cartier divisor and relative section);
empty T; empty zero locus (vacuous regularity and zero supported class); singular
base and singular regular zero scheme; nonsplit vector bundles; base change
which destroys regularity (excluded exactly as in L2); arbitrary base change
of polynomial-variable tautological sections; rank-zero factors and disjoint
supports in L3; arbitrary positive finite coefficient levels and ell=2. No
smoothness of T or Z(s) is assumed. Every universe and variable is explicit.

Searches for an existing statement (2026-10-18):

* msearch.py LeanFinder: "Localized top Chern class of a regular section of a
  vector bundle with supports". Eight hits, including ModuleCat.Tilde and
  structure-sheaf localization statements; none states a Chern class theorem.
* msearch.py Loogle: `"Chern"`. Two Lean matcher-name substring hits; no match.
* msearch.py grep: `localized.*Chern|Chern.*localized`. Zero Mathlib hits.
* msearch.py LeanSearch: "localized top Chern class regular section supported
  cohomology". Eight manifold-section, local-frame and affine-localization
  results; none is the scheme-theoretic supported Chern statement.
* rg over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `localized.*Chern|Chern.*localized|thm-pur-localized-top-chern`: no upstream
  theorem or declaration-name match. Side matches are source references in
  FlagPullbackInjective, SupportedProjectionSplitting, ChernFlagFormula and
  PurityRegularSection, not the requested theorem.
* Searches for tensor-pulled-back sections found the existing
  TensorPullbackSectionAdjunction interface; it is reused. Searches for the
  positive twist presentation found FixedFinitePositiveCoefficientTwist and
  affineLinearBaseCoefficient; those objects are reused, with an explicit
  tensor-shift map rather than a new twist definition.

Node fault noted: the item's repaired natural-language proof predates the
2026-10-18 sign correction to lem-pur-divisor-class. Its coordinate products
are written as positive frame boundaries, while the current normalized Cartier
class is minus that boundary. The theorem statement (L1)--(L4) remains correct.
The proof docstring uses the products of normalized Cartier classes, hence
(-1)^r times the raw ordered frame-boundary product. No statement change is
required, and no node field outside the permitted lean/stmt_deps fields is changed.

## Repair of the independent return

R1: replaced the theorem node `lem-pur-supported-cup-functoriality` in
stmt_deps with `def-pur-supported-class-operations`, an existing:true node
owning the actual definitions in the live `Sheaf.Paper.SupportedCupFunctoriality`.
Its declarations include every interface named by the return and the concrete
coefficient and comparison constructions they use. The theorem remains in
proof_deps. There is no new Lean file for this node and no copy of the definitions.

R2: removed `def-pur-frame-class` from stmt_deps and removed the sandbox's
PurityFrameClass dependency module and node record from the delivery packet.
Its unchanged occurrence in proof_deps belongs to the construction proof.

R3: removed the sandbox's SupportedCupFunctoriality dependency module and changed
`lem-pur-supported-cup-functoriality` record from the delivery packet. The live
NE/Q73 repairs and all live declarations, including
`functorialCupComparisonTwist_eq`, are preserved by using the published module.
The earlier report's descriptions of dependency-module changes have been removed;
this delivery contains no dependency-module rewrite. LocalizedTopChern.lean is
retained byte for byte. Its lean record additionally lists its existing
`localizedChernTensorPowerCharacterization` helper and copies the final theorem
signature verbatim, preserving its newline.

## New nodes

`def-pur-supported-class-operations` records existing definitions in
`Sheaf.Paper.SupportedCupFunctoriality`, with `FunctorialCupH` as its primary
declaration. It defines the two selected sheaf/derived categories, finite units
and signed twists, exact site comparison, supported and ordinary Hom groups,
normalized twist products, internal supported cup, supported pullback, change
of support and forgetting support. Its source is the displayed arrow and
(L2)--(L4) of the current blueprint target, using the already published
coefficient-normalized constructions. The definition asserts no theorem laws.
LeanSearch and LeanFinder returned unrelated generic pullback or group-cohomology
results; Mathlib grep and upstream source grep found no matching interface.
The side-project search found exactly the existing declarations being reused.
The DAG search found only the theorem owner and consumer definition nodes;
`def-pur-supported-cup` defines the general pro-etale tensor product rather than
this two-site signed-twist operation interface. All raw msearch results and the
DAG/source search results are recorded in the new node's mathlib_searches.
No new notion is implemented or alternative canonical map chosen.

## Canonical comparison realizations

The retained target's `localizedChernTwistMapEtaleRawCharacterization` fixes the
actual ordered zero, successor and multiplication maps via
`localizedChernTensorPowerCharacterization`. HEq reconciles only equal Hom
presentations; the result is the specified recursive tensor-shift composite.
`localizedChernOrdinaryCharacterization` fixes the transport of the independently
defined ordinary Chern class through that same comparison. Their unique-realization
theorems determine these objects completely. No class is chosen from the target's
mere existence conclusion and no unconstrained isomorphism replaces a canonical map.

## Self-check

I reread the node and current blueprint and retained exactly the module whose
mathematics the independent return accepted. The finite setting, separated
finite-type schemes, actual finite locally free bundle, section, regularity,
and zero scheme have their recorded meanings. L1 is the relative-torsor Kummer
class; L2 quantifies over every base morphism in the setting for which the
pulled-back section stays regular, including identities and arbitrary isomorphic
realizations; L3 is the internal product on the actual zero-scheme intersection;
L4 uses the independent ordinary Chern class with the fixed tensor comparisons.
Rank zero, empty schemes, empty supports, singular bases and singular regular
zero schemes remain included. No target hypothesis, clause, proof or source
field changed. I checked the new node against the current live definitions:
its pullback is the displayed exact derived composite, change of support is
precomposition by restriction, and forgetting support is precomposition by the
unit restriction. The generalized twist product retains positive annihilators
invertible on the scheme, including all finite levels used here.

No independent second worker was started, as the dispatcher explicitly forbids
starting other agents. The supplied immutable-head independent review accepted
the target's complete statement; this self-check addresses its three requested
packet repairs. The maintainer independently reviews this revised delivery.

## Validation

The required initial saved-packet dry run passed at 5f03ff2a59, but still included
the rejected dependency rewrites, so it was not pushed. Only the target module,
the item node, the new existing:true definition node, and this report are in the
revised packet. Compilation and final dry-run results are recorded below.

The retained LocalizedTopChern.lean passed scompile.py cleanly against live:
sandbox 40.3 s, library module 40.1 s, no errors or warnings. The final packet
self-check confirms the only existing item fields changed are lean and stmt_deps;
all original statement dependencies and all proof dependencies are retained.
Only the approved module and the two intended node records remain under the
delivery directories. Every declaration in the target is listed in lean.declarations.

## Second reading by NM

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
