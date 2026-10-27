## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.SpaceStrictLocalCohomologyComparison`, namespace
`AlgebraicGeometry.AlgebraicSpace.StrictLocalCoherent`. Stage 2 only: all four theorem
proofs are `sorry` (`ordinary_existsUnique`, `stalk_additive`, `derived_comparison`,
`comparison`). All definitions have real data; the ordinary map is selected only from
its unique, complete pointed-chart normalization.

Sources opened: `literature/stacks-project/spaces-cohomology.tex`, the proof of
lemma-formal-functions-stalk (08B1), especially its strict-local reduction and the paragraph
identifying stalk, sections and cohomology; flat base change (073K); the existing affine-base
comparison (08EX). The item is a supporting node, not its blueprint unit's statement.
The source's properness is used for formal functions after the reduction. This node uses
only the separated finite-type assumptions, as its accepted split explicitly specifies.

Hypothesis and clause correspondence:

- Schemes and morphisms: `{S : Scheme.{u}}`, `Y : Over S`, `X : AlgebraicSpace S`,
  `f : X ⟶ schemeSpace Y`. The auxiliary ambient base S is arbitrary and imposes no
  absolute finiteness or separatedness; Y can itself be used as the ambient base.
- Y locally Noetherian: `[IsLocallyNoetherian Y.left]` in both comparison theorems.
- f separated and finite type: `hsep : MapIsSeparated f`, `hft : MapIsFiniteType f`.
  The existing predicates mean closed-immersion diagonal and quasi-compact plus chartwise
  locally finite type. No properness, flatness of f, finite presentation or affineness is added.
- Coherent F: the full subcategory with predicate
  `fun M : X.Modules ↦ M.IsQuasicoherent ∧ M.IsFiniteType`; the derived statement has
  those same two hypotheses on M. On X all étale charts are locally Noetherian since f
  is locally finite type over Y. On such charts quasi-coherent finite type means associated
  to finite modules on affine covers. This is precisely the node's explicit meaning of
  coherent, including zero generators; it does not assume coherence of all module sheaves.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`,
  `t : Spec (.of Ω) ⟶ Y.left`. `point` is its Yoneda map over S.
- A is the geometric structure stalk: `Scheme.strictHenselizationRing t`, the existing
  small affine pointed-neighbourhood ring colimit. `ringIso` is the existing uniquely
  germ-preserving scheme/space comparison, applied to the identity chart of Y.
  `stalk` restricts scalars by that ring iso, so its output is an A-module, not a module
  over an unrelated isomorphic ring.
- c is the canonical map: `Scheme.strictHenselizationStructuralMap t` is defined by
  the compatible affine-neighbourhood colimit maps. `base` and `baseMap` only bundle
  this existing map over S and apply Yoneda; they do not choose another morphism.
- X_A is `space`, the actual sheaf fibre product `enlargedFibreProduct f (baseMap Y t)`.
  `projection` is h and `structureMap` is f_A, the actual first and second projections.
- F_A is `moduleTensorPullback (projection Y t f)`; in the equivalent small model this
  is the existing `smallModuleTensorPullback`. This is tensor pullback, not a different
  restriction or an arbitrary left adjoint supplied by the caller.
- All sheaves are structure-module sheaves on the small étale sites. The existing
  `smallModuleRestriction`/`smallModuleEquivalence` transports to a small affine basis
  without changing coefficients, the site topos, or the module section universe.
- R^q f_* is `(smallModuleDirectImage f).rightDerived q`, derived in ALL small-model
  module sheaves, then followed by the geometric module stalk. The coherent subcategory
  is imposed only on the input, after fixing the ambient derived functor.
- H^q(X_A,F_A) is `(sections Y t f).rightDerived q` applied to the tensor pullback.
  `sections` is the existing `affineScalarSections` for the actual f_A and A. It is
  Hom(O,-) with its structural A-action. Grothendieck module-sheaf instances give
  injective resolutions; their existence is not a geometric hypothesis on f or F.
- A Noetherian and local: the first two conjuncts of `comparison` are exactly
  `IsNoetherianRing (Scheme.strictHenselizationRing t)` and `IsLocalRing ...`.
- c flat: the third conjunct is `Flat (Scheme.strictHenselizationStructuralMap t)`.
- X_A locally Noetherian: the fourth conjunct quantifies over every small étale chart W
  and asserts `IsLocallyNoetherian ((space Y t f).etaleForget.obj W)`.
- F_A coherent: the fifth conjunct preserves BOTH quasi-coherence and finite type for
  every coherent M, using the recorded tensor pullback.
- Every q >= 0: `q : ℕ`, including zero. `source` and `target` are functors from the
  full category of coherent modules to `ModuleCat.{u} A`; `∃ e : ∀ q, source ... q ≅
  target ... q` is a natural A-linear isomorphism, including its naturality on every
  module morphism. It is stronger than unrelated objectwise choices only in syntax:
  naturality is explicitly required by the node itself.
- Canonical map and pointed-neighbourhood formula: `neighbourhoodMap` is Spec of the
  germ ring map, followed by the affine scheme's canonical isoSpec inverse.
  `OrdinaryFormula` quantifies over every pointed affine V, every chart of X over V,
  and every chart of X_A over that chart. The triangle forces the composite to V to be
  the canonical map through Spec A. The formula equates projection of the pulled-back
  global section with the local tensor section with coefficient 1, using the actual
  direct-image projections and tensor-adjunction unit. Unit isomorphisms explicitly
  transport between full and small sites; no section is silently identified.
- `ordinary_existsUnique` supplies exactly that normalized natural map.
  `ResolutionFormula` then fixes the induced cohomology map on EVERY injective
  resolution I, resolution J of F_A, and augmentation-compatible comparison a. Its
  first equation fixes the map on cycles by ordinary pullback followed by a; its
  second fixes the resulting cohomology class. Comparison maps exist since c and h
  are flat, so pullback preserves the exact resolution before extending to J.
  These identities express the usual cohomological pullback from each pointed
  neighbourhood; arbitrary neighbourhoods reduce to affine ones around the marked point.
- Derived form required by the current stage convention: `derived_comparison` asserts
  `IsIso` of the image of `resolutionMap` in the derived category, after extension by
  zero from natural to integer degrees. Thus it specifies an actual invertible arrow,
  rather than merely a `Nonempty` isomorphism. The only localization-size binder is
  `[HasDerivedCategory.{w} (ModuleCat.{u} A)]`; w is explicit and arbitrary.
  Taking homology and using exactness of stalks gives `comparison`; the same cycle
  equations retain its normalization. No derived-universe restriction is imposed on
  either site or coefficients.

Dependency declarations used (recorded declarations, with their full signatures/docstrings
opened in the read-only library):

- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Spec`, `Spec.map`, morphisms of schemes.
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian` and finite-type permanence.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`; every ideal is finitely generated.
- Mathlib.RingTheory.Finiteness.Defs: `Module.Finite`, the affine meaning of finite type.
- Mathlib.FieldTheory.IsAlgClosed.Basic and Mathlib.AlgebraicGeometry.ResidueField:
  `IsAlgClosed`, `Scheme.SpecToEquivOfField`, for the given geometric point.
- Mathlib.CategoryTheory.Preadditive.Injective.Basic/Resolution and
  Mathlib.CategoryTheory.Abelian.RightDerived: `Injective`, `InjectiveResolution`,
  `Functor.rightDerived`, `InjectiveResolution.isoRightDerivedObj`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `EtaleSite`, `Modules`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: `QCoh` and the same Mathlib
  `SheafOfModules.IsQuasicoherent` predicate on these module sheaves.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: `moduleDirectImageModel`,
  `moduleDirectImage`, `moduleTensorPullback`, `moduleTensorSection`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  `fibreProduct_isAlgebraicSpace`, used by the existing bundled sheaf fibre product.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality and
  AlgebraicSpaceMorphismProperties: the recorded chartwise property definitions
  `MapIsSeparated`, `MapIsFiniteType`, and their locality interface.
- Sheaf.AlgebraicGeometry.PointedEtaleStalk: `pointedEtaleStalk`, the opposite
  pointed-neighbourhood colimit. The module-valued enhancement uses the already
  recorded `SingleComplex.StalkModel`, not a second private stalk construction.
- WeilConjectures.AlgebraicGeometry.StrictHenselization:
  `Scheme.strictHenselizationRing`, `strictHenselizationScheme`.
- WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap:
  `Scheme.strictHenselizationStructuralMap`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels:
  `SingleComplex.Neighbourhood`, `neighbourhoodChart`, `stalkModel`, `stalk`,
  their ring colimit and module germs, all normalized on actual sections.
- Sheaf.AlgebraicGeometry.SpaceStrictLocalFlatness:
  `strictLocalChartComparison`, with the unique germ-normalized ring equivalence.
- Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections: `affineScalarSections`.
- Sheaf.AlgebraicGeometry.SpaceAffineSectionsCompositors: `fullModuleSection`.
- Sheaf.AlgebraicGeometry.SpaceAffineHomComparison: `affineIdentityChart`.
- Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback: `smallModuleTensorPullback`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules: `smallModuleDirectImage`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: `SmallModules`,
  `smallModuleRestriction`, `smallModuleEquivalence`.

Added stmt_deps are only existing landed interface owners for the constructions above.
No new node, dependency-node repair, statement correction or disputed statement.
The record's main declaration is the derived form; its declarations list also records
`comparison` and every helper belonging to this node's canonical map.

Edge cases checked before and after writing: q=0 is included and gives the ordinary
map via resolution comparison; zero F and empty X give zero stalk and cohomology;
empty Y admits no geometric t and the assertion is correspondingly vacuous; an empty
ring cannot occur as A because it has the given geometric pointing. There is no
assumption on characteristic, perfectness, connectedness, completeness, properness
or nonemptiness of X. Ω and schemes use the same original section universe u;
localization universe w remains independent. Identity c and nonproper separated
finite-type f (e.g. an open immersion) are included.

Searches for an existing statement:

- msearch.py leanfinder: "Geometric stalk of coherent higher direct image on an
  algebraic space is cohomology over strict henselization"; eight hits, ordinary
  scheme stalk maps and strict-local scheme results, no matching space theorem.
- msearch.py leansearch: "Geometric stalk strict henselization coherent higher direct
  images algebraic spaces"; eight hits, scheme stalks and morphism constructors,
  no matching algebraic-space comparison.
- msearch.py loogle: `"higherDirectImage", "stalk"`; zero hits.
- msearch.py grep: `strict.*local.*cohom|cohom.*strict.*local|AlgebraicSpace`; zero hits.
- rg of WeilConjectures and Sheaf for the item id, strictLocalCohomology and
  moduleCohomology/higher image names: the strict-local cohomology files concern
  constant-coefficient abelian sheaves on schemes, and do not give this ringed-module
  algebraic-space statement. Found and reused the existing scalar-sections,
  geometric-stalk, base higher-image sections and small-module interfaces instead.

Validation: prescribed scompile.py compiled the sandbox and its library module cleanly.
On later calls its local compiler reported ENOSPC; the wrapper's normal fallback
confirmed current server-source compilation in 10.0 seconds without diagnostics.
Only prescribed wrappers were used; no repository writes or direct git commands.

## Second reading by Q113

Reopened the node and the complete module after compilation. This is the worker's
second reading; the maintainer's independent review remains the review of this delivery.
Checked the two f hypotheses, locally Noetherian Y, geometric point, exact A and c,
actual cartesian projections, tensor pullback, all-module injective derivation,
Noetherian/local/flat conclusions, all-chart local Noetherianity, both coherence
clauses, every nonnegative degree, naturality and A-linearity, and both normalization
formulas against the node. Corrected explicit full/small module transports on both
sides of OrdinaryFormula; fixed the structure-module input by specifying its actual
ring element 1. Added the derived-category form with an explicit independent w,
while retaining all per-degree and geometric clauses. No mathematical statement
changed. The canonical map is not an arbitrary existential isomorphism: ordinary
sections are uniquely normalized and all resolution classes are prescribed.

## Retained-packet validation, 2026-10-24

Reopened the retained complete module, node and report against the current read clone.
The packet changes only `lean` and adds existing landed interface owners to `stmt_deps`;
no repair note exists for the item. The main recorded signature matches the module,
which disables auto-implicit binding. Retained the geometric and per-degree clauses,
canonical section normalization, and derived comparison unchanged.
The required initial `deliver2.py --no-push` and a direct prescribed `scompile.py`
retry both failed in the library-module compile with
`resource exhausted (error code: 28, no space left on device)`.
The sandbox phase printed no Lean diagnostics. No delivery was pushed.

## Dispatcher retry validation, 2026-10-24

Read the retained report and ran the required initial `deliver2.py --no-push`.
It again failed in the library-module compile with
`resource exhausted (error code: 28, no space left on device)` after 16.0 seconds;
the sandbox phase completed in 11.7 seconds without Lean diagnostics.
Retried the unchanged module directly through the prescribed `scompile.py`.
That retry returned the same library-module ENOSPC failure with the same timings.
The module already uses the required `module` header and explicit variables
(`set_option autoImplicit false`). No source repair is indicated by these diagnostics.
Retained all packet files, made no launcher-script or live-repository changes,
and did not push an unvalidated delivery.

## Dispatcher retry 4, 2026-10-24

Read the saved report and ran the prescribed initial `deliver2.py --no-push`.
The sandbox phase reported no Lean diagnostics (11.7 s); library-module
compilation failed with `resource exhausted (error code: 28, no space left on device)`
(16.0 s). Retried the retained module directly through prescribed `scompile.py`;
it returned the same ENOSPC failure and timings. Reopened the complete module
and compared the node against the current read clone: only `lean` and the allowed
landed-interface additions to `stmt_deps` differ; no repair note is present.
No source diagnostic calls for a Lean change. Retained the packet unchanged
apart from this report entry, did not modify any launcher script or live source,
and did not push an unvalidated delivery.

## Dispatcher retry 5, 2026-10-24

Inspected the saved report and ran the required initial `deliver2.py --no-push`.
The sandbox phase again reported no Lean diagnostics (11.7 s), while the
library-module phase failed with `resource exhausted (error code: 28, no space
left on device)` (16.0 s). A direct prescribed `scompile.py` retry returned the
same failure. Reopened the retained module and node; the module already has the
required module-mode header, explicit universes and `autoImplicit false`.
The failure provides no Lean source diagnostic to repair. Retained the packet,
changed no launcher scripts or live files, and did not push an unvalidated delivery.

## Dispatcher retry after attempt 5, 2026-10-24

Inspected the saved report and ran the required initial `deliver2.py --no-push`.
The sandbox phase reported no Lean diagnostics (11.7 s); library-module compilation
failed with `resource exhausted (error code: 28, no space left on device)` (16.0 s).
A direct prescribed `scompile.py` retry returned the same failure and timings.
Checked the current node against the retained packet: only `lean` and `stmt_deps`
differ, and there is no item repair note. Reopened the module header, explicit
universes and disabled auto-implicit setting. The diagnostic supplies no Lean
source repair. Retained the packet and did not push an unvalidated delivery;
no launcher scripts or live repository files were modified.

## Retained-packet retry, 2026-10-24

Inspected the saved report and ran the required initial `deliver2.py --no-push`.
The sandbox phase reported no Lean diagnostics (11.7 s); library-module compilation
failed with `resource exhausted (error code: 28, no space left on device)` (16.0 s).
A direct prescribed `scompile.py` retry returned the same failure and timings.
Reopened the complete module and current node; only `lean` and the permitted
`stmt_deps` additions differ, and no item repair note is present. The failure
provides no Lean source diagnostic to repair. Retained the packet, changed no
launcher scripts or live files, and did not push an unvalidated delivery.

## Saved-packet dispatcher validation, 2026-10-24

Inspected the retained report and ran the required initial `deliver2.py --no-push`.
The sandbox phase reported no Lean diagnostics (11.7 s); the library-module phase
failed with `resource exhausted (error code: 28, no space left on device)` (16.0 s).
Retried the retained module directly with the prescribed `scompile.py`; it returned
the same ENOSPC diagnostic and timings. Compared the packet node with the current
read clone: only `lean` and `stmt_deps` differ; no item repair note is present.
The retained module has an explicit module header, universes and `autoImplicit false`.
This is a compilation-tool storage failure, with no Lean diagnostic to repair.
Retained the packet; changed no launcher scripts or live files and pushed nothing.

## Current dispatcher retry, 2026-10-24

Inspected the retained report and ran the required initial `deliver2.py --no-push`.
It failed in library-module compilation with `resource exhausted (error code: 28,
no space left on device)` (16.0 s); the sandbox phase reported no Lean diagnostics
(11.7 s). A direct prescribed `scompile.py` retry returned the same failure.
Checked the module header and current node: module mode and explicit variables
are retained, only `lean` and `stmt_deps` differ from the read clone, and no item
repair note is present. The diagnostic is a compilation-tool storage failure,
not a Lean source error. Retained the packet and pushed nothing; no launcher
scripts or live repository files were changed.

## Dispatcher recheck, 2026-10-24

Read the retained report and ran the prescribed initial `deliver2.py --no-push`.
It again failed during library-module compilation with `resource exhausted
(error code: 28, no space left on device)` (16.0 s); the sandbox phase printed
no Lean diagnostics (11.7 s). A direct prescribed `scompile.py` retry returned
the same storage failure. Checked the retained module header and current node:
explicit universes and `autoImplicit false` remain, only `lean` and `stmt_deps`
differ from the current node, and no repair note is present. No Lean source
repair is indicated. Retained the packet and pushed nothing; no launcher
scripts or live repository files were changed.

## Latest saved-packet retry, 2026-10-24

Inspected the retained report and complete module, then ran the required initial
`deliver2.py Q113 lem-sfb-space-strict-local-cohomology-comparison --no-push`.
It failed during library-module compilation with `resource exhausted (error code:
28, no space left on device)` (16.0 s); sandbox compilation printed no Lean
diagnostics (11.7 s). A direct prescribed `scompile.py` retry returned the same
storage failure. Compared the retained node to the current read clone: only
`lean` and `stmt_deps` differ, the main recorded signature is verbatim in the
module, and no repair note exists. No Lean source repair is indicated by this
diagnostic. Retained the packet and pushed nothing; no live source or launcher
script was changed.

## Repair of returned head d09261dd9c64 (H2)

The maintainer accepted the mathematics and requested only five missing definition
owners in stmt_deps. Added each existing node without editing any Lean source:

- `def-trf-scheme-algebraic-space`: `schemeSpace`.
- `def-sfb-space-sheaf-fibre-product`: `enlargedFibreProduct` and
  `enlargedFibreProductFst`.
- `def-sfb-space-small-ringed-model`: `SmallModules`, `smallModuleRestriction`,
  `smallModuleEquivalence`, and `AffineEtaleCharts`.
- `def-sfb-space-derived-module-calculus`: `smallModuleDirectImage` and `chartToScheme`.
- `def-sfb-space-morphism-properties`: `MapIsSeparated` and `MapIsFiniteType`.

Read their existing node records and checked the retained packet against the current
read clone. All previous dependencies are retained. The item changes only lean and
stmt_deps relative to that clone; this repair adds only the five requested dependency
ids and this report entry to the retained delivery. No definition node or dependency
module is created. The Lean record, statements, definitions, proofs and imports are
unchanged. The maintainer explicitly accepted ringIso's unique-choice construction
from strictLocalChartComparison; it requires no repair. The mathematical and edge
case correspondence recorded above remains unchanged.

Unchanged Lean SHA-256: `8b70c6ff8863abca4b2a5ce245346c51fb231ae507b627a2c9d220621518450e`.

Validation will use only the prescribed single-file scompile.py and deliver2.py
wrappers; the dry run rebases the packet onto current server main before preflight.
