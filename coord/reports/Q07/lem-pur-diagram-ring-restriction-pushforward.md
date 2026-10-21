## Worker report

The module `Sheaf.CategoryTheory.DiagramRingRestrictionPushforward` states
`CategoryTheory.diagramRingRestrictionPushforward`; its single theorem is left
with `sorry`. The four auxiliary declarations have real data and only name the
componentwise inverse image, direct image, transported adjunction, and composite
forgetful functor needed to express this node. There are no new independent
notions, dependency replacements, or statement corrections.

Source read: `literature/stacks-project/sites-cohomology.tex`, Tag 0D6E,
`lemma-derived-pushforward-composition`, lines 4010–4031, including its proof by
derived adjunction and uniqueness. The node's five proof steps are reproduced
in the theorem docstring. This lemma applies to arbitrary morphisms of ringed
topoi and does not require flat structural maps.

Hypotheses and clauses, matched to the Lean signature:

- Small indexing category and small presenting sites: `J C D : Type u` with the
  three `SmallCategory` instances; `K` and `L` are the base site topologies.
  The diagram sites are exactly `diagramSiteTopology J C K` and
  `diagramSiteTopology J D L`, on `Jᵒᵖ × C` and `Jᵒᵖ × D`.
- The base geometric morphism, its adjunction, and left exact inverse image are
  the corresponding fields of `s : RingedToposMorphism SX SY`. Its structural
  map is precisely the specified `u⁻¹ SY → SX`; the module direct-image field
  is constrained by that existing structure's underlying-sheaf and linearity
  conditions, rather than an arbitrary additive functor.
- The commutative ring sheaves are `SX` and `SY`, with commutativity `hSX` and
  `hSY`. A sheaf of commutative rings is written using its underlying RingCat
  sheaf and pointwise commutativity, as in the realization dependency. The
  variable ring diagrams are `BX` and `BY`, with `hBX` and `hBY`, represented
  directly as ring sheaves on the actual product sites. Their restrictions
  along `(j,U)` give the ring diagrams; sheaves of modules over these rings
  encode precisely the required semilinear horizontal transitions, including
  all arrows of J. No constant-coefficient replacement of B is made.
- The constant ring diagrams are the existing `diagramSiteRing J C K SX` and
  `diagramSiteRing J D L SY`. The natural coefficient maps are `aX` and `aY`,
  morphisms of ring sheaves on the diagram sites, hence of whole ring diagrams.
- The diagram geometric morphisms with their B and constant-S structural maps
  are `fB` and `fS`. `hInvB`, `hInvS`, `hDirB`, and `hDirS` identify their
  underlying functors with the transported componentwise functors of s;
  `hAdjB` and `hAdjS` identify the adjunctions, too. These are presentation
  identifications of the given u^J, not flatness or acyclicity assumptions.
  `hStructuralS` says at every `(j,U)` that the constant-S structural map is
  the component of s's base structural map. Thus it cannot vary with j.
- Compatibility of the two structural maps with a is exactly `hRing`. Its
  `eqToHom` only identifies the two named inverse-image functors and makes
  the commuting square well typed; no equality of coefficient rings is imposed.
- The module categories are the dependency's `ringedSiteModules`, applied to
  B and to the constant S ring sheaves on the product sites. Restriction is
  exactly `SheafOfModules.restrictScalars aX` and `... aY`. The existential
  lifts `rX`, `rY`, with `phiX`, `phiY`, express termwise restriction through
  localization, with no resolution inserted. In particular these are
  canonically identified with the exact-functor derived lifts of the recorded
  Mathlib interface. There is no assumption that scalar restriction preserves
  K-injectivity.
- Ordinary unbounded derived categories are `DerivedCategory.{w}` with the
  four explicit `HasDerivedCategory.{w}` instances. Complexes are indexed by
  all of ℤ, using `ComplexShape.up ℤ`; no boundedness is imposed.
- `RB`, `RS`, and the units `etaB`, `etaS` satisfy the existing
  `IsRightDerivedFunctor` predicates at the quasi-isomorphisms. The two clauses
  asserting `IsIso (etaB.app I)` / `IsIso (etaS.app I)` on K-injectives specify
  the K-injective computations from the node.
- `c` is the unique ordinary scalar-restriction/direct-image comparison whose
  underlying set-sheaf map is the identity under the specified direct-image
  identifications. Its displayed underlying-sheaf equation prevents choosing
  an unrelated ordinary isomorphism.
- `kappa : RB ⋙ rY ≅ rX ⋙ RS` is exactly the requested direction
  `rho_Y R u_{*,B}^J ≅ R u_{*,S}^J rho_X` in Lean's composition convention.
  These are functors between derived categories of sheaves on the full
  diagram sites; no evaluation functor occurs.
- The final equation, for every complex M, is the normalization through the
  common composite. The left side uses `phiY.inv`, followed by the B-derived
  unit under rY, followed by kappa. The right side uses the class of c on
  complexes, then the S-derived unit on rho_X M, then `RS.map phiX.inv`.
  Both start at `Q(rho_Y fB_* M)` and end at `RS(rX(Q M))`. These are exactly
  the two composition units through `Rh_*` after the exact-restriction
  identifications. The composition dependency's unit normalization and
  uniqueness identify their quotient with its two-factorization comparison.
  The `∃!` asserts this characterization, rather than merely existence of a
  natural isomorphism with no normalization.

Dependency declarations read and used:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` and its additive instance (the recorded
  def-pc-sheaf-restrict-scalars). The construction keeps the underlying
  abelian presheaf and sheaf condition, restricting the scalar action.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q` (recorded abstract-derived category).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules` (recorded general module category).
- `Sheaf.CategoryTheory.DiagramSiteRealization`:
  `CategoryTheory.exists_diagramSite_realization`, including the normalization
  of the sheaf equivalence and the constant-coefficient module equivalence.
  Its underlying concrete construction is used via
  `Sheaf.CategoryTheory.DiagramSiteTopology` (`diagramSiteTopology`,
  `diagramSiteRing`) and `Sheaf.CategoryTheory.DiagramSiteSheafEquivalence`
  (`diagramSiteSheafEquivalence`). Its module equivalence applies only to
  constant coefficients; the variable B-module category is the ringed-site
  module category on the actual variable ring sheaf, as the node requires.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, with its full
  derived-unit and K-injective normalization, is imported for the proof plan.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective` (recorded Mathlib match of def-pur-kinjective-complex).
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`, and the
  triangulated instances (recorded exact-functor-derived-factorization match).
- The existing `RingedToposMorphism` interface is read from
  `Sheaf.CategoryTheory.RingedToposMorphism`. `Adjunction.whiskerRight` and
  `Adjunction.comp` are used for the explicit componentwise adjunction.

Edge cases checked mathematically before finalizing the statement: J empty
(all diagram-site categories and equations remain defined, no `Nonempty`
binder); J with one object and identity arrows (ordinary ringed-topos scalar
restriction); J disconnected (the explicit hStructuralS clause still forces
all constant-S structural components to come from s); identity coefficient
maps and identity u; zero rings and zero complexes; nonflat coefficient map
ℤ → ℤ/2 (no flatness binder and no assertion that restriction preserves
K-injectives). The common u is an arbitrary universe large enough for the
small sites and coefficients, while w is explicitly independent for the
chosen derived-category morphism universe.

Searches actually run via msearch.py:

- LeanFinder: `Derived restriction of scalars commutes with pushforward on
  ringed diagram topoi`: eight hits, including ordinary
  `SheafOfModules.pushforwardComp` and `pushforwardCongr`, none asserting the
  unbounded normalized diagram comparison for arbitrary geometric morphisms.
- Loogle: `SheafOfModules.restrictScalars, SheafOfModules.pushforwardComp`:
  zero hits for the combined query.
- Mathlib grep: `restrictScalars.*([Dd]erived|[Pp]ushforward)|[Dd]erived.*restrictScalars`:
  zero hits.
- LeanSearch: `Restriction of scalars on sheaves of rings commutes with
  unbounded derived direct image`: eight hits, including the actual
  `SheafOfModules.restrictScalars` reused here; no comparison theorem.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf`, and grep of the item
  identifier in `lean/WeilConjectures`, found no existing declaration of the
  item. The flat-ringed-diagram restriction family was read: it requires
  flat coefficient changes and constant coefficients in the J-direction,
  unlike the present variable-ring, arbitrary-coefficient statement.
  `Sheaf.derivedRestrictScalars` in the upstream DerivedBaseChange module is
  for constant external rings and provides no general ringed-topos comparison.
  Searches for the four new helper names and the theorem name found no
  duplicate declarations in either source tree or `dag/lean_names_upstream.json`.

No `STATEMENT-DISPUTED` flag or source/node correction is needed.

Validation: the prescribed scompile.py wrapper is being used for every
compile. Initial elaboration errors in helper qualification and the required
abelian-sheafification instance import were repaired in the sandbox. Subsequent
attempts report missing published library paths and server confirmation
`Live published library is unavailable`; compilation and delivery will be
retried through the prescribed tools.

Final tool status: three successive scompile.py retries after the initial
elaboration pass, followed by the required deliver2.py --no-push dry run,
failed before checking the revised module. The wrapper cannot compile the
unchanged `Sheaf.CategoryTheory.DiagramSiteTopology` dependency: `unknown module
prefix 'Mathlib'`, with only the live build directory and Lean toolchain in its
search path. Its independent server confirmation says `Live published library
is unavailable`. The dry run exits 1 and states `COMPILE FAILED on the server,
nothing pushed`. This is a compiler-wrapper/published-library availability
failure, not a missing mathematical declaration. The sandbox module, node
record, and this report are retained; the revised module is not yet verified.
No launcher scripts, live sources, or shared Git state were edited directly.

Retry on 2026-10-21: inspected this saved report and ran the prescribed
`deliver2.py Q07 lem-pur-diagram-ring-restriction-pushforward --no-push`
before changing the packet. It exited 1 while compiling the unchanged overlay
dependency `Sheaf.CategoryTheory.DiagramSiteTopology`, before elaborating the
item. The current diagnostic is a missing published Mathlib object file:
`Mathlib/Algebra/Category/Ring/Basic.olean`. The wrapper's server confirmation
again reports `Live published library is unavailable`. A separate prescribed
`scompile.py` retry on the saved module returned the identical diagnostic and
server confirmation, also with exit 1. This is not a busy-server timeout or a
Lean statement diagnostic. The packet is retained unchanged apart from this
validation record; no delivery was pushed. Restoring published compiler
artifacts requires the library maintainer and cannot be repaired within this
worker's sandbox or by changing this mathematical statement.

Dispatcher retry 3 on 2026-10-21: retained the saved packet and first ran
`deliver2.py Q07 lem-pur-diagram-ring-restriction-pushforward --no-push`.
It again exited 1 before checking this module: the unchanged overlay dependency
`Sheaf.CategoryTheory.DiagramSiteTopology` cannot import
`Mathlib.Algebra.Category.Ring.Basic` because its published `.olean` is missing.
The required `scompile.py` retry of the saved module independently returned the
same failure (exit 1); both server confirmations say
`Live published library is unavailable`. This is not exit 124 or a busy-server
timeout. No mathematical source or node changes were made, and nothing was
pushed. The missing published build artifact cannot be repaired within this
worker's authorized sandbox; the saved packet remains ready for a retry once
the published library is restored.

Dispatcher retry on 2026-10-21 (current session): inspected the retained report
and ran the prescribed deliver2.py --no-push first. It failed with exit 1
while compiling the unchanged DiagramSiteTopology overlay dependency, before
elaborating the delivered module: the published
Mathlib/Algebra/Category/Ring/Basic.olean does not exist. A separate prescribed
scompile.py retry of DiagramRingRestrictionPushforward.lean returned exit 1
with the identical missing-object diagnostic. Both wrappers independently
confirmed against current server sources: `Live published library is unavailable`.
This is not a busy-server exit 124. The mathematical module and node packet
remain unchanged; no push occurred. Repair requires restoring the published
library artifacts, outside this worker's sandbox and authorization.


Dispatcher final retry on 2026-10-21: retained the saved module and report and
started with the required deliver2.py --no-push. The previously missing Mathlib
artifacts were available for this attempt: the item compiled without its own
warnings, both as sandbox (6.8 seconds) and as library module (6.4 seconds).
The wrapper nevertheless refused delivery because the unchanged overlay
Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions emitted a long-line warning
at line 10. Retrying the prescribed dry run after that compilation did not reach
preflight: a newly refreshed dependency closure failed in the unchanged
Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction at line 6, because the
published WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean was
missing. Its server confirmation returned the identical missing-object error.
A separate prescribed scompile.py retry of the saved item also exited 1 with
that same missing artifact, both locally and in SERVER CONFIRMATION. Neither
failure was a busy-server exit 124. The published-library/overlay tooling must
restore or compile that prerequisite; this worker cannot modify the published
library, shared source files, or launcher scripts. Nothing was pushed.

The self-check reread the current item, its six statement dependencies and their
interfaces, the diagram-site helpers, and Stacks 0D6E. The full current theorem
signature still matches lean.statement verbatim; every helper is listed in
lean.declarations, the only sorry is the named item theorem, and every Lean
line is within 100 columns. No mathematical changes were needed. Refreshed the
sandbox node's non-Lean fields from the current read-only DAG (only the routine
lean_audit had changed since the saved packet), retaining the existing lean
record. The actual delivery therefore changes only lean. The maintainer's
independent review remains the review required by the direct-delivery brief.

Dispatcher retry on 2026-10-21 (missing derivability artifact): inspected the
saved report and first ran the required deliver2.py --no-push. It exited 1
before elaborating this item because the published object file
WeilConjectures/FromJoel/Algebra/Homology/DerivedCategory/DerivabilityStructureKInjectives.olean
is missing. The wrapper's independent SERVER CONFIRMATION returned the same
missing-object diagnostic. A separate prescribed scompile.py retry of the
saved module also exited 1 with that identical missing artifact in both its
local check and SERVER CONFIRMATION (0.4 seconds each). This is not a busy
server or exit 124. The saved Lean and node remain unchanged, and nothing was
pushed. Restoring this published prerequisite is outside the worker's sandbox;
no live sources, build artifacts, or launcher scripts were modified.

Current dispatcher retry on 2026-10-21: the required initial dry run succeeded:
`OK (dry run): commit 2e41787e14a passes the preflight and compiles; nothing pushed`.
Both sandbox and library compilation completed through deliver2.py. The earlier
published-artifact failures are resolved for this run. Retained the saved Lean
statement and node unchanged. The self-check reread the current item and all six
statement dependencies, their recorded signatures and docstrings, the concrete
diagram-site equivalence and ringed-topos interface, and Stacks 0D6E. Verified
that lean.statement is the signature verbatim, the sole sorry is the named item
theorem, all Lean lines meet the 100-column limit, the record uses the current
UTC date, and the node differs from the current DAG only in lean. The previously
reported edge cases and hypothesis/clause mapping still apply. No repair note
exists for this item. The maintainer's independent delivery review remains the
required independent review; this check is the worker's self-check.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
