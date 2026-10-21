## Worker report

The delivery states `AlgebraicGeometry.ProEtale.finite_classical_localizing` in
`Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing`. Its only proof is `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The item gains the already landed statement dependency `def-sfb-integral-model-generator-data`
solely to reuse its recorded canonical finite-coefficient realization helper.
The source read is the current main-20261015 blueprint,
`sec-six-functors-basics/sk-prop-ctf-finite-proper/`
`sk-prop-ctf-finite-proper-localizing.proof.md`, Transfer, together with the item's
six expanded proof steps. The module docstring gives all six steps and their dependencies.

Hypotheses and objects, matched against the node:

- The prime is `(ell : ℕ) [Fact ell.Prime]`.
- The finite commutative ring is `(A : Type) [CommRing A] [Finite A]`. Its discrete
  topology is `[TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]`.
  These topological structures express the uniquely specified discrete topology, not
  an additional mathematical hypothesis. Finite rings are represented in Type 0,
  as in the recorded admissible-coefficient interface; every finite ring admits such
  a representative. `ULift.{u, 0} A` changes only its universe, not its scalar ring.
- The positive-power annihilation condition is
  `_hA : ∃ n : ℕ, 1 ≤ n ∧ (ell ^ n : A) = 0`. The exponent is not restricted to one.
- `T : Scheme.{u}` is arbitrary for the closure, coproduct and pullback clauses.
  There is no invertibility assumption on ell and no characteristic restriction on T.
- The ordinary constant-ring derived category is
  `Scheme.proEtaleDerivedCategory T (ULift.{u, 0} A)`, whose underlying abelian
  category is `Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T ...)`.
  This is localization of unbounded complexes at quasi-isomorphisms, with its existing
  `HasDerivedCategory.standard` structure. It is not a completion or a bounded category.
- The full classical class is the existing `IsClassicalModuleComplex` from the recorded
  `Sheaf.SixFunctors.ClassicalDefinition`. This asks that every integer cohomology
  sheaf be classical on its underlying set sheaf. `det-pe-classical-sheaves-modules`
  identifies this condition with membership in the essential image of the specified
  module comparison inverse image; scalar actions descend by that exact fully faithful
  comparison. No alternative classicality predicate is introduced.

Conclusions, matched clause by clause:

- `HasCoproducts.{u + 1}` asserts existence of all small ambient coproducts in the
  fixed site/module universe, including the empty one.
- `IsLocalizingSubcategoryOfSize.{u + 1} (fun K ↦ IsClassicalModuleComplex K)`
  unfolds to triangulated closure, closure under all ambient isomorphisms, and closure
  under the ambient coproduct of every small family of classical objects. As an object
  property its full subcategory retains all ambient morphisms. Thus this is exactly
  full replete, triangulated and coproduct-closed, not merely the existence of some
  coproduct internal to a subcategory.
- The next quantified clause preserves classicality under both
  `DerivedCategory.TStructure.t.truncLE a` and `.truncGE a`, for every integer a.
- For every classical family K and every ambient coproduct cofan c with `IsColimit c`,
  the cohomology functor and both canonical truncation functors carry that very cofan
  to colimit cocones. The three `Nonempty (IsColimit (...mapCocone c))` assertions
  express preservation of the specified coprojections, hence invertibility of the
  canonical coproduct comparisons. No arbitrary isomorphism between sum objects is used.
- For every `W : Scheme.{u}` and every `r : W ⟶ T`, the exact canonical constant-ring
  inverse image `Scheme.proEtaleConstantRingDerivedPullback ... r` carries each
  classical K to a classical object. No qcqs, boundedness or finite-type condition is
  imposed on W or r.
- For every truncation degree a, `eLE` and `eGE` are natural isomorphisms between
  truncate-then-pullback and pullback-then-truncate. The two displayed equalities
  identify their composites with the actual `truncLEι` inclusion and `truncGEπ`
  projection. Thus these are the canonical truncation comparisons, not unnormalized
  objectwise identifications.
- Only the final implication binds `[CompactSpace T] [QuasiSeparatedSpace T]`.
  Its premise is exactly the existing `localizingClosureOfSize.{u + 1}` of
  `constantModelBoundedConstructible ... T ⊓ fun L ↦ DerivedCategory.finiteTorAmplitude _ L`.
  This is the recorded Dctf generator class; no Tor condition is silently dropped.
  Its conclusion applies the existing canonical `integralModelIntrinsicRealization T A`
  to each cohomology internal module and tests `IsClassicalModuleSheaf` in exactly
  the intrinsic constant-ring category used by the earlier clauses.

The final clause uses the recorded internal-module presentation of Dctf, rather than
silently replacing that generator class by a different constructibility predicate.
Here the ring object is `condensedRingObj (Profinite.continuousMapRingObj A) T`.
For the finite discrete A of this theorem, `finiteDiscreteCondensedRing_constant`
and `finiteDiscreteSchemeRing_constant` canonically identify it, as a ring object,
with the ordinary sheafified constant A ring. The final clause applies the existing real functor
`WeilConjectures.SixFunctors.integralModelIntrinsicRealization T A` to every
cohomology sheaf. Its three specified factors are
`CondensedRing.continuousRingModuleEquivalence` (reconstruct the sectionwise module
and its action), `integralModelFixedScalars` (restrict to constant scalar functions),
and `finiteCoefficientIntrinsicRealization T (ULift.{u, 0} A)` (associated module
sheaf along the constant-section unit). This lands in the exact ordinary
constant-ring module category of the earlier clauses. For finite discrete A the
coefficient identification is an equivalence, exact and coproduct preserving.
Thus testing `IsClassicalModuleSheaf` on every realized cohomology module expresses
precisely the same classical-cohomology class after the canonical coefficient
transport. The construction is given in the existing Lean source, not left to a
prose choice of map. The final predicate is not classicality of the entire unbounded
derived essential image. No unspecified transport or arbitrary equivalence is a
parameter of the theorem.

Dependency interfaces used (their full source signatures and documentation were read):

- `def-weil-pbc-derived-categories`: `WeilConjectures.AlgebraicGeometry.DerivedCategories`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, with ordinary `DerivedCategory`
  and `DerivedCategory.homologyFunctor`.
- `def-weil-pbc-proetale-modules`: `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`,
  `AlgebraicGeometry.ProEtale.FiniteCoefficientModules` and
  `FiniteCoefficientDerivedCategory`, and its canonical realization interface.
  The intrinsic constant-ring presentation is supplied by the operations interface.
- `sk-def-pe-classical-definition`: `Sheaf.SixFunctors.ClassicalDefinition`,
  `AlgebraicGeometry.ProEtale.IsClassicalModuleComplex` and `IsClassicalModuleSheaf`;
  their public dependency `ClassicalContinuityMap` supplies `IsClassical`.
- `det-pe-classical-sheaves-modules`:
  `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`,
  `AlgebraicGeometry.ProEtale.proEtaleClassicalSheavesModules`, whose final clause
  identifies underlying-set classicality with the essential image on module sheaves.
- `def-weil-pbc-proetale-operations`:
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `AlgebraicGeometry.Scheme.proEtaleConstantRingDerivedPullback`, induced termwise
  by the canonical exact module pullback and the constant-section ring comparison.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `AlgebraicGeometry.ProEtale.constantModelBoundedConstructible` and the generator
  class underlying `ConstantModelConstructibleFiniteTor`.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`,
  `CategoryTheory.IsLocalizingSubcategoryOfSize` and `localizingClosureOfSize`.
- The added landed existing:true definition node `def-sfb-integral-model-generator-data`:
  `Sheaf.SixFunctors.IntegralModelsGenerators`,
  `WeilConjectures.SixFunctors.integralModelIntrinsicRealization`, using the real
  three-factor definition just described. The helper is generic in arbitrary schemes
  and finite discrete rings and has no hypotheses about integral generators, standing
  fields, or locally closed immersions. Its owning node has no dependency path to this
  item (the stmt_deps/proof_deps reach was checked before adding the edge). Only the
  helper is used; the integral-generation theorem is not invoked. The owning definition
  node explicitly lists this helper in `lean.declarations`.
- `def-kun-truncations`: `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`,
  which publicly reuses the standard t-structure's canonical truncations and maps.
  Its telescope definition is not substituted for truncation.

Every stated proof-dependency module is also imported without `public`, including
`ClassicalModuleWeakSerre`, `CohomologyInWeakSerreSubcategory`,
`GrothendieckDerivedCoproductsColimit`, the two finite-discrete ring comparisons,
module-sheaf colimit and Grothendieck interfaces, and the constructible and direct-image
comparison modules. The `sorry` does not implement a second proof route.

Edge cases checked before and during writing: the zero ring satisfies the ring and
annihilation binders and is not excluded by a Nontrivial instance; the empty scheme is
allowed; arbitrary and negative truncation degrees are allowed; all complexes are
unbounded; the index type may be empty or infinite; the localizing intersection is
in the same u+1 indexing universe as the ambient sums; the identity and arbitrary scheme
morphisms are included. The ell-primary condition is allowed to be redundant for the
closure facts, but is retained verbatim from the item.

Searches actually run for an existing exact theorem:

- `msearch.py leanfinder`: “The full subcategory of unbounded derived proetale sheaves
  with classical cohomology is closed under coproducts triangles truncations and
  pullback”. Eight hits, including `LightCondensed.instIsGrothendieckAbelianLightCondMod`,
  `Sheaf.isGrothendieckAbelian_of_essentiallySmall`, `DerivedCategory.IsLE`, `.IsGE`,
  `.TStructure.t` and etale topologies. None states the closure and comparison theorem.
- `msearch.py leansearch`: “Complexes whose cohomology is in the essential image of
  etale inverse image form a localizing triangulated subcategory”. Eight generic
  derived-localization/triangulated hits; no exact pro-etale statement.
- `msearch.py loogle`: `"essImage"`. Twelve essential-image infrastructure hits,
  including `Functor.essImage`, its isomorphism-closure instance and `.getIso`;
  no classical-cohomology closure theorem.
- `msearch.py grep`: `pro[Ee]tale|[Cc]lassicalSheaf`, restricted to
  `Mathlib/CategoryTheory/Sites`; zero hits.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `classical.*localizing`, and `classical.*coproduct` found the sibling
  `FiniteProperClassicalCoproducts` theorem about direct image, not this theorem.
  Further searches for `IsClassical`, `finiteCoefficientIntrinsicRealization`,
  finite coefficient transports, and localizing closures located the interfaces
  reused above. `finite_classical_localizing` has no existing declaration in
  Mathlib, WeilConjectures or Sheaf.

No disputed statement or node fault was found. All universes and variables are explicitly
bound, and there are no file-local definitions, notation, instances, or hidden proof holes.

## Second reading by Q14

I reread the node alongside the final signature, independently of the drafting order.
The dispatcher explicitly prohibits starting another worker; this is a second consistency
reading by the author, with the maintainer's independent review still required.

The prime, finite commutative ring, positive-power annihilation and arbitrary T all
occur as binders. The ordinary category and recorded classicality predicate occur in
the first five conjuncts. The localizing predicate includes repleteness, all triangles
and ambient sums; existence of ambient sums is explicit. Both truncations occur in
both closure and sum-preservation assertions. The latter now quantify the actual
classical family and every ambient coproduct cofan, with its coprojections retained.
The map r is unrestricted, and both comparison isomorphisms are natural and normalized
by the inclusion/projection equalities. Only the last clause assumes qcqs. Its exact
recorded bounded constructible finite-Tor generator class is retained, with the existing canonical coefficient realization applied explicitly to every
cohomology module before testing the same intrinsic classicality predicate. I checked
the actual three-factor definition of that realization and added its already landed
owning node to stmt_deps. I also checked that a zero cohomology module gives the
empty/zero cases of that same predicate.
No added boundedness, nonemptiness, nonzero-ring or coefficient-invertibility assumption
was found. No statement correction was necessary.

Validation: the final module passed `scompile.py` in sandbox mode (7.6 s) and library
mode (7.4 s), with no errors or warnings. The signature record matches the source
verbatim; all Lean lines are at most 100 characters. The delivery has one named theorem
and one whole-proof `sorry`. The item changes only `lean` and gains the single landed
statement dependency documented above. The required delivery dry run is run after this
final signature and report update.

## Repair of return L (immutable head 98070c178d44), H2

Replaced the added theorem-node statement dependency
`det-lem-integral-models-generators` with the landed existing:true definition node
`def-sfb-integral-model-generator-data`. I read its statement and full Lean record:
`lean.declarations` explicitly owns
`WeilConjectures.SixFunctors.integralModelIntrinsicRealization`. I reread that
unchanged definition and its source docstring in
`Sheaf.SixFunctors.IntegralModelsGenerators`: it is the composition of the actual
section-module equivalence, constant-scalar restriction and intrinsic realization,
not a choice from the integral-generation theorem. The import therefore stays the
same. No Lean file was moved, copied, or edited, and the theorem signature and proof
remain unchanged. Against the current shared node the packet changes only `lean`
and adds this definition node to `stmt_deps`.

The initial saved-packet dry run failed before preflight because the compile wrapper
could not load Mathlib from the published library; server confirmation reported
`Live published library is unavailable`. This is an infrastructure failure rather
than a Lean diagnostic. Compilation and the required repaired-packet dry run are
retried after the H2 repair.

Repair self-check: only `lean` and `stmt_deps` differ from the current shared node;
the sole added dependency is `def-sfb-integral-model-generator-data`; its existing
record owns the helper. The saved Lean signature is verbatim, with one whole-proof
`sorry` and all Lean lines at most 100 characters. The explicit repaired-packet
`scompile.py` retry also failed in infrastructure before compiling the item:
`unknown module prefix 'Mathlib'` while compiling the upstream overlay
`WeilConjectures.Mathlib.CategoryTheory.NatIso`; server confirmation again returned
`Live published library is unavailable`. No launcher or library files were changed.

## Retained-packet retry, 2026-10-21

Read the saved packet and ran the required initial `deliver2.py --no-push` before
changing anything. The H2 repair remains present: the only added statement
dependency is `def-sfb-integral-model-generator-data`, whose existing:true record
explicitly owns `integralModelIntrinsicRealization`. Rechecked the unchanged real
three-factor definition and its source docstring. Comparison with the current
shared node finds differences only in `lean` and `stmt_deps`; no stale stage-1
fields need rebasing. The signature matches the module verbatim, its only proof
is one whole-proof `sorry`, and every Lean line is at most 100 characters.

The initial dry run and the explicit prescribed `scompile.py` both exit 1 before
compiling this module. Both fail compiling the upstream overlay
`WeilConjectures.Mathlib.CategoryTheory.NatIso`, line 6, with
`unknown module prefix 'Mathlib'`. The reported search path contains only the
live project's build/lib/lean directory and the Lean toolchain library, and the
server confirmation is `Live published library is unavailable`. This is the
same infrastructure failure as the previous attempt, not an item elaboration
error or a busy-server timeout. The saved Lean module and repaired node have
been retained unchanged; no launcher scripts or live sources were modified.

The second dry run after this report update reproduced the identical exit-1
Mathlib-prefix failure and server-unavailable confirmation. Nothing was pushed.

## Further retained-packet retry, 2026-10-21

Ran the required saved-packet `deliver2.py --no-push` first, then the explicit
`scompile.py` for the unchanged module. Both exit 1 before checking the item:
the upstream overlay `WeilConjectures.Mathlib.CategoryTheory.NatIso`, line 6,
cannot find the compiled module
`Mathlib/CategoryTheory/Functor/Category.olean` in the live Mathlib build.
Both server confirmations say `Live published library is unavailable`.
This diagnostic is a missing published artifact, rather than an elaboration
error in this delivery or a busy-server timeout.

Rechecked the packet against the current shared node: only `lean` and
`stmt_deps` differ; the sole added dependency is the landed existing:true
`def-sfb-integral-model-generator-data`. Its `lean.declarations` owns
`WeilConjectures.SixFunctors.integralModelIntrinsicRealization`, whose unchanged
three-factor definition and docstring were reread. The theorem node
`det-lem-integral-models-generators` is absent from `stmt_deps`. The signature
still matches the Lean file verbatim; there is one whole-proof `sorry`, and
all Lean lines satisfy the 100-character limit. The H2 repair and Lean module
remain intact. No launcher script, live source or compiled artifact was edited.

## Current-main repair retry, 2026-10-21

The required initial saved-packet dry run still fails before item elaboration:
Mathlib/CategoryTheory/Functor/Category.olean is missing. The explicit
scompile.py retry instead encounters the missing compiled artifact
Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.olean while compiling
the upstream KanExtension.Preserves overlay. Both exit 1, and both server
confirmations report `Live published library is unavailable`.

Rechecked return L H2 against the current shared node and source. The sole added
statement dependency remains def-sfb-integral-model-generator-data, whose
lean.declarations owns the unchanged real integralModelIntrinsicRealization
definition. The theorem dependency det-lem-integral-models-generators is absent.
The theorem signature matches lean.statement verbatim, there is one whole-proof
sorry, and no Lean line exceeds 100 characters. The saved node had a stale
lean_audit value (null rather than the current empty record); refreshed all
non-delivery fields from the current shared node, preserving only lean and
stmt_deps from the packet. This removes that unintended difference. No Lean
module, launcher file, live source or compiled artifact was changed. The final
repaired-packet dry run is retried with this report.

## Retained H2 repair: current validation retry, 2026-10-21

Inspected the saved report and ran the prescribed saved-packet dry run first.
Rechecked against the current shared node: only `lean` and `stmt_deps` differ;
the only added dependency is `def-sfb-integral-model-generator-data`, and
`det-lem-integral-models-generators` is absent from `stmt_deps`. The landed
existing:true definition record lists `integralModelIntrinsicRealization`;
its unchanged definition and docstring were reread. The saved signature is
verbatim, with one whole-proof `sorry` and no Lean line over 100 characters.
No Lean or node change is required for the already retained H2 repair.

Both the initial `deliver2.py --no-push` and the explicit `scompile.py` exit 1
before checking the item. Their local compile diagnostic is exit 124 while
compiling the upstream overlay
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`,
with a 60-second timeout. Both server confirmations report
`Live published library is unavailable`. This is not a no-answer-from-server
message, nor a diagnostic against the delivered theorem. No launcher script,
live Lean source, or compiled artifact was changed. The repaired packet is
retained, and a final prescribed dry run follows this report update.

The final dry run also exits 1 and pushes nothing. Its local attempt repeats
the upstream SheafCohomology.Basic timeout, but server confirmation now
progresses through upstream dependencies and stops at
`Sheaf/CategoryTheory/SiteInverseImageTensor.lean:6:0`: the published object
`WeilConjectures/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.olean`
does not exist under the live server build. This is the latest concrete
validation blocker; the delivered theorem is still not reached. The H2
repair remains retained unchanged.

## Latest retained-packet validation, 2026-10-21

The required initial saved-packet `deliver2.py --no-push` and the explicit
`scompile.py Q14 lem-sfb-finite-classical-localizing` both fail before the
item is compiled. The local overlay compile cannot load the published
`WeilConjectures/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.olean`.
Server confirmation also fails in `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
because the published
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean` does not exist.
These are missing build artifacts in the prescribed compiler's upstream
library, not missing declarations or a diagnostic against this packet.
No compiler, launcher, upstream source, or build artifact was modified.

The repair self-check again passes: only `lean` and `stmt_deps` differ from
current shared main; the sole added edge is the landed definition node
`def-sfb-integral-model-generator-data`. That existing:true record owns the
unchanged real three-factor realization definition. The theorem-node edge
is absent, the signature is verbatim, and the unchanged module contains one
whole-proof `sorry` and no line over 100 characters. The packet is retained
for delivery once the prescribed published build is available.

## Current retained-packet repair verification, 2026-10-21

The first required saved-packet `deliver2.py --no-push` and the subsequent explicit
`scompile.py` both fail before compiling this item, in the upstream overlay
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleObject`, line 7.
The local wrapper and its current-server-source confirmation both report that
`WeilConjectures/CategoryTheory/GrothendieckAbelian/ConcreteCoefficients.olean`
is missing from the live published build. This differs from the previous retry's
missing TensorProduct object, but is again a published-build/tool failure, not an
elaboration diagnostic for this packet. No launcher scripts or live sources were
edited and no global build was run.

The H2 repair is retained. Mechanical self-check against the current read-only
shared node passes: only `lean` and `stmt_deps` differ, and the latter adds exactly
`def-sfb-integral-model-generator-data`. Its landed existing:true record explicitly
owns `WeilConjectures.SixFunctors.integralModelIntrinsicRealization`; rereading the
real three-factor definition confirms it does not choose data from the theorem.
The Lean file is unchanged. Its signature matches `lean.statement` verbatim, it
contains one whole-proof `sorry`, auto implicits are disabled, and every line is
at most 100 characters. The final dry run below retries the current-server check.

Final `deliver2.py --no-push` retry: failed before the item again, in
`EtaleInverseImageModuleObject.lean:7`, with local and server confirmation now
reporting missing published object
`WeilConjectures/Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Sheaf.olean`.
Thus two dry runs and the explicit compiler retry all fail in published upstream
artifacts. The repaired packet remains saved; nothing was pushed.

## Retained H2 packet: latest server-artifact check, 2026-10-21

Ran the required saved-packet dry run first, followed by the prescribed explicit
`scompile.py`. Both exit 1 before this item is elaborated. The local overlay
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleObject` cannot load
`WeilConjectures/SixFunctors/Etale/UpperLowerStar/Defs.olean`. The dry-run
server confirmation reaches `Sheaf.CategoryTheory.ModuleInverseImageAdjunction`
and reports missing `WeilConjectures/Topology/Stratification.olean`. The explicit
compiler's server confirmation progresses further, then fails in
`Sheaf.AlgebraicGeometry.ProEtaleOperations` because
`WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.olean`
is missing. These are published upstream artifacts, not item diagnostics or
busy-server no-answer timeouts.

Rechecked return L H2 against current shared main: only `lean` and `stmt_deps`
differ; the only added dependency is `def-sfb-integral-model-generator-data`,
and `det-lem-integral-models-generators` is absent from `stmt_deps`. Read the
landed existing:true record, which explicitly owns
`WeilConjectures.SixFunctors.integralModelIntrinsicRealization`, and reread
that definition's full signature, real three-factor body, and docstring.
The Lean module remains unchanged, the recorded signature matches verbatim
up to the proof delimiter, there is one whole-proof `sorry`, auto implicits
are disabled, and every Lean line is at most 100 characters. No stale
non-delivery node fields need refreshing. No launcher script, live source,
or build artifact was modified. A final prescribed dry run follows.

The final `deliver2.py --no-push` also exits 1 before item elaboration.
Its server confirmation stops in
`Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction:6` with the
same missing published finite-coefficient UpperLowerStar/Defs.olean.
Nothing was pushed; the repaired packet remains retained.

## Retained H2 repair: current validation retry, 2026-10-21

Read the saved packet and ran the required initial `deliver2.py --no-push`
before editing. Rechecked return L H2 against the current shared node:
only `lean` and `stmt_deps` differ, and the sole added edge is
`def-sfb-integral-model-generator-data`. Its landed existing:true record
explicitly owns `WeilConjectures.SixFunctors.integralModelIntrinsicRealization`.
Reread the full signature, source docstring and unchanged real three-factor
construction. The theorem-node dependency is absent from `stmt_deps`.
The signature is verbatim, auto implicits are disabled, there is one whole-proof
`sorry`, all Lean lines are within 100 characters, and JSON formatting passes.
No Lean file was edited, moved or copied.

The initial dry run progressed through upstream dependency compilation, then
exited 1 before item elaboration. Its local attempt timed out after 60 seconds
in `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`; server
confirmation timed out after 60 seconds in
`WeilConjectures/AlgebraicGeometry/EtaleCohomologyFilteredColimit.lean`.
The explicit `scompile.py` retry again reported the local upstream
`Sites.CohomologyContinuity` timeout and started server confirmation. These
are upstream implementation timeouts, not missing dependency interfaces or
a diagnostic against the delivered theorem. No launcher scripts, live sources
or compiled artifacts were edited, no limit was raised, and no global build
was run.

The explicit compiler returned exit 1. Server confirmation got past
`EtaleCohomologyFilteredColimit` (48.3 seconds), then compiled further
upstream dependencies and timed out after 60 seconds in
`WeilConjectures/AlgebraicGeometry/EtaleLimitCohomologyConnectingLadder.lean`.
The item was not elaborated. This was a concrete upstream timeout, not the
busy-server “no answer” diagnostic. A final prescribed dry run follows.

The final `deliver2.py --no-push` also returned exit 1 before item
elaboration. Server confirmation compiled further upstream dependencies,
including `EtaleLimitCohomologyConnectingLadder`, and ultimately reproduced
the timeout after 60 seconds in
`WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean`.
Thus the two dry runs and explicit compiler retry all failed in upstream
compilation; no diagnostic against this item was produced and nothing was
pushed. Final comparison with current shared main again finds only `lean`
and `stmt_deps` changes, with exactly the intended landed definition-node
addition. The signature and single-sorry/line-width checks still pass.
The H2 repair is retained unchanged for the next validation attempt.

## Upstream-timeout investigation and delivery-gate refusal, 2026-10-21

Ran the prescribed saved-packet dry run first. It reproduced the local and
server-confirmed 60-second timeout in
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`, before item
elaboration. The H2 correction remains intact: current shared main differs only
in `lean` and the single added landed definition dependency
`def-sfb-integral-model-generator-data`. Its definition record owns the unchanged
real `integralModelIntrinsicRealization`; the theorem dependency is absent.
The item signature is verbatim, auto implicits are disabled, the sole proof is
one whole-proof `sorry`, the JSON formatting is exact, and the maximum Lean line
length is 94.

Investigated the upstream module in sandbox copies only, using `scompile.py` for
every compiler call. The current server source read through `scompile.py --source`
agrees with the shared source. Profiling shows that `sectionsFunctor` and both
theorem headers elaborate quickly. A diagnostic run with a lower heartbeat limit
and progress markers reached the construction of the cohomology diagram and
cocone, the application of continuity, and the final elementwise argument. At
50,000 heartbeats it reported the expensive `whnf` at `exact congrArg _ hy`.
The reduction counters repeatedly unfold the Ext/derived single-complex and
inverse-image constructions. The tested restriction of `dsimp` to `dsimp only`,
local irreducibility of the cohomological comparison maps, and the backward
transparency option each still timed out. Merely supplying the missing function
to `congrArg` also still timed out. A further candidate removes the unnecessary
`classical` command as well as pinning that function; its validation was started.
These are diagnostic attempts, not a claim that the upstream timeout is fixed.
No theorem signature or docstring was changed, no existing sorry was added or
removed, and no limits were raised.

The requested upstream repair cannot be submitted through the prescribed stage-2
wrapper. Placed the concrete candidate at
`lean/WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean` in this
sandbox and reran the required dry run. It exits 1 immediately, before compilation
or preflight, with exactly:

```
FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean
```

This is a delivery-tool gate that refuses the upstream repair explicitly requested
by the current brief; it is distinct from the original Lean timeout. The wrapper
also requires each accepted module to be owned by a node's `lean.file`, so merely
allowing the upstream prefix would not yet provide the full upstream-repair
packet route. No launcher script was patched or copied, no live source or compiled
artifact was edited, no global build was run, and nothing was pushed. The item
packet, candidate, and diagnostic copies are retained in the authorized sandbox.

The remaining candidate compiler calls have now finished: removing `classical`
while pinning the `congrArg` function also times out locally and in server
confirmation. Thus no attempted upstream change is represented as a validated
repair. The final packet dry run below checks the independently actionable
upstream-path gate again; no push is attempted through a failing dry run.


## Current retained-packet repair retry

The prescribed initial dry run reproduced the leftover upstream-module path refusal.
Moved the old unvalidated upstream candidate out of the delivery's `lean/` tree into
`retained-attempts/upstream/`, keeping it as diagnostic history only. The delivery
now contains exactly the original item module and its node. No Lean source in the
item was edited. The requested H2 repair remains present: the item cites
`def-sfb-integral-model-generator-data`, not the integral-generation theorem.

Rechecked against the current shared node: the only differing fields are `lean`
and `stmt_deps`, and the only added dependency is that landed definition node.
Its `lean.declarations` explicitly lists the realization helper. The recorded
signature is byte-identical to the file, auto implicits are disabled, there is one
whole-proof `sorry`, and every Lean line is within 100 characters. No new nodes,
dependency modules, or statement correction are included.

The layout-corrected dry run proceeds into server compilation. The independent
explicit `scompile.py` check reports a 60-second timeout rebuilding the upstream
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`, before checking
the item, and begins the wrapper's required current-server confirmation. The
current upstream source was read through `scompile.py --source`; it still has the
expensive `exact congrArg _ hy` diagnosed in the prior retry. The existing
recorded helper module source is absent in the read clone; both its recorded
`Sheaf.SixFunctors.IntegralModelsGenerators` name and the corresponding
`WeilConjectures` name return `Module source unavailable` from the prescribed
source-reading wrapper. These source-reader results are recorded without
claiming that this retry reread that missing definition.

The explicit compile and the final layout-corrected `deliver2.py --no-push` both
finished with current-server confirmation:
`WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean: timeout after 60 s`.
The final dry run exits 1 with `COMPILE FAILED on the server, nothing pushed`.
The prescribed delivery route still cannot carry an upstream repair (the initial
dry run reproduced its `lean/WeilConjectures/` path refusal), and none of the
retained upstream experiments is a validated repair. No tool was modified, no
limits were increased, and no live sources or artifacts were edited. The H2
correction and unchanged item module remain ready in the sandbox; nothing was
pushed through the failed dry run.


## Definition-level repair and current delivery refusal, 2026-10-21

Ran the prescribed saved-packet dry run before edits. It reproduced the 60-second
CohomologyContinuity timeout; server confirmation independently found the missing
published IntegralModelsGenerators object. The prescribed source reader returns
Module source unavailable for both the recorded Sheaf module and its corresponding
WeilConjectures name. The explicit item compile subsequently encountered an upstream
unknown identifier constructible_of_iso in IntegralConstructibleSequentialHom.
These diagnostics precede elaboration of the delivered theorem.

The retained H2 repair was checked mechanically against current shared main:
only lean and stmt_deps differ, with exactly the added landed definition node
`def-sfb-integral-model-generator-data`; no statement dependency was removed.
The theorem signature is verbatim, the sole proof is one whole-proof sorry,
auto implicits are disabled, JSON formatting is exact, and maximum Lean line
length is 94. The item module remains unchanged.

Continued the definition-level timeout investigation in sandbox candidates only.
The bounded diagnostic confirms excessive unfolding of cohomological maps,
Ext additive structures, single complexes, and inverse-image constructions.
Broad transparency changes and local irreducibility alone did not validate.
A concrete definition repair now compiles cleanly: make the real existing
cohomologyTriangleMap definition @[no_expose], retain its data verbatim, and
export the exact equation cohomologyTriangleMap_eq with a closed rfl proof.
The owning module EtaleCohomologyTriangleLaws passed both prescribed compiler
checks, sandbox in 34.2 seconds and library in 51.3 seconds, with no warnings.
Its source is retained under definition-repair/lean/WeilConjectures/.
Three direct unfolding users have candidate adaptations to use that equation;
the multi-file scompile validation is recorded in definition-repair/users-compile.log.
A clean compile of the owning definition alone is not yet a claim that the
original continuity timeout or every caller has been repaired.

Tested the required delivery route with this concrete compiled upstream module
placed at its real sandbox delivery path. deliver2.py --no-push exits 1
immediately, before preflight or compilation, with exactly:

```
FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/AlgebraicGeometry/EtaleCohomologyTriangleLaws.lean
```

This is a concrete delivery-tool refusal of the explicitly requested upstream
definition repair, independently of any Lean timeout. No wrapper was edited or
copied, no path gate was bypassed, no limit was raised, and no shared source or
compiled artifact was changed. The test upstream file has been removed from the
active delivery tree; its candidate and validation logs remain under
definition-repair. The active packet retains the unchanged item module and H2
node repair. Nothing was pushed.


The multi-file definition/caller check compiled the sealed triangle-map module
(34.2 seconds sandbox, 51.3 seconds library) and its fixed-base continuity caller
(28.3 seconds sandbox, 20.0 seconds library). It found one direct unfolding user
in EtaleCohomologyLocalRingColimit whose dsimp could not use the new equation;
the saved candidate changes it to simp only. A focused three-file retry reaches
CohomologyContinuity but still times out there after 60 seconds, so the candidate
is not represented as a complete timeout fix. A reviewable source diff is saved
as definition-repair/repair.patch. No theorem statement or original docstring
was changed, and no new sorry was introduced by these experiments.

The final active-packet dry run returned exit 1 with no push. Its concrete
failure is now the upstream IntegralConstructibleSequentialHom unknown
constructible_of_iso at line 114 (7.1 seconds), before the item. The independent
upstream-path gate refusal above remains reproducible for the concrete compiled
definition repair. Neither this compiler error nor the residual timeout is
being labeled a tool failure: the blocking tool failure is specifically the
required delivery wrapper refusing the authorized upstream repair path.

The focused retry finished exit 1: its fallback current-server confirmation
also exceeded 60 seconds compiling EtaleCohomologyTriangleLaws. This does not
erase its earlier successful 34.2/51.3-second checks, but confirms that the
saved upstream candidate has not achieved reliable complete validation. All
compiler calls from this attempt have ended; no push was attempted.


## Current saved-packet retry and import visibility diagnosis, 2026-10-21

Ran the required saved-packet dry run before editing. It exits 1 before item
elaboration in `Sheaf.Paper.IntegralConstructibleSequentialHom:114`, with
`Unknown identifier constructible_of_iso`. An independent prescribed item
`scompile.py` reproduces that diagnostic. The saved H2 correction passes the
mechanical check against current shared main: only `lean` and `stmt_deps`
differ, exactly the landed `def-sfb-integral-model-generator-data` edge is added,
and the integral-generation theorem is absent from `stmt_deps`. The Lean file
remains unchanged; its signature is verbatim, there is exactly one whole-proof
`sorry`, auto implicits are disabled, and JSON formatting and line width pass.
Reread the owning landed existing:true definition record and the full signature,
docstring and real three-factor realization construction in the shared source.

Read the current failing module through `scompile.py --source`. Its helper was
moved to a private declaration in the Sheaf.UpstreamExtra derived-category
module, but its consumer only imports that module publicly. A sandbox candidate
retains the public import and adds `import all` for private helper access, without
changing any declaration, statement, proof or original docstring. The two-file
prescribed compiler accepts the candidate sequential-Hom module in 12.2 seconds,
then times out after 60 seconds compiling the upstream
`Sheaf.Paper.ContinuousConstructibleIntegralDenominators`. Current-server
confirmation is running; this is not represented as a completed item compile.
The candidate and complete compiler output are retained under
`definition-repair/lean/Sheaf/Paper/IntegralConstructibleSequentialHom.lean` and
`definition-repair/sequential-import-compile.log`.

Tested the delivery wrapper with that import repair in the active delivery tree.
It refuses it before compilation because the module is not the `lean.file` of
an included node. The actual owning theorem node is reached through imports but is not in the
current item's statement/proof DAG prerequisite closure (checked by exhaustive
traversal). Its existing proved module cannot be replaced by stage-2 sorry
statements just to package an import fix. Removed the test file from the active tree.
Also retested the retained upstream definition repair at its original module
path: the required wrapper still exits 1 immediately with:

```
FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/AlgebraicGeometry/EtaleCohomologyTriangleLaws.lean
```

Removed that test file too; both candidates remain in definition-repair only.
No tool gate was bypassed, launcher script changed, live source or build artifact
written, limit raised, or global build run. The active packet again consists
only of the original unchanged item module and the H2-repaired item node.
A final active-packet dry run follows.


The candidate compiler has now finished exit 1. Server confirmation accepts the
import visibility candidate in 27.2 seconds and passes the previously timed-out
denominators module in 34.3 seconds, plus further integral and Tate-twist
prerequisites. It stops at a 60-second timeout in
`Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback`, before the
item is elaborated. The current-server source reader subsequently shows that
main has independently fixed the original private-helper import by replacing
`import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`
with the corresponding `import all Sheaf.UpstreamExtra...` module. Thus the saved
sandbox candidate is unnecessary for that error and remains diagnostic only.

The final active-packet dry run also finishes exit 1, with nothing pushed.
It gets past those earlier prerequisites but fails in
`Sheaf.Paper.LocalizingClosureCtfEqualsBc:99` with
`Unknown constant ModuleCat.HasFiniteProjectiveDimension`. Source inspection
identifies another retired-import defect: this module publicly imports the
withdrawn empty `Sheaf.RingTheory.GlobalDimension`, whereas the real unchanged
predicate is now in `WeilConjectures.RingTheory.GlobalDimension:51`. The
failing module's owning node is also outside this item's current DAG prerequisite
closure. This is an upstream compiler error, not itself a tool failure. The
concrete tool refusal remains the reproduced delivery path gate quoted above;
no supported upstream-repair delivery route was available in this task.

Final self-check against the latest shared node again passes: only `lean` and
`stmt_deps` differ, exactly the requested landed definition edge is added, no
theorem-node statement edge remains, the signature is verbatim, JSON formatting
is exact, and the active delivery contains exactly the unchanged item Lean file.
All compiler invocations from this retry have ended. No push was attempted
through a failed dry run; the narrow H2 correction is retained for delivery.


## Maintenance-following repair validation, 2026-10-21

Ran the required initial saved-packet dry run before editing. Kept the reviewed
Lean module byte-identical to head 98070c178d44 (SHA-256
5912468662179d7dd5e7565bb097fc47d854769ee7da0d99eece9b332a7612fa).
The H2 correction remains exactly as requested: stmt_deps includes the landed
existing:true definition node def-sfb-integral-model-generator-data, whose
lean.declarations owns integralModelIntrinsicRealization; the integral-generation
theorem is not a statement dependency. Reread the owning definition record and
the helper's full signature, docstring and real three-factor construction.
Only lean and stmt_deps differ from the current shared item node, with exactly
that definition edge added. The recorded signature is verbatim, JSON uses indent 1
and a final newline, auto implicits are disabled, the sole proof is one whole-proof
sorry, and the maximum line width is 94. The active delivery tree has exactly the
item module; old upstream/import-repair experiments remain outside lean/.

The maintenance private-helper and global-dimension import repairs are already
in the live library and are not resubmitted here. Initial checks encountered
upstream 60-second timeouts; subsequent server confirmation passed those modules.
The explicit prescribed scompile.py retry completed successfully (exit 0):
Sheaf/AlgebraicGeometry/FiniteClassicalLocalizing.lean checked in 17.3 seconds,
nice 19, two threads, limit 60 seconds, with no item diagnostics or warnings.
No theorem, definition, statement, import or docstring in the item was changed.
The dry-run retry and final delivery use the normal deliver2.py route.

The final dry run passed (exit 0): deliver2.py --no-push printed OK for
commit 2f495f7f3e3, with the item module compiled in both sandbox and library
modes and the server preflight accepted. Only the report, corrected item node,
and original item module were staged. The prescribed push follows.
