## Worker report

The delivery states `lem-sf-semilinear-clopen-unit-projector` in
`Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector`. The namespace is
`AlgebraicGeometry.ProEtale.VaryingRing`. All nine theorem proofs are `sorry`;
all definitions contain real construction data. No statement, dependency list,
source, proof or other existing node field changes; only `lean` changes.

The statement has two main declarations, both recorded in `lean.declarations`:
`semilinearClopen_unit_projector` gives the clopen identities and the ordinary
representative normalization; `semilinearClopen_coefficient_naturality` gives
naturality for arbitrary compatible coefficient changes, for restriction and
derived extension of scalars. Supporting statements and canonical maps also
belong to this node, and every declaration has its source/blueprint docstring.

Hypotheses and objects, in the order of the node:

- An arbitrary inverse coefficient sequence is `R : ℕ → CommRingCat.{u + 1}`
  and `φ : ∀ n : ℕ, R (n + 1) ⟶ R n`. Starting at zero only renumbers the
  node's sequence. No flatness, finiteness or surjectivity is assumed.
- `X : Scheme.{u}` uses the dependency's `Modules R φ X` and `Derived R φ X`.
  They are modules on the actual vertical sequence site over `X.ProEt`, and
  their ordinary unbounded derived category. The site retains object universe
  `u+1` and Hom universe `u`. There is no new category of systems or localization.
- `s : U ⟶ X` has `[IsOpenImmersion s] [IsClosedImmersion s]`. For an open
  immersion, closed image is equivalent to being a closed immersion; this does
  not impose an additional mathematical condition.
- The complementary open is `c : C ⟶ X`, `[IsOpenImmersion c]`, with
  `hc : Set.range c = (Set.range s)ᶜ`. Any presentation of that complementary
  open is allowed; no chosen model or quasi-compactness assumption is added.
- The node's restriction `P_s` is named `G R φ s` by the dependency. Its derived
  direct image `S_s` is named `P R φ s`; open extension is `J R φ s`.
  The actual adjunctions are `jAdj R φ s` and `adj R φ s`; their units are
  exactly the node's `u_s` and `η_s`.
- `semilinearClopen_openUnit_isIso` supplies invertibility of the specified open
  unit. `clopenToDirect` is the explicit right-adjunction transpose of its
  inverse: right unit followed by `P` of the inverse open unit, with functor
  unitors and associator. It is not an arbitrary isomorphism.
- `clopenPi` is the exact localization of the existing `modulePi R φ s`, using
  `Localization.liftNatTrans`, the derived identity comparison and the exact
  derived composition comparison. Thus its input map is the dependency's
  actual ordinary identity/zero projector, not an unrelated derived map.

Clauses, in the order of the node:

1. Invertibility of `t_s` is the first conjunct
   `IsIso (clopenToDirect R φ s)`.
2. `(t_s P_s) ∘ π_s = η_s` is the natural-transformation equality
   `clopenPi ... ≫ Functor.whiskerLeft (G ...) (clopenToDirect ...) = (adj ...).unit`.
   Lean composition runs in the reverse textual order from the node's circle notation.
3. `P_s π_s = 1` under the open unit is stated without suppressing transport:
   for every whole derived system `M`, `G_s.map (π.app M) = u_s.app (G_s.obj M)`.
   Since `u_s` is invertible, this is exactly the asserted identified identity.
4. `P_c π_s = 0` is `∀ M, (G R φ c).map ((clopenPi ...).app M) = 0`.
5. These are transformations on the whole derived system category: `clopenPi`
   and `clopenToDirect` are `NatTrans`, and the unit equation is an equality of
   `NatTrans`. The other equations quantify over all objects of that category.
   Nothing asserts that level evaluations detect equality of derived maps.
6. The corresponding ordinary section formulas induce the derived maps.
   The projector is defined by localization. The last conjunct of the core
   theorem identifies `clopenToDirect` on every complex with termwise
   `moduleOpenToP` through the canonical exact/right-derived comparison and the
   standard exact-functor factorization isomorphisms. This uses
   `semilinearClopen_push_colimits` and its instance, because clopen ordinary
   direct image is exact. This helper is proof step 4, not an extra hypothesis.
7. Coefficient naturality is explicit, rather than an unconstrained predicate.
   For arbitrary `D`, `ψ`, ring maps `α n : R n ⟶ D n` and exactly their commuting
   equation `hα`, `clopenCoefficientMap` applies the existing constant-sheaf
   functor to `α n`. `clopenCoefficientRestriction` uses the recorded
   `SemilinearSections.systemMap` and `res`; its derived functor is
   `clopenCoefficientRes`. `clopenCoefficientScalar` uses the recorded
   `semilinearDerivedSections` coefficient-extension model and normalized
   scalar adjunction; its `scalar.T` is the actual K-flat derived extension.
8. The ordinary pushforward comparison `clopenCoefficientPush` is chosen from
   a unique existence statement requiring identity on every section at every
   `(n,H)`. Hence the use of choice selects a uniquely specified map. Its
   inverse-image mate is localized to `clopenCoefficientG`. The derived open
   and direct-image comparisons are the specified mates of this comparison,
   named `clopenCoefficientJInv`, `clopenCoefficientJ`, `clopenCoefficientP`.
   Their invertibility is stated, not assumed. The scalar-extension comparisons
   `clopenScalarG`, `clopenScalarJ`, `clopenScalarP` are their transposes under
   the dependency's scalar adjunctions. They are also stated to be invertible.
9. `ClopenCoefficientNaturality` is just the four displayed equations: the
   comparison square for `t_s`, the square for `π_s`, the open-unit square and
   the direct-image-unit square. `semilinearClopen_coefficient_naturality`
   asserts these equations for both actual scalar functors and their specified
   comparisons. The predicate does not quantify over arbitrary comparison maps
   in lieu of constructing them. Its functor arguments are specialized in the
   theorem to the actual coefficient restriction and extension functors.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.VaryingRingOperations`:
  `coefficients`, `coefficientTransition`, `Modules`, `Derived`, `push`, `pull`,
  `moduleAdj`, `extension`, `moduleJAdj`, `G`, `P`, `J`, `adj`, `jAdj` and their
  exactness/additivity instances. Imported publicly through the arrows module.
- `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`:
  `moduleOpenToP`, `moduleOpenToP_isIso`, `modulePi` and
  `moduleJAdj_unit_isIso`. The recorded primary declaration `gamma` was also
  read; it is the proper/open mate and not the clopen-unit identity of this item.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `SemilinearDerivedSectionsData`, `semilinearDerivedSections`, especially
  `coefficientExtension`. Its public dependencies supply `ScalarSystems`,
  `ScalarData`, `systemMap`, `res` and `resD`; no versions are copied.
- `def-weil-scheme-morphism-properties` is the convention record without a
  declaration. Its named Mathlib `Scheme`, `IsOpenImmersion` and
  `IsClosedImmersion` are the ones used.
- Proof imports: `Sheaf.SixFunctors.OpenTensorNormalizationData`
  (`SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction`),
  `Sheaf.CategoryTheory.SiteCoveringAxioms`
  (`CategoryTheory.Precoverage.IsSiteForCoverings`),
  `Sheaf.CategoryTheory.RingedSiteModules` (`CategoryTheory.ringedSiteModules`),
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
  (`CategoryTheory.Functor.exactFunctor_derivedFunctor`), and Mathlib
  `Localization.liftNatIso` / `liftNatTrans` in
  `Mathlib.CategoryTheory.Localization.Predicate`. The pro-etale site module
  and semilinear module are already imported publicly by the operations module.

Sources read: local `literature/stacks-project/sites-modules.tex`,
`lemma-extension-by-zero` (Tag 03DI), including the direct-sum presheaf formula;
`derived.tex`, `lemma-right-derived-exact-functor` (Tag 015F), especially (4);
and current blueprint
`main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`,
the sentence about coefficient comparisons for adjunction units and counits.
The six proof steps in the item's DAG record supply the system extension.

Edge cases checked mathematically before writing:

- `U = ∅`: both clopen extensions/direct images are zero, their comparison is
  an isomorphism between zero objects, and `π` and `η` are the maps to zero.
  Restriction to the complementary whole scheme sends `π` to zero.
- `U = X`: the complement is empty; `π` is identity under the canonical open
  identifications and the complementary equation is a map between zero objects.
- `X = ∅`: all clauses reduce to the zero category; no nonempty hypothesis occurs.
- Zero coefficient rings are permitted by `CommRingCat` and give zero module
  categories. No field or nontriviality assumption occurs.
- Nonflat transitions such as `ℤ/4 → ℤ/2` and nonflat coefficient changes are
  permitted. Only derived, K-flat scalar extension is used for coefficient change.
- Arbitrarily unbounded complexes and noncartesian systems are included by
  `Derived R φ X`; no boundedness, normalization or flatness binder is present.

Searches actually run through `msearch.py Q10 <item>`:

- `leanfinder`: “Clopen extension by zero equals direct image for strict
  semilinear module sheaf systems and the component projection equals the
  adjunction unit”. Eight results, including sheaf presentation generators,
  condensed locally constant counits and topological sheaf gluing, no exact match.
- `loogle`: `CategoryTheory.Adjunction.unit, CategoryTheory.IsIso`.
  Twelve results: generic adjunction equivalence/full-faithfulness facts,
  no semilinear clopen projector statement.
- `grep`: `clopen.*(unit|project)|openToP|modulePi`.
  Three Mathlib hits (quasi-affine open covers and ideal quotient `modulePi`),
  none for this statement.
- `leansearch`: “For an open and closed immersion the extension by zero of
  inverse systems of module sheaves agrees with derived direct image and the
  component projection is the adjunction unit”. Eight results, including
  ordinary scheme-module restriction adjunctions, no derived system identity.
- `rg` of `lean/WeilConjectures` for the node id, clopen unit/projector and
  `modulePi`/`openToP`: fixed-coefficient étale clopen-transfer lemmas and unrelated
  rank-stratum projectors; no arbitrary varying-ring system theorem.
- `rg` of `lean/Sheaf`: the existing varying-ring ordinary arrows,
  `VaryingRingProperOpenPasting.modulePi_components` and
  `VaryingRingModulePiComplementZero.modulePi_complement_zero` supply ordinary
  component statements, not this derived unit plus coefficient-naturality claim.
  Those broad pasting modules are not imported; the existing owning module for
  `modulePi` is imported directly. New declaration names were also searched in
  Mathlib, upstream and `Sheaf`, with no collisions.

No new independent notion, new node or dependency-module repair is needed.
The coefficient comparison helpers specialize recorded notions and expose the
maps needed by the final clause of this same item. No statement dispute or
source correction was found. The unchanged DAG proof is reproduced in the main
and helper docstrings as appropriate to their individual clauses.

Validation: the complete module passed `scompile.py` on the live server as both
sandbox and library module, with no errors or warnings (5.1 s and 5.2 s).

Delivery dry run: `deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push`
printed OK: the three-file packet passed the server preflight and compiled.

## Repair retry: published-library failure

On 2026-10-21 the retained packet was inspected and the prescribed
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push` was run first.
It exited 1 before compiling this module: the overlay dependency
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`, line 6, reported
`unknown module prefix 'Mathlib'`. Server confirmation reported
`Live published library is unavailable`. A separate prescribed `scompile.py`
invocation for the retained module reproduced the same error and server
confirmation, also exiting 1. These current failures supersede the historical
validation above. No Lean or node changes were made: the diagnostic concerns
the compiler environment, which cannot be repaired within the worker sandbox;
launcher scripts and the published library must not be edited. Nothing was
pushed.

## Repair retry: missing published Mathlib object

On 2026-10-21 this retry again inspected the retained packet and ran
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push` first.
It exited 1 before compiling the item: the overlay dependency
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`, line 6, reported
that the published object file
`Mathlib/LinearAlgebra/TensorProduct/Basic.olean` does not exist. The prescribed
`scompile.py Q10 lem-sf-semilinear-clopen-unit-projector` invocation with the
retained module independently reproduced the same missing-object diagnostic
and exited 1. Both wrappers confirmed against current server sources and
reported `SERVER CONFIRMATION: Live published library is unavailable`.
This is a published-library tool failure before this delivery's Lean is checked;
no change within the sandbox can supply the missing published Mathlib build.
The Lean module and node record remain retained without changes, launcher
scripts and published artifacts were not modified, and nothing was pushed.


## Repair retry: missing published presheaf monoidal object

On 2026-10-21 this retry inspected the retained report and ran the required
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push` first.
The earlier tensor-product overlay compiled, but the next overlay,
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom`, failed at
line 6 because the published Mathlib object
`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.olean` does not exist.
The prescribed `scompile.py` invocation on the retained
`SemilinearClopenUnitProjector.lean` independently reproduced this diagnostic.
Both wrappers exited 1, confirmed against current server sources, and reported
`SERVER CONFIRMATION: Live published library is unavailable`.
The failure occurs before this delivery's module is checked. The retained Lean
module and node record were preserved; no launcher script or published library
was modified and nothing was pushed. Restoring the published Mathlib build is
outside the authorized worker sandbox.


## Repair retry: upstream object still missing after dependency progress

On 2026-10-21 the saved packet and its report were inspected before running
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push`.
The wrapper advanced through the dependencies that previously failed, waiting
for their concurrent compiles. It eventually exited 1: the overlay
`WeilConjectures.Algebra.Homology.HomComplexSectionsCochains` exceeded its
60-second file limit. The wrapper's current-server confirmation then failed in
`Sheaf/Paper/CoefficientHomRepresentativeEvaluation.lean:6:0` because the
published object
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean` does not exist.

A separate prescribed `scompile.py Q10 lem-sf-semilinear-clopen-unit-projector`
run on the retained module independently failed with exit 1 in
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation`, both locally and in its
current-server confirmation, with that same missing upstream object. The item
module was never reached. This is a compiler-environment prerequisite failure,
not a missing mathematical interface in the delivery, and cannot be repaired
by changing an authorized sandbox statement. No launcher tool or upstream
library was changed and nothing was pushed.

The retained Lean source was preserved. Its signature was checked verbatim
against `lean.statement`, all 26 declarations are recorded, all nine `sorry`
tokens are whole named theorem proofs, no line exceeds 100 characters, and
`autoImplicit` is disabled. The current repository node was compared with the
saved packet; only its current audit metadata had changed independently.
The sandbox node was refreshed from the current repository while retaining
its `lean` record, so no stale non-`lean` field is proposed for delivery.


## Repair retry: current-server missing object confirmed (2026-10-21 04:23 UTC)

Inspected the retained report and ran the required saved-packet dry run first:
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push`.
It exited 1 before checking the item. The overlay
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation`, line 6, could not import
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` because its published
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean` does not exist.
The wrapper's current-server confirmation reproduced the diagnostic (0.4 s).

An independent prescribed `scompile.py` invocation on the retained module also
exited 1 at the same dependency, with the same missing published object in both
the initial compile and current-server confirmation (0.4 s). The item itself
was never checked. This is a published compiler-environment failure; supplying
a mathematical helper or changing this statement cannot restore the missing
object. Launcher scripts and the published library are outside the authorized
write scope and were not modified.

Compared the sandbox node with the current shared repository by reading both
JSON files: only `lean` differs, so the saved packet proposes no stale metadata
changes. Preserved the Lean source and node record unchanged, retained all prior
work, and did not push an unvalidated packet.

## Repair retry: missing published object persists (2026-10-21 04:24 UTC)

Read the saved report and ran the required saved-packet dry run first:
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push`.
It exited 1 before checking the item. The overlay
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation`, line 6, could not import
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`: the published object
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean` does not exist.
Its confirmation against current server sources reproduced the same error.

The independent prescribed `scompile.py` invocation on the retained module also
exited 1 before checking the item, with the identical missing-object diagnostic
in both its initial run and current-server confirmation (0.4 s and 0.3 s).
This is an unavailable published compiler artifact, not a missing mathematical
interface. Repairing it requires writes outside this worker's sandbox or a
change to the launcher tooling, both forbidden by the brief. Neither was done.
Compared the retained node with the current shared node: only `lean` differs.
Preserved the retained Lean module and node record, and did not push.


## Repair retry: published dependency objects unavailable (2026-10-21 04:26 UTC)

Inspected the saved report and ran the required saved-packet dry run first:
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push`.
It exited 1 before checking this item: the overlay
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation`, line 6, failed because
`WeilConjectures/SixFunctors/Etale/Derived/Hom.olean` is absent from the
published live library. Current-server confirmation reproduced that error.

An independent prescribed `scompile.py` run on the retained module also exited 1
before checking the item. Its overlay
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, line 6, failed because
`Sheaf/Paper/FiniteFieldFiber.olean` is absent from the published live library.
Current-server confirmation reproduced this second missing-object error.
Both errors concern already supplied dependency modules and published build
artifacts, not absent mathematical notions or a diagnostic in the saved module.
They cannot be repaired by writing statement interfaces in this sandbox.
No launcher script or live library file was modified.

Read and compared the current shared node with the retained sandbox node:
only `lean` differs, so no stale metadata changes are proposed. The retained
main signature matches `lean.statement` verbatim, auto-bound implicits remain
disabled, and no source line exceeds 100 characters. The Lean source and node
record were retained unchanged. Nothing was pushed because the required
compiler checks could not reach this item.


## Repair retry: shared dependency has type errors (2026-10-21 04:33 UTC)

Inspected the retained packet and ran the prescribed saved-packet dry run first:
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push`.
Also ran the prescribed `scompile.py` separately on the retained Lean module.
Both wrappers advanced past the previously missing published artifacts, then
exited 1 before checking this item. The current overlay dependency
`Sheaf.CategoryTheory.RingedSiteDualityMaps` failed at lines 795 and 828
with type mismatches (27.5 s). At 795 the equality of sectionwise chosen
coefficient-Hom components does not elaborate as the required composite with
`homComplexπ`; at 828 `ringedSiteBidualDegree_eval` does not elaborate as the
required coefficient-Hom component formula for `β`.

Read the current server source using
`scompile.py --source Sheaf.CategoryTheory.RingedSiteDualityMaps` and traced
the mandatory import path in the read clone:
`VaryingRingProperOpenArrows → VaryingRingOperations → SemilinearDerivedSections
→ SemilinearSystemsExistence → RingedInternalHomShiftOfUniverses
→ RingedSiteDualityMaps` (all intermediate names have the recorded Sheaf paths).
Removing optional proof imports cannot avoid the failure: it is in the primary
recorded statement dependency's import closure. This is an existing shared
module's proof failure, not an absent notion or an unusable statement interface
that can be supplied by this delivery. Repairing that shared source or the
overlay machinery is outside this worker's sandbox and was not attempted.

Compared the retained node with the current shared node: only `lean` differs.
The recorded main signature still matches the Lean source verbatim;
`autoImplicit` is false; no source line exceeds 100 characters; the nine named
postponed theorem proofs and 26 recorded declarations are retained. The Lean
module and node were preserved unchanged. No unvalidated packet was pushed.

## Repair retry: shared dependency failure confirmed (2026-10-21 05:46 UTC)

Read the saved packet and ran the required saved-packet dry run first:
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push`.
It exited 1 before compiling the delivered module. The mandatory overlay
`Sheaf.CategoryTheory.RingedSiteDualityMaps` failed at lines 795 and 828
with the same type mismatches recorded in the previous retry (21.7 s).
The independent prescribed `scompile.py` invocation on the retained module
also exited 1 with those identical errors (21.7 s). Thus the returned unknown
Mathlib-prefix failure has cleared, but the prerequisite compilation remains
broken; neither wrapper reaches this item's Lean file.

This is a failure in the shared dependency's existing proof bodies, not an
absent canonical object or an unusable mathematical statement interface.
Replacing the item's definitions, duplicating the dependency, or weakening its
statement would not repair it. Direct edits to the shared module and changes
to launcher tools are forbidden, so neither was attempted. Nothing was pushed.

Compared the saved node with the current shared node by reading both JSON
files: only `lean` differs. The saved main signature is present verbatim in
the module, all 26 declarations remain recorded, `autoImplicit` is disabled,
and no source line exceeds 100 characters. No repair-note file exists for
this item. Retained the module and node unchanged, with the complete prior
statement work and report available for the next retry.


## Repair retry: mandatory dependency proof errors (2026-10-21 05:49 UTC)

Inspected the retained report and ran the prescribed saved-packet dry run first:
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push`.
It exited 1 before checking the item, with type mismatches at lines 795 and
828 of the overlay `Sheaf.CategoryTheory.RingedSiteDualityMaps` (21.7 s).
An independent prescribed `scompile.py` invocation on the saved module also
exited 1 with the same two errors (21.7 s). The unknown Mathlib prefix from
the returned head no longer appears, but the mandatory dependency still fails.

Read the current server source with `scompile.py --source` and inspected the
corresponding proof bodies. The first error is in `ringedSiteBidualFormula_ext`:
section evaluations of chosen coefficient-Hom components do not elaborate as
evaluations of the composite with `homComplexπ`. The second is in
`ringedSiteOrdinaryBidual_existsUnique`, where `ringedSiteBidualDegree_eval`
does not elaborate as the coefficient-Hom component formula. These are existing
shared proof errors, rather than missing notions or an unusable statement
interface. The required public arrows import operations, which import
`SemilinearDerivedSections`; its `SemilinearSystemsExistence` import reaches
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`, which publicly imports
the failing module. Removing optional imports from this delivery cannot fix it.
The brief prohibits edits to the shared dependency and launcher tools.

Compared the saved node with current shared main by reading both JSON files:
only `lean` differs. The saved main signature occurs verbatim in the module,
all 26 declarations remain recorded, auto-bound implicits are disabled, and
no source line exceeds 100 characters. There is no current repair-note file.
Preserved the Lean module and node record unchanged and did not push an
unvalidated packet. The saved work remains available for a retry once the
mandatory dependency compiles.


## Repair retry: live dependency proof failure (2026-10-21 05:50 UTC)

Inspected the saved packet and ran the prescribed saved-packet dry run first:
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push`.
It exited 1 before checking the delivered file: mandatory overlay
`Sheaf.CategoryTheory.RingedSiteDualityMaps` has type mismatches at lines 795
and 828 (21.7 s). An independent prescribed `scompile.py` invocation on the
retained module exited 1 with exactly these two errors (21.7 s). The historical
unknown Mathlib-prefix error no longer occurs.

Read the current server source with `scompile.py --source` and inspected lines
760--835. The failures are proof bodies of `ringedSiteBidualFormula_ext` and
`ringedSiteOrdinaryBidual_existsUnique`: coefficient-Hom components do not
elaborate as the required `homComplexπ` expressions. This is a shared dependency
compilation failure, before the item, rather than a missing mathematical notion
or an unusable recorded signature. The dependency is on the mandatory import
path documented above; a sandbox statement repair cannot fix its proof bodies.
The shared library and launcher tools remain read-only, so neither was edited.

Compared the sandbox node with current shared main: only `lean` differs. The
main recorded signature remains verbatim in the module, all 26 declarations
are recorded, all nine postponed proofs remain named theorems, auto-bound
implicits are disabled and no source line exceeds 100 characters. There is no
repair-note file for the item. Retained the complete Lean and node work without
changes; no unvalidated delivery was pushed.


## Repair retry: prerequisite still fails (2026-10-21 05:51 UTC)

Read the retained report, then ran the prescribed saved-packet dry run first.
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push` exited 1
before reaching this item: the mandatory overlay
`Sheaf.CategoryTheory.RingedSiteDualityMaps` has type mismatches at lines 795
and 828 (21.7 s). The separate prescribed `scompile.py` invocation on the
retained module reproduced both errors and exited 1 (21.7 s).

Read the live server source using `scompile.py --source` and inspected the
failing proof bodies. In `ringedSiteBidualFormula_ext`, the chosen
coefficient-Hom component evaluation does not elaborate as the required
composite with `homComplexπ`; in `ringedSiteOrdinaryBidual_existsUnique`, the
degree evaluation does not elaborate as the coefficient-Hom formula. These
are shared prerequisite proof failures, not a missing notion or an unusable
statement signature. Their repair requires changing the shared dependency,
which this worker is explicitly forbidden to edit. No tool was patched and
no library source was changed.

Compared the saved node with the current shared node by reading both files:
only `lean` differs. The recorded main signature is verbatim in the module,
all 26 declarations remain recorded, all nine postponed proofs are named
theorems, auto-bound implicits are disabled, and no line exceeds 100 characters.
No repair-note file is present. Preserved the Lean module and node record;
nothing was pushed because neither required compiler check reached this item.


## Repair retry: required live dependency type mismatches

On 2026-10-21 this retry inspected the saved packet and ran the required
`deliver2.py Q10 lem-sf-semilinear-clopen-unit-projector --no-push` first.
The former missing-Mathlib failure has cleared, but compilation now fails
before the item in live overlay `Sheaf.CategoryTheory.RingedSiteDualityMaps`,
with type mismatches at lines 795 and 828/829 (depending on the current live
revision). The bidual extensionality proof does not identify the sectionwise
projection/composition expression, and the ordinary bidual construction does
not identify the coefficient projection with `homComplexπ`.

The prescribed `scompile.py` independently reproduced the failures. Removing
the item's four optional proof imports did not avoid this module: the required
dependency chain imports it too. A sandbox experiment with simplification in
the dependency did not compile; attempting a dry run with that extra module
was correctly rejected because it belongs to no node of this packet. That
experimental file was removed and the item's original imports restored.
No shared repository or launcher file was edited. The retained item module
and node record remain unchanged, and nothing was pushed. This is an upstream
compilation failure before the wrappers can validate this delivery.


## Repair retry resolved: validation against current live build

The earlier diagnostics in this retry were superseded while the live
dependencies were repaired. The subsequent dry run progressed past the
bidual module but reported an upstream CohomologyContinuity timeout, with
server confirmation timing out in RingedInternalHomShiftOfUniverses.
A fresh prescribed scompile.py invocation then passed both sandbox and library
compilations of the retained item (5.9 s and 5.5 s), without diagnostics.
No upstream repair is included in this delivery.

The retained module and item node were self-checked again: only lean differs
from the current shared node, the main signature is verbatim, every line is
at most 100 characters, and autoImplicit is false. The hypothesis and clause
correspondences in the Worker report remain unchanged: arbitrary coefficient
sequences, clopen immersion and complementary open; invertibility of the
specified transpose; the unit and both restriction identities; termwise
normalization; and both coefficient-change naturalities. All theorem proofs
remain sorry and all construction data remain explicit.

## Second reading by Q10

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
