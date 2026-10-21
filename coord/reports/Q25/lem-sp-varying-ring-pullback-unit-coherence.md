## Worker report

The module `Sheaf.AlgebraicGeometry.VaryingRingPullbackUnitCoherence` states
`AlgebraicGeometry.ProEtale.VaryingRing.pullback_unit_coherence`. Its two
conjuncts are the ordinary and derived left identity unit equations for the
actual operations of `def-sp-varying-ring-operations`. The single theorem proof
is `sorry`. No definitions or new nodes are introduced, and no statement
correction is needed. The retained theorem is unchanged; this repair also
removes one unused import from its recorded semilinear existence prerequisite.

Hypotheses and clauses, matched against the node:

- Arbitrary commutative rings R_n are `R : ℕ → CommRingCat.{u + 1}`; arbitrary
  transition homomorphisms are `φ : ∀ n : ℕ, R (n + 1) ⟶ R n`. There is no
  flatness, finiteness, or invertibility assumption on them.
- Schemes and every scheme morphism are `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  This follows the dependency's existing universe convention: the small
  pro-etale site has object universe u+1 and morphism universe u, and module
  values and rings live in universe u+1. No equality of site universes is added.
- The actual ordinary inverse image L_f is `pull R φ f`. It is the left adjoint
  to the actual sectionwise `push R φ f`, not an arbitrary functor or map.
- The specified c_{1_X,f} is `(moduleGComp R φ (𝟙 X) f).hom`. Its source is
  `pull R φ ((𝟙 X) ≫ f)` and its target is
  `pull R φ f ⋙ pull R φ (𝟙 X)`.
- The specified e_X is written directly as
  `Adjunction.leftAdjointIdIso (moduleAdj R φ (𝟙 X)) (modulePId R φ X)`.
  This is exactly the ordinary adjoint identity used in the dependency's gId,
  with the section-normalized direct-image identity `modulePId`; no second
  identity comparison is defined or chosen. `Functor.whiskerLeft (pull R φ f)`
  applies e_X at L_f, giving the node's e_X L_f.
- The first equality composes c with that whiskered e, in Lean's left-to-right
  `≫` convention. Its right side is
  `(eqToIso (congrArg (pull R φ) (Category.id_comp f))).hom`, the comparison
  induced by `(𝟙 X) ≫ f = f`. Thus, before source transport the composite equals
  the transport map; after transport it is the identity, exactly as stated.
  The composite with the identity functor is definitionally the original
  functor in this API, so an additional unitor term is unnecessary.
- The derived G_f is `G R φ f`, the existing exact `mapDerivedCategory` of pull
  on the ordinary unbounded derived category of all semilinear systems.
  The second conjunct uses precisely `(gComp R φ (𝟙 X) f).hom` followed by
  `Functor.whiskerLeft (G R φ f) (gId R φ X).hom`.
- Its right side is
  `(eqToIso (congrArg (G R φ) (Category.id_comp f))).hom`. This is the equality
  transport requested by the final sentence, not a coefficientwise check.
  No evaluation functor occurs, and no boundedness or cartesianness is assumed.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.VaryingRingOperations`:
  `AlgebraicGeometry.ProEtale.VaryingRing.Modules`, `Derived`, `push`, `pull`,
  `moduleAdj`, `modulePComp_existsUnique`, `modulePComp`, `moduleGComp`,
  `modulePId_existsUnique`, `modulePId`, `G`, `gComp`, and `gId`. I read their
  signatures and docstrings, including the direct-image section formulas and
  the exact derived composition and identity definitions.
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`:
  `CategoryTheory.Adjunction.leftAdjointIdIso`, which is the exact ordinary
  identity comparison already used by gId, and the generic unitality lemmas.
- The recorded proof dependencies `lem-weil-pbc-conjugate-iso-unit-equation`
  and `def-weil-pbc-composite-adjunction` are Mathlib matches, respectively
  `CategoryTheory.unit_conjugateEquiv_symm` in
  `Mathlib.CategoryTheory.Adjunction.Mates` and
  `CategoryTheory.Adjunction.comp` in
  `Mathlib.CategoryTheory.Adjunction.Basic`. These modules are proof imports.
  Their signatures, unit equations, and accompanying declarations were read.
- `lem-sp-exact-derived-transformation-pasting` has neither a lean record nor a
  mathlib_match in the read repository. It is a proof dependency only; no part
  of its missing interface is needed to type this statement, so no dependency
  module is added. The theorem docstring retains its exact role in proof step 4.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`remark-base-change` (Tag 07A7), lines 4032–4059; and the node's full four-step
isolated OrdinaryUnits proof. Tag 07A7 motivates the adjoint-comparison
convention; the identity unit law itself is the isolated argument recorded in
the node. The docstring gives all four proof steps: identity graphs; adjunction
unit equations; naturality and uniqueness; exact derived localization with
transport. It does not claim that Tag 07A7 alone states this lemma.

Edge cases checked mathematically before writing: f = 1_X makes this the same
unit coherence for the identity; the empty scheme introduces no nonemptiness
condition; the zero coefficient ring and the zero system remain allowed;
nonflat maps such as ℤ/4 → ℤ/2 impose no new hypothesis because geometric inverse
image is exact on these systems; unbounded and noncartesian systems are still
objects of the unchanged dependency categories. Both comparison maps have the
same source and target even though inverse image along the identity scheme map
is only specified up to isomorphism, not identified strictly with the identity.

Searches actually run with the prescribed `msearch.py Q25
lem-sp-varying-ring-pullback-unit-coherence` wrapper:

- LeanFinder: “Canonical inverse image composition and identity comparisons for
  semilinear module sheaf systems satisfy the identity unit equation”. Eight
  hits, mostly free module/unitHomEquiv lemmas; no exact match.
- Loogle: `CategoryTheory.Adjunction.leftAdjointCompIso,
  CategoryTheory.Adjunction.leftAdjointIdIso`. The two generic
  `leftAdjointCompIso_comp_id` and `leftAdjointCompIso_id_comp` lemmas were found.
  Their types require right-adjoint coherence as an additional premise and do
  not assert this normalized geometric ordinary-and-derived statement.
- Mathlib grep: `leftAdjointCompIso_id_comp|pullback_id_comp`. Eight hits,
  including sheaf/presheaf pullback and scheme-module pseudofunctor lemmas.
  `SheafOfModules.pullback_id_comp` uses the actual identity site functor and
  ring identity, whereas scheme identity base change is only canonically
  isomorphic to that site functor. It also has no derived system clause.
- LeanSearch: “Pullback composition with identity morphism on inverse systems
  of sheaves over varying coefficient rings agrees with the canonical identity
  comparison”. Eight hits, including `SheafOfModules.pullback_id_comp`,
  `Scheme.Modules.pseudofunctor_right_unitality`, and over-site pullback laws;
  these concern other categories or leave out the normalized derived clause.
- Project/source rg: node id, `moduleGComp`, `moduleGId`,
  `moduleGComp_id_left|gComp_id_left|pullback_unit_coherence` in `lean/Sheaf`,
  `lean/WeilConjectures`, and `dag/lean_names_upstream.json`. No public exact
  statement was found. `VaryingRingProperOpenPasting.lean:969,986` has separate
  private ordinary/derived helpers. They are internal declarations of the
  downstream proper/open pasting node, which itself depends on this node, and
  cannot supply a public dependency interface without closing an import cycle.
  The single-coefficient strict-tower private helpers concern other categories.
  The new public theorem states both required clauses using the owning
  dependency's existing comparisons and introduces no duplicate notion.

No STATEMENT-DISPUTED issue or node fault was found.

Validation: scompile.py compiled the sandbox and named library module cleanly
(3.1 s and 2.9 s respectively); the expected postponed theorem is the only
`sorry` in this delivery. The dry-run and final delivery results are recorded
below when available.

## Second reading by Q25

This is a separate manual reading pass by this worker; the dispatcher explicitly
prohibits starting other agents. The maintainer supplies the independent review.
With the node, operations module, and completed statement open, I checked R and φ
are unrestricted; X, Y and f are bound; both functors are the existing system
functors; c is used in its forward direction; e is the adjoint of the fixed graph
identity; and the whiskering is on the correct side. The ordinary right side is
transport of pull and the derived right side is transport of G, both along
Category.id_comp f in the forward direction. The conjunction includes both
ordinary and derived assertions with no evaluation, flatness, or boundedness
premise. No mismatch was found and no statement change was made. The docstring
was checked against each of the four node proof steps, including that the right
adjoints are used only to establish the ordinary equality, and that localization
of transport is justified by equality elimination.

Delivery dry run: `deliver2.py Q25 lem-sp-varying-ring-pullback-unit-coherence
--no-push` returned OK: commit c2ce78a2471 passes preflight and compiles; nothing
was pushed by that dry run. Only the item's lean field differs from the read
repository; the recorded signature is verbatim and every Lean line is at most
100 characters.

## Returned-delivery validation (2026-10-21)

The retained packet was inspected before any edit. Its node differs from the
current read clone only in `lean`; the recorded theorem signature matches the
module verbatim, all Lean lines meet the 100-character limit, all variables and
the universe are explicitly bound, and the sole postponed proof is the named
item theorem. The ordinary and derived conjuncts still match the node. No Lean
statement or dependency change is indicated by the returned diagnostic.

The required first retry of `deliver2.py Q25
lem-sp-varying-ring-pullback-unit-coherence --no-push` failed before compiling
this module. Both its local attempt and its confirmation against current server
sources failed in the upstream overlay
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`, line 6, with
`unknown module prefix 'Mathlib'`. The reported search path contains only the
live project's build directory and the Lean toolchain, with no Mathlib package
path. The confirmation explicitly says `Live published library is unavailable`.

A separate prescribed `scompile.py Q25
lem-sp-varying-ring-pullback-unit-coherence <sandbox module path>` reproduced the
same upstream error and the same server confirmation. This is the exact failure
reported for returned head `737c45d526e3`, rather than a Lean error in this packet.
No launcher scripts, compiler paths, published library, or shared repository
files were modified. The packet is retained; no delivery was pushed in this
retry because neither authorized compiler wrapper can access the live library.

## Dispatcher repair retry (2026-10-21T04:10:53Z)

Inspected the retained report and ran the required first dry run before making
any edit. `deliver2.py Q25 lem-sp-varying-ring-pullback-unit-coherence --no-push`
failed before reaching the delivered module. The diagnostic has changed from
an unknown Mathlib prefix to a missing published Mathlib object:
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`.
The upstream overlay `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`
fails at line 6 in 0.1 seconds. Confirmation against current server sources
repeats the failure and says `Live published library is unavailable`.

A separate prescribed `scompile.py Q25
lem-sp-varying-ring-pullback-unit-coherence` invocation on the retained module
reproduced that exact missing-object diagnostic, including server confirmation.
This is a published-library/tool infrastructure failure before this packet is
compiled, rather than a statement or elaboration diagnostic to repair locally.
The authorized wrappers cannot validate the delivery in this state.

The current read-clone node and sandbox node differ only in `lean`; the current
node has no landed Lean record. Re-read the retained module and node: both
ordinary and derived clauses are present, all variables and universes are bound,
the recorded signature occurs verbatim, no Lean line exceeds 100 characters,
and the single `sorry` is the named theorem proof. There is no repair note in
the current read clone. Kept all Lean and node content intact; only this report
was extended. No push, shared-repository edit, Git command, launcher-script
change, or published-library modification was performed.


## Dispatcher repair retry (2026-10-21T04:13:00Z)

Inspected the retained packet and ran the prescribed first dry run before
changing it. The dry run failed in the upstream tensor-product overlay because
`Mathlib/LinearAlgebra/TensorProduct/Basic.olean` was absent. The current-source
server confirmation reported `Live published library is unavailable`.

Compared the saved node with the current read clone without running Git. The
current node has gained `lean_audit: {}`; refreshed the non-lean node fields
from that current node while retaining this packet's Lean record. The node now
differs only in `lean`. The module remains intact: the signature matches the
record verbatim, no line exceeds 100 characters, auto-implicits are disabled,
and the sole `sorry` is the named theorem proof. The ordinary and derived
identity comparisons and equality transports remain the two required clauses.

The separate prescribed `scompile.py Q25
lem-sp-varying-ring-pullback-unit-coherence <module>` failed before reaching
this module in upstream overlay
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom`, line 6:
`Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.olean` does not exist.
The repeated dry run after refreshing the node reproduced exactly that failure.
Both current-source server confirmations said
`Live published library is unavailable`. This is a missing published Mathlib
artifact, not an elaboration error in this packet. No launcher script, shared
source, compiler configuration, or published artifact was changed; nothing
was pushed. Validation cannot finish until the authorized compiler wrappers
can access the published library.


## Dispatcher repair retry (2026-10-21T04:23:07Z)

Read the retained report and ran the saved packet's dry run before editing.
Compared the packet with the current read clone: only `lean` differs, no
current Lean attachment or repair note is present, and the module is not
already landed. Re-read the theorem and the operations dependency's actual
ordinary and derived comparisons. Both required clauses, unrestricted ring
transitions, equality transports and explicit universe binders are retained.
The node signature matches the module verbatim; every line is within 100
characters and the single postponed proof is the named item theorem.

The first `deliver2.py --no-push` waited for concurrent upstream dependency
compiles, then its local attempt timed out in
`WeilConjectures.Algebra.Homology.HomComplexSectionsCochains`. Server
confirmation failed earlier than this packet, in
`Sheaf/Paper/CoefficientHomRepresentativeEvaluation.lean:6:0`, with:

```text
object file '/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean' of module WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic does not exist
```

The separate prescribed `scompile.py` invocation reproduced this exact
missing-object failure in 0.4 seconds locally and on server confirmation.
Thus the reproducible blocker is the published library artifact, not the
initial local timeout or a diagnostic in this theorem. The published sources,
artifacts and launcher scripts are read-only for this worker; no such files
were changed. Retained the Lean module and node unchanged and recorded this
retry here. The final `deliver2.py --no-push` retry reproduced the same missing tensor-product
object in 0.4 seconds, including server confirmation. Nothing was pushed; the
retained packet remains ready for validation once that artifact is available.


## Dispatcher repair retry (2026-10-21T04:24:42Z)

Inspected the saved report and ran the prescribed first `deliver2.py --no-push`
before editing the packet. It failed in the upstream overlay
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation`, line 6, before reaching
this theorem. Both the local attempt and current-source server confirmation
reported the missing published artifact
`WeilConjectures/Mathlib/LinearAlgebra/TensorProduct/Basic.olean`
under the live project's `.lake/build/lib/lean` directory.

A separate prescribed `scompile.py` call on the retained module also failed
before reaching it. Its local attempt reported missing
`WeilConjectures/Mathlib/CategoryTheory/Sites/SheafHom.olean`; its current-source
server confirmation reproduced the missing tensor-product artifact above.
These are missing published artifacts, not statement errors or server-busy
exit 124. Neither wrapper can validate this packet in the current library.

Compared the sandbox node with the current shared read clone using file reads,
without Git: only `lean` differs, the current node has no Lean record, and no
repair note exists. Re-read the retained theorem: its ordinary and derived
conjuncts use the specified comparisons and identity equality transports.
The signature is verbatim in the node record, every line meets the 100-character
limit, auto-implicits are disabled, and the sole postponed proof is the named
item theorem. The packet's Lean and JSON remain intact. No launcher script,
shared source, compiler configuration, or published artifact was modified.
The report records the concrete tool failure; no delivery has been pushed.


## Dispatcher repair retry (2026-10-21T04:26:38Z)

Inspected the saved report and ran the required first dry run on the retained
packet before editing. `deliver2.py Q25
lem-sp-varying-ring-pullback-unit-coherence --no-push` failed before reaching
this theorem, in `Sheaf.Paper.CoefficientHomRepresentativeEvaluation:6:0`:

```text
object file '/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/SixFunctors/Etale/Derived/Hom.olean' of module WeilConjectures.SixFunctors.Etale.Derived.Hom does not exist
```

The current-source server confirmation reproduced the same failure (0.4 s).
A separate prescribed `scompile.py` invocation on the retained module failed
before reaching it, in `Sheaf.Paper.RestrictionOfScalarsExact:6:0`:

```text
object file '/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/Sheaf/Paper/FiniteFieldFiber.olean' of module Sheaf.Paper.FiniteFieldFiber does not exist
```

Its current-source server confirmation reproduced that failure (0.1 s).
Neither error is a server-busy timeout or an elaboration diagnostic in this
packet. The authorized wrappers cannot validate it against the published
library while these artifacts are unavailable.

Compared the saved node against the current shared read clone using file reads:
only `lean` differs, the current node has no Lean record, and no item repair
note exists. Re-read the retained theorem against the node: both the ordinary
and derived identity-unit clauses use the specified comparisons and equality
transport. The recorded signature matches verbatim; all Lean lines are at most
100 characters; auto-implicits are disabled; the universe and variables are
explicit; the single `sorry` is the named item theorem. Retained the Lean and
node unchanged and extended only this report. No shared source, published
artifact, launcher script or compiler configuration was modified; nothing was
pushed. This retry remains blocked by the confirmed published-artifact failure.


## Dispatcher repair retry (2026-10-21T04:34:11Z)

Inspected the retained report and packet, then ran the prescribed first dry run
before editing. The dry run and a separate prescribed `scompile.py` invocation
both failed before reaching this theorem. Unlike the earlier missing-artifact
failures, this retry reaches an upstream source error:

- `Sheaf.CategoryTheory.RingedSiteDualityMaps.lean:795:4`: type mismatch in
  `(hβ i q h' hqi U x W φ).trans (hγ i q h' hqi U x W φ).symm`,
  comparing the chosen `coefficientHomComponent` with `homComplexπ`.
- The same module at `828:4`: type mismatch in
  `ringedSiteBidualDegree_eval`, where the required formula uses
  `WeilConjectures.coefficientHomComponent`.

Both wrappers report the same overlay snapshot
`95fe8449bb0472d0fb5c47544aef5f199bafc802ac4938eb2ebb3f54e7f22318`
and the same two compiler errors (27.5 seconds). Read current server source with
`scompile.py --source Sheaf.CategoryTheory.RingedSiteDualityMaps`; it matches
the shared read clone, up to the wrapper's final newline. This is a failure
in the required live dependency closure, not an elaboration error in this
packet or a server-busy exit 124.

Checked whether an import repair can avoid the failure. The mandatory statement
dependency has this import path:
`VaryingRingOperations → SemilinearDerivedSections → SemilinearSystemsExistence
→ RingedInternalHomShiftOfUniverses → RingedSiteDualityMaps`. The first import
supplies the node's actual `pull`, `moduleGComp`, `G`, `gComp` and `gId`;
removing it would discard the required dependency interface. Neither of this
packet's proof imports introduces the failing path. Repairing the upstream
proofs would require edits to the shared read-only library, outside the
authorized packet; no import-only repair here removes this error.

Compared the saved node with the current read clone without Git: only `lean`
differs, no Lean attachment or repair note is present on the current node, and
the module has not landed. Re-read the node and the actual ordinary and derived
comparison definitions in `VaryingRingOperations`. Both required unit clauses
use the specified comparisons and explicit equality transport, with arbitrary
rings and transition maps, all variables and the universe explicitly bound,
and no extra hypotheses. The recorded signature is verbatim; every Lean line
is at most 100 characters; auto-implicits are disabled; the sole postponed
proof is the named item theorem. No statement or dependency repair is indicated
by the returned diagnostic. Retained all Lean and node content and updated only
this report. No shared source, launcher script, compiler configuration or
published artifact was modified, and nothing was pushed.

Final dry-run retry after recording this diagnosis again failed in the same
required `RingedSiteDualityMaps` overlay at lines 795 and 828, with the same
type mismatches and snapshot hash. The wrapper exited 1 and explicitly printed
`COMPILE FAILED on the server, nothing pushed`. Delivery remains unvalidated.


## Dispatcher repair retry (2026-10-21T05:46:44Z)

Inspected the saved report and ran the required first `deliver2.py Q25
lem-sp-varying-ring-pullback-unit-coherence --no-push` on the retained packet.
It exited 1 before compiling this theorem, reporting `COMPILE FAILED on the
server, nothing pushed`. The required upstream module
`Sheaf.CategoryTheory.RingedSiteDualityMaps` still fails at lines 795 and 828:
the proof terms using `homComplexπ` do not have the types expressed with
`WeilConjectures.coefficientHomComponent`. A separate prescribed `scompile.py`
call on the retained module reproduced both errors in 21.7 seconds. Both
wrappers used overlay snapshot
`fcf3d81923f39a93f40790da657d1c7172b3a0564784c7d1d9117dd13b53e8fb`.
This is neither a busy-server exit 124 nor the earlier missing Mathlib artifact.

Rechecked the mandatory import chain in the current read clone:
`VaryingRingOperations → SemilinearDerivedSections → SemilinearSystemsExistence
→ RingedInternalHomShiftOfUniverses → RingedSiteDualityMaps`. The first module
owns the required actual `pull`, `moduleGComp`, `G`, `gComp`, and `gId`.
Removing its import would discard the specified dependency interface;
replacing that interface would duplicate the node's existing canonical
constructions. The diagnostic is in upstream proofs, not an unusable statement
interface requiring an (A)/(B) addition. Shared Lean files and launcher tools
remain read-only; neither was modified or bypassed.

Compared the sandbox node against the current main read clone by parsing the
files without Git: only `lean` differs; main has no Lean attachment and there
is no repair note for this item. Re-read the theorem and current dependency
comparison definitions. Both ordinary and derived clauses, their direction,
identity whiskering, arbitrary coefficients and equality transports still
match the item. The record's signature is verbatim, every Lean line is at most
100 characters, auto-implicits are disabled, and the only `sorry` is the named
item theorem. No statement correction is indicated. Retained the Lean and
node unchanged, extended only this report, and did not push an unvalidated
packet. The required wrappers remain unable to compile the dependency closure.


## Dependency modules

`lem-coef-semilinear-system-existence` owns
`Sheaf.Paper.SemilinearSystemsExistence`. Its current recorded interface failed
to compile through an unused import of
`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`, which imports
`Sheaf.CategoryTheory.RingedSiteDualityMaps`. The server reported type
mismatches in the latter module at lines 795 and 828. The supplied dependency
module removes only that unused import. Its structure, theorem signature,
source and proof docstrings, and postponed theorem proof are byte-for-byte
unchanged. The dependency node changes only its Lean record, with the repair
reason recorded in `lean.note`.

This is an actual transitive prerequisite: the item uses
`def-sp-varying-ring-operations`, which uses
`lem-coef-semilinear-derived-sections`, which uses
`lem-coef-semilinear-system-existence`. No new dependency edge is introduced.
The canonical functors and ordinary/derived comparisons remain those of the
original operations module. No arbitrary map or replacement construction is
introduced.

`def-sp-varying-ring-operations` owns
`Sheaf.AlgebraicGeometry.VaryingRingOperations`. The first repaired compile
then reached an unrelated import chain through
`StrictTowerProperOpenCalculus`, `FiniteConstantCoefficientTransport` and
`ProEtale.Comparison.LowerStarAcyclic`, ending in
`Sites.CohomologyContinuity`, which timed out at 60 seconds. Replace that broad
import with its smaller prerequisite `StrictTowerOpenExtension`, which owns
the actual single-level `modulePullback`, `moduleDirectImage`, `moduleJ` and
`moduleJAdj` used here. Import ring filtered colimits and concrete coefficient
sheafification explicitly to retain the ring-sheafification instance previously
supplied transitively. All declarations and their proofs remain unchanged;
only imports differ. The node changes only in `lean`, with this reason in
`lean.note`. No compile timeout was increased.

## Repair validation (current retry)

Inspected the saved packet and ran the required first `deliver2.py --no-push`.
It reproduced the bidual type mismatches at lines 795 and 828. A separate
`scompile.py` call reproduced the same diagnostic. Read the current server
source with `scompile.py --source`, then traced imports and DAG dependencies.
The unused-import repair avoids the defective bidual implementation without
changing its read-only source. Experimental copies of alternative repairs
are retained only under scratch and are not part of the delivery.

Rebased the item and dependency node copies from the current read repository
without any Git command. The item differs only in `lean`; the dependency
differs only in `lean`. Rechecked both ordinary and derived clauses and the
verbatim recorded theorem signature. The item still has exactly its original
postponed theorem proof; the dependency retains its existing named postponed
theorem. Compilation and dry-run results follow below.

The repaired `scompile.py` call compiled all three delivered files individually
in dependency order, including sandbox and library names, with no errors or
unexpected warnings. Library timings were 1.7 s for
`SemilinearSystemsExistence`, 16.9 s for `VaryingRingOperations`, and 1.8 s for
`VaryingRingPullbackUnitCoherence`. The intermediate
`SemilinearDerivedSections` also compiled in 5.8 s. All files remain below the
fixed 60 s limit. A local structural check confirmed that every recorded
signature occurs verbatim, all lines are at most 100 characters, and each
node differs from the current base only in `lean`.

## Final delivery-tool failure

The repaired packet compiles cleanly, but `deliver2.py Q25
lem-sp-varying-ring-pullback-unit-coherence --no-push` fails in the server
preflight after staging the seven intended module, node and report paths.
The gate rejects the existing proved theorems in the dependency module, e.g.:

```text
(c) lean/Sheaf/AlgebraicGeometry/VaryingRingOperations.lean
(def-sp-varying-ring-operations): theorem
AlgebraicGeometry.ProEtale.VaryingRing.pull_exact: the proof is not `sorry`
(stage 2 states; every theorem and lemma ends with `:= by sorry` or `:= sorry`)
```

It issues the same refusal for the original `modulePComp_existsUnique`,
`modulePId_existsUnique`, `push_isRightAdjoint`, and the other already-proved
helpers. A structural comparison against the read repository confirms that
every non-import line of both supplied dependency modules is unchanged.
Thus these are existing published proofs, not proofs written in this stage-2
packet. Replacing them by `sorry` would discard existing verified work and
is not an appropriate repair of an import-only dependency change.

The human launcher instructions explicitly say a gate that seems wrong is
reported as BLOCKED and launcher scripts must never be patched or worked
around. No tool was edited and no delivery was pushed. The sandbox retains
the compiled import-only repairs, the node records, and
`retry-pruned-operations-compile.log` / `retry-repaired-dry-run.log` as evidence.
The required remaining action is a preflight fix allowing unchanged existing
proofs in dependency modules carried only for import repairs.


## Dispatcher repair retry (2026-10-21T06:08:20Z)

Read the saved packet and ran the required first dry run before changing any
file. The dry run completed its compilation phase, staged the seven intended
paths, and exited 1 with `PREFLIGHT FAILED, nothing pushed`. It still rejects
unchanged existing proofs in the import-only dependency repair, for example:

```text
(c) lean/Sheaf/AlgebraicGeometry/VaryingRingOperations.lean
(def-sp-varying-ring-operations): theorem
AlgebraicGeometry.ProEtale.VaryingRing.modulePId_existsUnique:
the proof is not `sorry` (stage 2 states; every theorem and lemma
ends with `:= by sorry` or `:= sorry`)
```

The refusal also names `pull_exact`, `push_isRightAdjoint`,
`modulePComp_existsUnique`, and other existing helpers. Compared both dependency
modules with the current live server sources obtained using the prescribed
`scompile.py --source`: every non-import line is identical, including all
existing proofs. This confirms the gate is rejecting preserved upstream work;
no proof was added by this stage-2 repair. Replacing those proofs with postponed
proofs would discard existing work rather than repair the imports. The launcher
instructions explicitly require a wrong gate to be reported as BLOCKED and
forbid editing or bypassing the tools.

A separate prescribed `scompile.py` invocation on all three delivered modules
exited 0, with no errors or unexpected warnings. Each file compiled separately:
`VaryingRingOperations` in 32.9 s, `SemilinearSystemsExistence` in 3.5 s, and
`VaryingRingPullbackUnitCoherence` in 2.8 s under library names. Sandbox checks
also passed within the fixed 60 s limit. The original missing-Mathlib return
is therefore no longer the current failure.

Compared all three node copies with the current read clone without Git: each
differs only in `lean`. The item has no current Lean attachment or repair note.
Rechecked both ordinary and derived clauses against the node and the actual
comparison definitions: unrestricted rings and transitions, the specified
adjoint identity, left whiskering, and forward equality transport are retained.
Every recorded signature is verbatim, every Lean line is at most 100 characters,
and auto-implicits are disabled. No statement correction is needed. All Lean
and node content is retained; only this report was extended. No tool, shared
source, compiler configuration, or published artifact was modified, and no
unvalidated delivery was pushed. The remaining blocker is the concrete
preflight refusal of unchanged dependency proofs.


## Maintenance repair and current packet scope (2026-10-21)

Maintenance commit `ced1d0987aeb0a77c460871ec1db534945b5a86b` on the server's
`sheaf-dag` applies the two import-only prerequisite repairs outside this
stage-2 statement packet. Both modules were compiled sequentially with
`tools/lean_file.sh` at the unchanged 60 s limit: SemilinearSystemsExistence
6.1 s, VaryingRingOperations 33.0 s, no errors or warnings. Every non-import
line is unchanged, preserving every existing proof. The commit was made with
the required identity and SHEAF_LEAD=L-only under coord/.merge.lock.

The current packet now contains only the original unit-coherence module, its
item node, and this report. The four redundant prerequisite module/node copies
were removed after preserving adjacent `.maint-Q25-unit-coherence-1792562946.bak`
backups. This report has the same backup suffix. The earlier dependency repair
sections describe historical attempts; no dependency modules are delivered
in the current packet. No theorem statement, definition, proof, docstring, or
DAG dependency was changed by maintenance.

The repeated preflight failure came from tools/stage2_delivery.py applying its
sorry-only rule to every theorem in a supplied dependency module, including
unchanged published proofs. No protected tool was edited. The item should now
use the repaired library prerequisites and be delivered through the ordinary
tool after a successful dry run. See the maintenance REPORT.md for evidence
and the requested upstream gate change.


## Final worker validation (2026-10-21)

The first dry run in this retry reproduced the unchanged-proof gate failure.
A separate scompile.py call compiled all three retained modules cleanly.
After the maintenance prerequisite repair, scompile.py with the item alone
compiled cleanly against live dependencies (sandbox 4.3 s, library 3.1 s).
The now-minimal packet passed deliver2.py --no-push: commit 19f3d1ed48d,
preflight and per-file compilation OK. No protected tool was changed.

Final self-check confirmed that the packet contains exactly one Lean module
and one JSON node, the node differs from the current read clone only in lean,
the signature is verbatim, all Lean lines meet the 100-character limit, and
the sole sorry is the named item theorem. Re-read both clauses: the ordinary
and derived compositors have the specified direction, identity comparison,
whiskering and equality transport; no hypotheses or clauses changed.
The existing Second reading section remains the mathematical self-review.
