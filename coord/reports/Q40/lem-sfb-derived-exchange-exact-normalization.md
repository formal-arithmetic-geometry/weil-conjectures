## Worker report

The module `Sheaf.Paper.DerivedExchangeExactNormalization` constructs the ambient
pullback-square comparison and its canonical adjunction mate, and states all clauses of
`lem-sfb-derived-exchange-exact-normalization`. The first theorem states the counit
identity, exactness of both functors, compatibility with every integer shift, and the
triangle morphism with its three prescribed components. The second states the
full-subcategory restriction identity. The third explicitly identifies the recorded
bounded-constructible base-change components with the ambient exchange. All theorem proofs are `sorry`; all definition
and instance data are existing canonical constructions.

Hypotheses and clauses:

- The standing setting is bound explicitly: `ℓ : ℕ`, `Fact ℓ.Prime`, `k : Type u`,
  `Field k`, `Fact (ringChar k).Prime`, and `Fact (ringChar k ≠ ℓ)`. Each of the four
  schemes is an `Over (Spec (.of k))` object with `LocallyOfFiniteType`, `QuasiCompact`
  and `IsSeparated` on its structure morphism. The section includes these standing
  hypotheses in both theorem declarations. `linter.unusedSectionVars` is disabled
  because this categorical identity does not use the standing geometric restrictions.
- Every commutative condensed ring is admitted: `Λ` is an abelian sheaf on
  `coherentTopology Profinite`, with `MonObj Λ` and `IsCommMonObj Λ`. This is exactly
  the underlying-object presentation of `Profinite.CondensedRing`, not a topological
  presentation, a finiteness-coefficient assumption, or an adic-completeness condition.
- The square is `sq : CommSq g' p' p g` in the category of k-schemes. Its image under
  `Over.forget` is the ambient scheme square. There is no cartesian or proper assumption.
- The actual ordinary unbounded derived functors are the dependency declarations
  `moduleObjectDerivedPullback` and `moduleObjectDerivedPushforward`. The adjunction
  is the existing `derivedUpperStarLowerStarAdjunction`.
- `moduleObjectDerivedPullbackSquareComparison` is the inverse compositor for p',g,
  then the equality in the square, then the compositor for g',p. It uses the existing
  `leftDerivedUpperStarComp`, with Lean diagrammatic functor composition.
- `moduleObjectDerivedExchange` is `mateEquiv` applied to that comparison and the two
  canonical adjunctions. Mathlib's defining composite is unit insertion, square
  transport, and counit contraction, including its canonical associators and unitors.
- The first conjunct of `moduleObjectDerivedExchange_exact_normalization` is the
  displayed counit equation for every K, in Lean's left-to-right composition order.
  The next two conjuncts are `.IsTriangulated` for Gp followed by Pg and Pg' followed
  by Gp'. Pullback `CommShift ℤ` is transported along the canonical comparison with
  the exact termwise functor; pushforward `CommShift ℤ` is precisely the published
  K-injective instance. These structures are fixed data, not existential choices.
- `NatTrans.CommShift ... ℤ` gives the entire integer-shift square. The final conjunct
  quantifies over every distinguished triangle T and produces a morphism between
  the two image triangles whose `hom₁`, `hom₂`, and `hom₃` are exactly B at the three
  vertices. Its `TriangleMorphism.comm₃` field is the connecting square. Exactness
  asserts that both image triangles are distinguished.
- `moduleObjectDerivedExchange_fullSubcategory` takes four arbitrary object
  properties `S_X`, `S_Y`, `S_X'`, `S_Y'`, each `IsTriangulated`. The six preservation
  hypotheses `hPp`, `hPg`, `hPp'`, `hPg'`, `hGp`, `hGp'` are precisely the four
  pullbacks and two pushforwards in the node. Their restrictions are the existing
  `ObjectProperty.liftFullSubcategory` functors. The two restricted adjunctions are
  `ObjectProperty.liftFullSubcategoryAdjunction` of the actual ambient adjunctions,
  so their unit and counit are their restrictions, not freely chosen adjunction data.
  `θ` is the restricted square isomorphism, and `hθ` says at every object that its
  underlying component is the ambient comparison component. Thus it specifies
  precisely the required restriction of the composition comparison. The conclusion
  identifies the underlying component of its restricted mate with B at K.obj.
- The theorem
  `boundedConstructibleBaseChangeOfPreserves_app_eq_moduleObjectDerivedExchange`
  renders the Dbc clause directly using the recorded
  `boundedConstructibleBaseChangeOfPreserves`. It takes its preservation witness H,
  the four triangulatedness hypotheses, and the componentwise restriction of the
  published square comparison. The canonical restricted adjunctions already have
  the ambient unit and counit by their construction. Its conclusion equates every
  actual restricted component (under the full inclusion) with B at K.obj.
- This also follows from the general Dbc substitution: substitute the four existing
  `ProEtale.boundedConstructible (condensedRingObj Λ T)` predicates and their
  triangulatedness/preservation hypotheses into the second theorem. The Hom types,
  identities and compositions of their `FullSubcategory` are ambient ones. The
  definition `boundedConstructibleBaseChangeOfPreserves` is exactly the same
  restricted unit--square--counit formula, so this specialization identifies its
  components when its preservation and restriction hypotheses hold. No unconditional
  preservation, triangulatedness, or finiteness theorem is asserted here.

Dependency declarations read and used:

- `Sheaf.Paper.CondensedModuleDerivedPushpull`: the two module-object total derived
  functors; publicly reexports `derivedUpperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `leftDerivedUpperStarComp`, `leftDerivedUpperStarIsoMapDerivedCategory`, and
  `derivedUpperStarLowerStarAdjunction`, read with their complete source signatures.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the explicit field setting and `compactificationOverField`; no compactification
  is needed in the exchange formula.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Sheaf.Paper.BoundedConstructibleBaseChange`:
  `boundedConstructibleBaseChangeOfPreserves` and the existing restricted comparison.
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`: publicly retains
  the relevant general ring-object `ProEtale.boundedConstructible` predicate and
  `ProEtale.BoundedConstructible` full subcategory. Its additional constant-ring
  presentation is not substituted for the node's module-object category.
- Mathlib `CategoryTheory.Adjunction.Mates`: `mateEquiv` (also the exact recorded
  `mathlib_match` of `det-def-sfb-base-change-morphism-bc`).
- Mathlib `CategoryTheory.Triangulated.Pretriangulated`, `.Functor`, `.Subcategory`:
  `Pretriangulated`, `Functor.IsTriangulated`, `ObjectProperty.IsTriangulated`,
  `Functor.mapTriangle`, and `TriangleMorphism`.
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict`:
  `ObjectProperty.liftFullSubcategoryAdjunction`; its public import includes the
  canonical `liftFullSubcategory` functors and their existing morphism constructions.
- The stated proof dependencies are imported, including the pullback exactness,
  canonical right-derived adjunction shifts, exact-derived composition, and exact
  termwise factorization interfaces. Their proof roles are explained in the two
  theorem docstrings.

Edge cases checked: identity and non-cartesian commutative squares are included;
empty schemes, zero complexes and zero triangles introduce no missing hypothesis;
integer shifts include zero and negative integers. The two category universes are
those already fixed by the recorded pro-etale derived module-object framework. The
restriction theorem admits any full triangulated predicates and uses no stronger
coefficient-class assumption. It requires only the six preservation properties stated
in the node. The square isomorphism is characterized componentwise, so the theorem
does not replace a canonical comparison by an arbitrary unconstrained map.

Searches made, retained in `searches.jsonl`:

- `msearch.py leanfinder`, “Unit square counit derived base change transformation
  commutes with shifts and restricts to preserved full subcategories”: eight generic
  adjunction/shift or square results, none the complete ambient geometric statement.
- `msearch.py loogle`, `CategoryTheory.Adjunction, CategoryTheory.NatTrans.CommShift`:
  four generic adjunction shift interfaces, not this exchange theorem.
- `msearch.py grep`, `baseChange.*[Ss]hift|[Ss]hift.*baseChange|mate.*[Cc]ommShift`:
  zero matches.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the new declaration names and
  exchange/normalization variants, and `grep -rn` for the item id in
  `lean/WeilConjectures`: no existing declaration stating this entire node. Existing
  bounded-constructible exchange definitions are reused through their recorded module.
- API inspection found the existing `liftFullSubcategory` and
  `liftFullSubcategoryAdjunction` helpers, which are used directly; no duplicate
  full-subcategory or adjunction notion is introduced.

Server-source refresh through `scompile.py --source` confirmed that
`Sheaf.Paper.CondensedModuleDerivedPushpull`,
`Sheaf.Paper.BoundedConstructibleBaseChange`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`, and the
canonical right-derived triangulated module have the same relevant declarations as the
read clone (only the source reader's trailing newline differs).

No statement correction, disputed statement, new node, or dependency rebind is needed.

Current validation (2026-10-21 UTC): the prescribed saved-packet dry run now succeeds:
`OK (dry run): commit 886ca60a775 passes the preflight and compiles; nothing pushed`.
The delivery wrapper compiled the complete module, including the explicit
bounded-constructible specialization, against the current live published library and
accepted the server preflight. The timeout and unsupported upstream-repair experiments
below are historical diagnostics, superseded by this successful validation. No upstream
repair candidate is part of this delivery. After the explicit standing-primality
binder repair, `scompile.py` also compiled the final source cleanly in sandbox mode
(36.6 s) and library mode (41.3 s), with no warnings or errors.

The final self-check compared the copied node
with the current repository node (only `lean` differs), verified that `lean.statement`
is the primary signature verbatim, checked all seven recorded declarations, and found
no line exceeding 100 columns. The three postponed proofs are named theorems with proof
and source docstrings; the two instances and two definitions contain real canonical
data. All universes are declared explicitly and `autoImplicit` is disabled. Rechecked
the commutative square orientation, both counits, the canonical compositor and derived
adjunction signatures, the general restriction hypotheses, and the blueprint source
paragraph against the saved statement. Named and explicitly included `hℓPrime` in the
section so Lean retains the standing `Fact ℓ.Prime` binder in the ambient and general
restriction theorems even though their categorical conclusions do not use it. This
repairs only the missing standing hypothesis; the statement's clauses, canonical
constructions, node statement and dependencies are unchanged.

## Second reading by Q40

The dispatcher forbids starting another agent. This is the worker's explicit self-review;
the maintainer's independent reading remains the delivery review. Reopened the node and
module together: the retained attempt omitted both the triangle and general restriction
clauses; both have now been added. Checked the orientation of `leftDerivedUpperStarComp`
and `mateEquiv` against their full signatures, the placement of both counits, all six
preservation directions, and the componentwise restriction of the square comparison.
The first theorem's triangle morphism specifies all three components, so its connecting
square cannot be satisfied by an unrelated triangle morphism.


## Archived timeout diagnostics before the current repair (2026-10-21 UTC)

The initial prescribed dry run found the old attempt had no node JSON. Restored the
current node copy with only its `lean` field changed, completed the triangle and
full-subcategory clauses, repaired the invalid old `include` syntax and the private
shift-instance import, and checked the completed ambient and general restriction
statements in both compiler modes through the prescribed wrapper. Added an explicit
bounded-constructible component equality using the recorded dependency declaration.
The module, node record and report are retained in the sandbox.

The following prescribed checks all fail before worker declarations are elaborated:

1. Full module through `scompile.py`, both before and after the final explicit
   bounded-constructible specialization.
2. `deliver2.py Q40 lem-sfb-derived-exchange-exact-normalization --no-push` with the
   restored node and report: `COMPILE FAILED on the server, nothing pushed`.
3. `scompile.py Q40 lem-sfb-derived-exchange-exact-normalization
   scratchpad/BoundedProbe.lean`, whose complete content is only:

       module
       public import Sheaf.Paper.BoundedConstructibleBaseChange

   This reproduces the same failure with no worker definitions, statements,
   optional proof imports, or additional coefficient imports.

Local wrapper diagnostic:

    overlay WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
    timeout after 60 s: the fault is usually a definition that is expensive to unfold,
    not the limit

The wrapper automatically confirms against current server sources and reports:

    SERVER CONFIRMATION
    WeilConjectures/AlgebraicGeometry/EtaleCohomologyFilteredColimit.lean:
    timeout after 60 s

This is not the `no answer from the compile server` busy-server case. The import
closure compiled many upstream prerequisites successfully before reaching these
specific upstream per-file timeouts. The mandatory dependency itself is mathematically
usable and its source signatures match the current server. Neither timeout comes from
an absent notion, a worker definition, an elaboration error in this module, or a
replaceable optional import. The minimal mandatory-import probe demonstrates that
removing optional proof imports cannot repair it. The failing upstream modules are
outside this item's statement-dependency repair scope and outside the only writable
sandbox; replacing the correct recorded dependency merely to evade its published
import closure would not be an exact interface repair under section 1(B).

No file timeout was raised. No live source or artifact, launcher script, Git state,
or lock was edited, and no direct compiler or global build was run. Delivery was not
pushed because the mandated full-file compilation cannot reach this file. Publication
of usable current upstream artifacts, or an upstream repair of the two timed-out
modules, is needed before the retained final file can complete full validation.


## Upstream definition repair and delivery-tool refusal (2026-10-21 UTC)

The resumed worker first inspected this report and ran the required saved-packet dry
run. It reproduced the timeout in
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity` before the item's
module was elaborated. This timeout is treated as an implementation fault, not as
the reason for stopping.

The diagnostic copies and all logs are in `scratchpad/`. A low-heartbeat profiler
probe located repeated definitional reduction through `cohomologyTriangleMap` in
the cohomology diagram's `map_comp` check. Restricting the three broad `dsimp` calls
to `dsimp only` did not remove the timeout. The candidate actual repair marks the
canonical `cohomologyTriangleMap` definition `@[no_expose]`, retains its exact
construction, and exports `cohomologyTriangleMap_def` through an internal equation
lemma (the same exposure pattern used by the published base-change definition).
Consumers that explicitly unfold the construction instead rewrite by that formula.
The continuity, fixed-base continuity, local-ring colimit, restricted-neighbourhood
colimit and global-sections comparison users have sandbox repair copies. No live
source, Git state, compiler limit or launcher tool was edited.

The repaired definition module and its fixed-base continuity consumer passed
server compilation through `scompile.py`: the definition took 24.3 s in sandbox
mode and 29.9 s in library mode; fixed-base continuity took 14.3 s and 14.0 s.
Sealing the map alone did not resolve the original continuity file's timeout.
A second, scoped low-heartbeat probe reached all five progress markers and located
remaining costly reduction in the elementwise vanishing argument, specifically
cancelling inverse cohomology maps at its `Sheaf.H.map_comp_apply` rewrite. Replacing
that calculation with the existing `Sheaf.H.bijective_map_of_isIso` also still hit
the 60 s limit. These are incomplete candidate source repairs, not a successful
repair or a claim that the final item has passed full validation. The expensive
server-confirmation continuation of this last unsuccessful experiment was stopped
once the independent delivery gate below had been confirmed. There are no remaining
compiler processes from this attempt.

The concrete delivery obstacle is separate from the timeout. Including the needed
upstream source repairs in the sandbox packet and running the prescribed
`deliver2.py Q40 lem-sfb-derived-exchange-exact-normalization --no-push` returns,
before compilation or preflight:

    FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/AlgebraicGeometry/CofilteredFixedBaseCohomologyContinuity.lean

The complete refusal is retained in `scratchpad/upstream-delivery-gate.log`.
The required canonical imports point to those upstream module names. Moving an
identically named construction to a `Sheaf` module does not change their import
closure; importing it together with the upstream definition would duplicate the
notion. Removing the canonical dependency imports would violate the statement
contract. The delivery tool supplies no supported upstream-source-patch channel,
and the human explicitly forbids patching a launcher gate. The source repairs
are retained under both `scratchpad/lean/WeilConjectures/` and the sandbox packet's
`lean/WeilConjectures/` for review. Nothing has been pushed.


Current handoff: the reason for BLOCKED is the delivery tool's explicit refusal
of required upstream module paths, not either timeout. Enabling a supported
maintenance source-patch channel is required before this repair can be delivered.
The full item has not compiled or passed preflight; no commit was pushed. The
original item module and node record were retained unchanged during this repair
attempt. Candidate upstream sources in the sandbox are clearly separate by path.

## Saved-packet retry (2026-10-21 UTC)

Started with the required saved-packet dry run. It again failed immediately with:

    FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/AlgebraicGeometry/CofilteredFixedBaseCohomologyContinuity.lean

Preserved the incomplete upstream candidate packet by moving its `lean/WeilConjectures`
directory into `scratchpad/RetainedUpstreamPacket`; no candidate source was deleted.
The delivery source tree now contains only the item's original Sheaf module. Retried
`deliver2.py Q40 lem-sfb-derived-exchange-exact-normalization --no-push` on that packet.
It reached the compiler, reproduced the local overlay timeout in
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`, performed its normal
current-server confirmation, and exited 1 with:

    COMPILE FAILED on the server, nothing pushed:
    WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean: timeout after 60 s

Thus the current live source still does not validate the required import closure;
archiving the unsupported repair paths resolves the packet-layout diagnostic but does
not resolve compilation. Inspected the current required base-change dependency,
its pushforward-restriction dependency, and the upstream BoundedConstructible module:
they still require the same upstream import closure. Replacing those canonical
interfaces with copied declarations would not be an authorized interface repair.
The saved candidate patches remain incomplete and are not asserted to fix this failure.
No launcher script, timeout, live repository file, or Git state was changed directly.

Self-check: comparing the node copy with the current read clone finds only `lean`
changed; its recorded primary signature matches the source verbatim; no Lean source
line exceeds 100 columns. The source and node record themselves were retained unchanged.
No delivery was pushed. The actual delivery-tool path refusal above still prevents
submitting upstream source repairs through this worker's prescribed delivery channel;
a supported upstream maintenance channel is needed for that work.


## Current dispatcher retry (2026-10-21 06:03 UTC)

Inspected the saved report and began with the prescribed saved-packet dry run,
without changing the item source or node. It again reported the local overlay
timeout in `WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity`, then
confirmed against current server sources and exited 1 with:

    COMPILE FAILED on the server, nothing pushed:
    WeilConjectures/AlgebraicGeometry/Sites/CohomologyContinuity.lean: timeout after 60 s

Re-read all nine statement-dependency node statements and current records, the
recorded derived pushpull and base-change modules, the compositor and adjunction
signatures, and the blueprint source paragraph. The required canonical
bounded-constructible dependency still imports the upstream closure that fails.
The saved packet changes only the item's `lean` field; the primary signature is
verbatim, all seven declarations are recorded, and all lines meet the 100-column
limit. This source check does not claim full compilation: the required dependency
fails before the item's declarations can be checked.

To test the concrete previously reported delivery-tool obstacle, temporarily
restored the retained upstream candidate directory to `lean/WeilConjectures`
inside this sandbox and ran the same prescribed `deliver2.py --no-push`. It
again exited 1 immediately, before compilation, with:

    FAILED: a module must be under lean/Sheaf/<Topic>/, not lean/WeilConjectures/AlgebraicGeometry/CofilteredFixedBaseCohomologyContinuity.lean

Restored that directory to `scratchpad/RetainedUpstreamPacket` afterwards; all
candidates remain preserved and are still incomplete, as the earlier report
explains. The delivery tree contains only the original Sheaf statement module.
No live repository source, launcher script, compiler limit, or Git state was
directly changed, and nothing was pushed. The BLOCKED reason is the reproduced
explicit delivery-tool path refusal, which prevents submitting upstream source
repairs via the worker's only authorized delivery channel.
