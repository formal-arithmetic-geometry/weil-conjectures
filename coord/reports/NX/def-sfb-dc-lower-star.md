## Worker report

The retained module `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructibleLowerStar`
now defines `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerStarAtMorphism`,
its `boundedConstructibleLowerStarAtMorphismCompatibility`, and the canonical comparison
`boundedConstructibleLowerStarAtMorphismGlobalIso`. All three have real definition data;
there are no new theorems, axioms or sorries. Only the item's `lean` record changes.

## Repair of return L (immutable head a8c3b9f43f59)

The returned packet redeclared two names owned by the already published module
`Sheaf.Paper.BoundedConstructiblePushforwardRestriction`:
`boundedConstructibleLowerStarOfPreserves` and
`boundedConstructibleLowerStarOfPreservesCompatibility`.
The required initial dry run of the saved packet passed at a5e0f1b0b7, but does not
invalidate the independent reader's collision finding. I opened the existing module
locally and through `scompile.py --source`; the published sources agree.
Neither existing name is now declared in this delivery. That module is publicly
imported, and both its declarations are used by the new canonical `GlobalIso`.

The return permits different names only for genuinely different statements. Here
that condition matters: the existing declarations take
`H : PreservesBoundedConstructiblePushforwards Λ k`, which quantifies over ALL
separated finite-type schemes X,Y over k and ALL their morphisms f. This node and
its cited blueprint instead fix ONE f and assume only that its Rf_* preserves
bounded constructible complexes. Our `h` has exactly that local scope. Rebinding
the node to the existing global declaration would add an assumption.

Concrete distinction: for k algebraically closed of characteristic p and the
constant discrete condensed ring F_p, the identity morphism preserves bounded
constructibility. Global H fails for these same coefficients: the morphism
A1_k → Spec k has infinite H1 by Artin--Schreier, the counterexample recorded in
`lem-sfb-dc-lower-star-preserves`. Thus this is not a cosmetic rename of an exact
existing declaration. The new name says `AtMorphism` to expose the weaker hypothesis.
The local restriction reuses Mathlib's existing `ObjectProperty.lift`; the new
`GlobalIso` reuses the existing GLOBAL restriction and its compatibility via the
fully faithful inclusion. It canonically identifies the interfaces for any h,H
when both are available. No second global-preservation construction is introduced.

The global module belongs to the parent unit `sk-def-sfb-dc-restricted-functors`;
that unit lists this node as a proof dependency. Accordingly it must not later
import this module back as a proof-only import: that would close an import cycle.
The present import graph is acyclic and compiles. No backwards DAG edge to the
parent unit is added. The current recorded module of the direct statement
dependency `sk-def-sfb-module-derived-pushpull` is also imported and its named
`moduleObjectDerivedPushforward` is used throughout (definitionally the same Rf_*).

## Correspondence with the node

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Positive characteristic p distinct from ell: `{k : Type u} [Field k]`
  `[Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`.
- Separated finite-type k-schemes: `{X Y : Over (Spec (.of k))}`, with
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]`,
  and the same three instances on Y.hom. `(f : X ⟶ Y)` is over k.
- Arbitrary commutative condensed ring: `(Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]`. No coefficient-finiteness class is assumed.
- Pulled-back coefficients are the existing `condensedRingObj Λ X.left` and its Y
  counterpart, giving internal module objects, not ordinary constant-ring modules.
- Ambient Rf_* is exactly the recorded dependency's `moduleObjectDerivedPushforward
  Λ f.left`; its real body is `(lowerStar Λ f.left).rightDerivedFunctor`, the total
  derived functor of the entire underived module-object composite.
- Preservation for this f: `h : ∀ K : DerivedCategory (Mod ...),
  boundedConstructible ... K → boundedConstructible ...
  ((moduleObjectDerivedPushforward Λ f.left).obj K)`. It does not quantify over f.
- The source and target are the dependency's `BoundedConstructible
  (condensedRingObj Λ X.left)` and its Y counterpart.
- Restriction is `(boundedConstructible ...).lift ((boundedConstructible ...).ι ⋙
  moduleObjectDerivedPushforward Λ f.left) (fun K ↦ h K.obj K.property)`.
  Objects and morphisms are the ambient images, with the preservation proof on objects.
- Commuting with inclusions is `boundedConstructibleLowerStarAtMorphismCompatibility`:
  the canonical `ObjectProperty.liftCompιIso`, with identity data.
- The O_E, E and Qlbar examples use the already stated
  `boundedConstructible_rightDerivedLowerStar_obj Λ ℓ f` under
  `[IsFinitenessCoefficient ℓ Λ]`. This supplies h; it is not an extra assumption
  on the definition. The dependency now also covers finite torsion coefficients.
- `GlobalIso` is auxiliary comparison data, from the two inclusion comparisons
  using `((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso`.
  The additional H belongs only to this comparison, never to the main definition.

## Dependencies read and used

- `sk-def-sfb-dc-setting`: recorded module
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
  `ProEtale.BoundedConstructible` and `ProEtale.boundedConstructible` give the full
  bounded-constructible subcategory, imported publicly through the global module.
  Its `CondensedRing.compactificationOverField` is not needed for lower-star.
  The current server source was read: it uses Over-scheme geometry and no
  compactification hypothesis is imposed on this definition.
- `sk-def-sfb-module-derived-pushpull`: recorded module
  `Sheaf.Paper.CondensedModuleDerivedPushpull` and its full signature and body for
  `CondensedRing.moduleObjectDerivedPushforward`. It publicly imports the same
  `CondensedRing.derivedUpperStarLowerStarAdjunction` of the total derived functors.
- `lem-sfb-dc-lower-star-preserves`: current recorded declaration
  `CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`, in the first
  module above, with `[IsFinitenessCoefficient ℓ Λ]` and the same Over-scheme setting.
  The published signature and docstring were read through `scompile.py --source`.
- Mathlib `CategoryTheory.ObjectProperty.lift`, `liftCompιIso`, and
  `fullyFaithfulι` in `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`
  are the generic constructions used; the definitions and docstrings were read.
- Existing global restriction and compatibility: full source and docstrings of
  `Sheaf.Paper.BoundedConstructiblePushforwardRestriction` were read both locally
  and from the published source, including the universally quantified H predicate.

## Searches and edge cases

The retained search log `searches.jsonl` records the original service searches:
LeanFinder, "derived pushforward restricted to bounded constructible complexes
assuming preservation of constructibility"; LeanSearch, "restriction of derived
pushforward to bounded constructible modules with an explicit preservation
hypothesis"; Loogle, `"liftCompιIso"`; and grep in `CategoryTheory/ObjectProperty`
for `boundedConstructible.*LowerStar|lowerStar.*boundedConstructible|def lift|def liftCompιIso`.
They found general full-subcategory lifts and underived pushforwards, not the local
pro-etale internal-module interface. The record's source searches covered both
read-only slopmaster2 `WeilConjectures` and the project's `lean/Sheaf` by node id
and bounded-constructible lower-star names. The coefficient-specialized framework
restriction requires IsFinitenessCoefficient, so cannot encode arbitrary Λ with h.

For this repair, rg over project `lean/Sheaf`, slopmaster2 `WeilConjectures`, and
`dag/lean_names_upstream.json` located the exact two returned name collisions in
`Sheaf.Paper.BoundedConstructiblePushforwardRestriction` and downstream uses in
`Sheaf.Paper.BoundedConstructibleBaseChange`. The first source was read in full;
its H is genuinely global. Searches for the new AtMorphism names found none.
The main-20261015 node source and its whole parent unit were reread: preservation
is conditional, and restriction is the ambient functor with its inclusion comparison.

Edge cases: zero complexes; empty schemes when a morphism exists; identity f for
arbitrary Λ (in particular F_p outside the global-preservation coefficients); and
an arbitrary ring outside IsFinitenessCoefficient with a given local h. No
nonemptiness, properness, global preservation, or coefficient-finiteness condition
is added. All universes and binders are explicit, with autoImplicit false.
No statement correction, new node, dependency repair or STATEMENT-DISPUTED issue.

The maintainer supplies the independent reading under the current direct-worker
policy. This report does not assert an independent second reading.

## Retained historical maintenance evidence

The following stage-1 recovery and validation entries are preserved verbatim.
They concern route metadata, not the stage-2 compiler validation.

## Maintenance recovery for the next Q51 worker and second reader (2026-10-16)

The historical missing chapter/unit return is repaired on the authoritative
server: live be148130e20df307acc3a28209581384702f1fd4, side
30002d787829c936450ebabf0918ee2d1720634c. Both server commits contain the exact
requested chapter sec-six-functors-basics, unit sk-def-sfb-dc-restricted-functors,
and their source records. The prior mathematical/citation review passed.
Keep the retained definition; no mathematical change is required for this return.

The ordinary delivery command can queue for several minutes behind another Q51
stage-1 or stage-2 delivery, worktree capacity or a shared fetch. Let it reach
its actual exit and preflight result. Earlier 60-second interruptions were not
failed preflights. The 60-second single-file Lean limit does not limit stage-1
delivery. Maintenance observed the group lock change owners normally; it did
not establish a stale lock. Never kill another worker or delete an active lock.

The deployed item route note informs future writing/repair attempts. Second
readers receive this recovery through report.md, which their brief requires
reading. Server handoff: coord/reports/maintenance/Q51-dc-lower-star.md,
maintenance commit 0802b74697b8d80e7f933d1092c8cc9aa5b78117. Ordinary no-push
validation is in progress; the final maintenance report will record its outcome.

## Accepted repair dry run (2026-10-16)

After the retained sandbox item was verified to contain `chapter: sec-six-functors-basics` and `unit: sk-def-sfb-dc-restricted-functors`, I reran the exact required command:
`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q51 def-sfb-dc-lower-star --no-push`.
It completed successfully and printed `OK (not pushed) deliver/Q51/def-sfb-dc-lower-star at 83fc6199c8: preflight passed`. This supersedes the earlier resource-wait observations. No repository, live source, launcher file, compiler, or Lean file was modified, and nothing was pushed.


## Maintenance ordinary validation passed (2026-10-16)

The active worker's exact required ordinary command completed successfully:

    python3 /home/ubuntu/weil-launcher-nt/deliver.py Q51 def-sfb-dc-lower-star --no-push
    OK (not pushed) deliver/Q51/def-sfb-dc-lower-star at 83fc6199c8: preflight passed

The launcher log reports a successful exit after 544113 ms. Full temporary
candidate: 83fc6199c8c61f27de27eb758c59d34fcd11b0de. Maintenance read that
candidate and verified its correct chapter/unit and both source records before
preflight ended. No mathematical fields differ from the reviewed f1cd301618
packet. Continue the ordinary second reading and delivery. Maintenance did not
push this item or alter failure counts. It stopped only its own still-queued
duplicate validation (PID 2408243) after the worker's successful result was
available; that intentional duplicate cancellation is not a failed preflight.
Evidence: the maintenance directory's evidence/ordinary-worker-preflight.txt.


## Historical stage-2 validation (superseded by the repair below)

The first scompile.py run diagnosed a missing CategoryTheory.Obj scope, needed for
the strong-monoidal functor to transport the coefficient ring-object structure.
Adding the same scoped instances used by the upstream framework fixed the error.
The final scompile.py invocation compiled both the sandbox and module-path probes
with exit 0, no warnings and no errors (3.7 s and 24.8 s respectively). The source
contains two definitions and no sorry. A local record check confirms that the node
differs only in lean, the main signature is verbatim, and all Lean lines are at most
100 characters. No direct or global build was run.

The worker delivers directly under the 2026-10-17 launcher policy; the maintainer
performs the independent review. No worker second reading is asserted here.

The first stage-2 packaging preflight reported only that its signature reader starts
at `def`, excluding the `noncomputable` modifier. The record was adjusted to start
at `def` verbatim, matching that reader; the Lean module and mathematics did not change.

The repaired dry run completed with exit 0:

    OK (dry run): commit ddc1816cce passes the preflight and compiles; nothing pushed

This is the stage-2 validation for the present NX module; the historical Q51
entries above remain preserved as the route-metadata recovery evidence.


## Repair validation (2026-10-18)

The initial required saved-packet dry run passed at a5e0f1b0b7. The independent
return was then repaired substantively as described above; it was not an unchanged
re-push. The first repair compilation found only four overlong-line warnings;
all four were wrapped. The final scompile.py run compiled the sandbox and exact
library-path versions with exit 0, no errors and no warnings (2.4 and 2.5 s).
Importing the existing global module in this same compilation checks that the
returned duplicate-declaration problem is gone and both existing declarations
are usable alongside all three local declarations.

The repaired dry run completed with exit 0:

    OK (dry run): commit 3d45885909 passes the preflight and compiles; nothing pushed

Self-check: compared the complete retained node against the current shared node;
only lean differs. Its recorded statement is copied verbatim from def through
the signature before :=. All universes and variables are bound explicitly;
all Lean lines have at most 100 characters. Both original names occur only as
uses of imported declarations. There are no theorem proofs or sorry terms.
The wrapper constructs the delivery on the current authoritative base; no
read-only checkout, upstream source, launcher script or git state was edited
by this worker. The historical maintenance entries above are retained intact.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
