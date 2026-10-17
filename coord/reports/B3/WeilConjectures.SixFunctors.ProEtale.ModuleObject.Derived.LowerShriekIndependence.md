## What changed

The three target theorems in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence`
remain unchanged in signature and are proved as in the retained delivery.

The returned duplicate declarations were consolidated into the existing proof-support module
`Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono`.
That module now contains one private proposition-valued abbreviation for each shared support
proof, with unique names `sharedBoundedOpenUnitIsIso`, `sharedOpenRestrictionPushforwardZero`,
`sharedPullbackExtensionZero`, `sharedDerivedPullbackExtensionZero`, `sharedModuleJointZero`,
`sharedModuleJointIso`, and `sharedDerivedModuleJointIso`.  The target module imports that
module with `import all` and uses these declarations; its duplicate local theorem copies were
removed.  The support module adds the proof-only `Open.Complement` import needed by
`sharedOpenRestrictionPushforwardZero`.  `ShriekComposition` is unchanged, retaining its
existing private theorem names and proofs.

The direct `Open.Complement` import was removed from the target module after compilation showed
that the shared support import supplies it.  The direct fully-faithful helper import is retained
because the target's complement argument uses `Adjunction.isIso_map_unit_app_obj`.

## Proved and sorry left

Closed all three original holes (3 of 3):

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekRefinement`;
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward`;
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl`.

Zero `sorry`s remain in the item module.  No new `sorry`, split-off theorem, axiom, definition,
or target statement was added.

## No longer needed

No DAG node is pruned.  The duplicate local support declarations in the target module are no longer needed; the
target's proof uses the single shared abbreviations in `ExchangeMono`.  The target module's
direct import of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement` was removed
because the shared support module imports it.  No other original import was removed.

## Where the brief, the DAG or earlier work was wrong

The retained delivery independently reproduced seven support propositions already present in
`ShriekComposition`.  The landing check correctly rejected those word-for-word duplicates, but
the import graph made importing `ShriekComposition` from the target impossible: it imports the
target through `BaseChangeTheorems.LowerShriek.MorphismDefs`.  The correct repair is to place the
shared support API in the lower-level `ExchangeMono` module, which both consumers can import
without a cycle.  All three target statements and the unit route are unchanged.

## Forced adaptations

The returned landing error was:

`tools/import_prune_check.py refused ... LowerShriekIndependence: ... proves statements that the
library already states word for word`, listing the seven support declarations and their copies in
`ShriekComposition`.

The forced changes are:

- `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono`
  (current holder: unclaimed): added seven private proposition-valued abbreviations carrying
  the shared support proofs and its proof-only `Open.Complement` import.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence`
  (item module): removed its seven duplicate private theorem declarations, switched their uses
  to the shared abbreviations, and removed the now-redundant direct `Open.Complement` import.

`ShriekComposition` is not adapted; its existing theorem declarations remain unchanged.  These
changes leave all public signatures and mathematical statements unchanged.

Change record: `coord/changes/lower-shriek-support-deduplication.md`.

## Earlier second reading (a previous round; superseded)

The item module, the shared `ExchangeMono` support module, and the import graph were recompiled
with `lcompile.py --all`; all three compile with no errors or warnings.  The three target
signatures are unchanged, the old `ShriekComposition` declarations remain intact, and the target
now resolves each support proof from the single imported shared abbreviation.  No `sorry`, axiom,
unsafe declaration, or hollow definition was introduced.

## Second reading by B3

1. **Declarations and signatures.** I compared the delivered target module with the repository
   version. Every existing public declaration, including all three repaired theorem signatures and
   both compactification isomorphism definitions, is byte-for-byte unchanged in its declaration
   type. The only added target declarations are the two private proof helpers required by the
   proper-base-change argument. The support-module adaptation adds only private, proposition-valued
   proof abbreviations and a proof-only import.

2. **Proof and trust basis.** I compiled all three sandbox modules with
   `lcompile.py --all`; they compile without errors or warnings. The delivered Lean files contain
   no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and no definition uses
   `sorry`. The three original holes are closed by the stated comparison, complement, and proper
   base-change arguments. The private helper declarations are ordinary theorems with no postponed
   proof obligations.

3. **Statements and support declarations.** No statement was split off and no target statement was
   weakened or strengthened. The shared support abbreviations are used only to avoid repeating
   already-proved propositions across the import closure; their types are exactly the propositions
   needed by the target proof. They are private proof support, so no new public API or DAG node is
   required. The existing `ShriekComposition` declarations remain unchanged.

4. **Route, imports, and pruning.** The proof follows the unit route: restriction comparison,
   proper pushforward comparison via the closed complement and proper base change, then refinement
   and common-refinement isomorphisms. `BaseChangeTheorems.Proper` and the fully-faithful
   adjunction helper are proof-only imports; `ExchangeMono` is imported with `import all` solely
   for its private proof support. The direct complement import is supplied by that support module,
   so no additional target import is needed. No old DAG node or stated proof dependency is unused.

5. **DAG and change records.** The target nodes and their proof dependencies agree with the proof,
   and the unit's route is unchanged. The required adaptation is recorded in
   `coord/changes/lower-shriek-support-deduplication.md`, which lists the affected modules and
   explains why the lower-level support module is necessary to avoid the import cycle. The change
   record remains open for landing verification.

I changed only the two target proof bodies, added their two private intermediate lemmas, moved the
shared proof support into `ExchangeMono`, added its proof-only complement import, and added the
proof-only imports needed by the target. No mathematical statement, target definition, or existing
public signature was changed.
