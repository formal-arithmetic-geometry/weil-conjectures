## What changed

Partial repair of Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap: construct
AlgebraicGeometry.affineDerivedExtension as extendScalars.leftDerivedFunctor and
AlgebraicGeometry.affineDerivedExtensionAdjunction by deriving the specified
extendRestrictScalarsAdj and transporting exact restriction through its unit-compatible
comparison. No arbitrary scalar-adjunction witness is selected. The existence theorem
retains its signature and now follows from these concrete definitions.

The second reader removed the first worker's CommRingCat-specific preservation theorem
and its duplicated tensor calculation. The new module ExtensionKFlatQuasiIso instead
exports ModuleCat.extendScalars_preservesKFlatQuasiIso by reusing the existing private
CochainComplex.scalarExtension_quasiIso_of_kFlat proof in KFlatScalarExtensionDerivedIso.
All existing declaration signatures are unchanged; only the two scalar definitions and
the scalar existence proof change bodies. Keep the original theorem ordering, docstrings
and target-local transparency settings except for the construction docstrings that must
now describe the repaired definitions. The latter settings keep expensive scalar-derived
machinery out of unrelated proof search.

The required preservation import is public: Lean rejects a private import in these exposed
definition bodies. The new module's proof machinery remains privately imported. Remove
three redundant direct imports whose public paths are retained, as listed below.
Forced adaptations preserve the reported importer universe and supply the coherence
theorem with its needed local elaboration budget; their signatures and proof bodies stay
unchanged apart from the importer universe annotation.
Change record: coord/changes/affine-derived-extension-canonical-adjunction-Q1.md.

## Proved and sorry left

Holes closed: none. The assigned module has zero local sorries on the current baseline.
Holes added: none. No delivered declaration contains sorry and no statement is split off.
ModuleCat.extendScalars_preservesKFlatQuasiIso is proved, with node
lem-pc-extension-kflat-quasi-iso. The existing
AlgebraicGeometry.exists_affineDerivedExtension,
AlgebraicGeometry.exists_canonicalTensorHomAdjunction and
AlgebraicGeometry.exists_globalHomPullbackComparison remain proved.

Scratch #print axioms checks for all 16 declarations of the item and the new preservation
theorem show only propext, Classical.choice and Quot.sound, with no sorryAx.
This is a concrete-data repair, not a net reduction of proof holes. The inherited
canonicalPullbackAdjunction class-2 issue remains open; this delivery does not claim to
repair its shared composition-counit normalization.

## No longer needed

Remove these redundant direct imports:
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory:
  publicly re-exported by the retained DerivedCategory.Adjunction import.
- Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison:
  publicly re-exported by CanonicalDerivedTensorHom through CanonicalDerivedTensorHomModel.
- WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution:
  publicly re-exported by GlobalDerivedHom through DerivedInternalHom.

The first worker's additional LeftDerivedFunctor.Defs direct import is unnecessary because
DerivedCategory.Adjunction already publicly imports it. The duplicate local theorem and
its direct MixedTensorKFlatQuasiIso import are removed. The new preservation wrapper
reuses the mixed-tensor proof already in KFlatScalarExtensionDerivedIso.

The old direct proof dependency lem-pc-mixed-tensor-kflat-quasi-iso is replaced in this
module by lem-pc-extension-kflat-quasi-iso; mixed tensor remains transitively used by the
new property module. No old dependency becomes unnecessary to the entire proof route.
No module becomes unreachable; modules pruned: none. No blueprint unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

This is a zero-local-sorry repair item. S3's canonical scalar repair was present at the
start of the second reading, but reverted during it after the global build found a universe
error in ProperFlatImageGlobalHomBaseChangeIso. The repaired scalar construction must
therefore be delivered again against the reverted baseline. The second reading explicitly
reproduced that original importer error against the delivered overlay.

The remaining canonicalPullbackAdjunction uses the counit existentially supplied by
exists_derivedPullbackComposition. Its fix requires coordinated changes with
schemeHomPullbackAdjunction and the composition/model-unit equations, including
AffinePullbackSectionsUnitUncancelled.pinned_unit_fac and
DerivedPushforwardSquareMateUnit.canonical_adjoint_eq. This partial delivery keeps the
existing REPAIR marker for that issue and introduces no new arbitrary existential data.

## Second reading by Q1

1. Signatures and data: compared all modules against the current repository. The item
   retains every existing signature byte for byte, including the original instance
   parameters. Only affineDerivedExtension, affineDerivedExtensionAdjunction and
   exists_affineDerivedExtension change bodies; all other declaration bodies match.
   The two data changes are recorded explicitly and reopen affected target semantic
   reviews under AGENTS.md section 4. No target text or conclusion changes.
2. Proof and trust: the item and new property module compile cleanly via lcompile.py.
   All 17 public declarations checked by scratch #print axioms use only the three
   allowed axioms. There is no local sorry, axiom, unsafe, opaque, implemented_by or
   extern, and no definition chooses arbitrary scalar data from a mere existence
   theorem. The inherited pullback-counit repair remains explicitly open.
3. Split statements: none. The proved preservation theorem is valid for zero rings,
   zero complexes, identity maps and non-flat ring maps because mixed tensor with the
   target ring in degree zero needs no flatness premise. Local rg searches with both
   scalarExtension and extendScalars found the exact private proof; it is reused through
   import all in a theorem proof, and no private helper appears in exposed definition
   data. LeanFinder returned module flatness results, Loogle returned no match, and
   LeanSearch was unavailable (recorded as unavailable); none replaces the K-flat result.
   A whole-blueprint search for extension of scalars returned three unrelated nodes,
   with no exact imported blueprint statement.
4. Route and pruning: checked the naturality specialization and mkOfHomEquiv counit
   identity for tensor-Hom, the evaluation mate and all eight comparison equations.
   Preserve the shortest existing tensor proof via a named property module; the scalar
   existence proof now uses the concrete definitions. The old mixed-tensor dependency
   remains transitively needed, so no module pruning is claimed. The unit record is
   dag/units/sk-thm-picard-duality.json; its realized lists are empty on the repository
   baseline. No unit statement, step or realized record is changed. Three redundant
   direct imports are removed using the public paths above.
5. DAG agreement: the existing node's proof and proof_deps now name the preservation
   wrapper and the fixed scalar construction. Its lean signatures/declaration names
   remain unchanged; proof_origin and the lean note describe this partial repair.
   The new node records the actual preservation theorem, source, complete proof,
   dependencies, searches and edge cases. The first worker's duplicate declaration
   entry is removed.

Changes by the second reader: reuse the existing private preservation proof through its
own public module and node; restore minimal scalar-existence proof, declaration ordering
and target-local options; remove redundant imports; correct the DAG and report; repair the reported importer with one explicit sheaf-module universe annotation; add
the necessary theorem-local coherence heartbeat setting and its explanatory comment.

## New nodes

lem-pc-extension-kflat-quasi-iso exposes the existing scalarExtension_quasiIso_of_kFlat
argument as the Prop-valued class needed by leftDerivedFunctor. It is proved and introduces
no hole. It is strictly smaller than the affine global-Hom construction and reuses a library
proof, with no flatness or boundedness assumption. Module:
lean/Sheaf/Algebra/Homology/ExtensionKFlatQuasiIso.lean.
Change record: coord/changes/affine-derived-extension-canonical-adjunction-Q1.md.

## Forced adaptations

Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso (unclaimed): the unchanged
original compiles against the compiled baseline in 18.8 seconds. Against this delivery's
.lbuild overlay it fails at line 194 with `failed to solve universe constraint`, trying to
unify `Category.{u + 1, u + 1} AddCommGrpCat` with
`Category.{u, u + 1} AddCommGrpCat`; line 198 then reports `No goals to be solved`.

The only adapted token is `SheafOfModules.overFunctor` changed to
`SheafOfModules.overFunctor.{u}` in the local hP proof. It fixes the sheaf-module universe
of the exact restriction functor, already determined by hP's goal and the theorem's
existing parameters. All existing signatures, visibility, mathematical statements,
imports, options and other proof text stay byte for byte. The adapted file compiles against
the overlay in 19.2 seconds. No theorem is weakened and no additional hypothesis is added.

Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence (unclaimed): its original
compiles against the baseline in 40.4 seconds. Against the delivered overlay it reaches
the deterministic 200000-heartbeat limit at the theorem's signature (whnf, line 31),
exiting with a compiler error after 21.9 seconds. Add only
`set_option maxHeartbeats 800000 in` immediately before that theorem's docstring and a
comment explaining the signature-elaboration cost. The declaration's signature and proof
body remain byte-identical. With that setting it compiles in 37.8 seconds, within the
single-file time limit; the comment removes the maxHeartbeats style warning. This is an
elaboration-budget adaptation, with no change of statement, definition or logical trust.

## Forced adaptations

### Sheaf.AlgebraicGeometry.AffineSectionsSquareComparisonCoherence
Original against changed dependencies failed:
```
/tmp/forced-adaptation-uq_0kxh5/lean/Sheaf/AlgebraicGeometry/AffineSectionsSquareComparisonCoherence.lean:31:0: error: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.

(with the modules compiled into /tmp/forced-adaptation-uq_0kxh5/.lbuild) [22.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

### Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso
Original against changed dependencies failed:
```
/tmp/forced-adaptation-uhss0499/lean/Sheaf/AlgebraicGeometry/ProperFlatImageGlobalHomBaseChangeIso.lean:194:12: error: failed to solve universe constraint
  ?u.579 + 1 =?= u
while trying to unify
  Category.{?u.579 + 1, u + 1} AddCommGrpCat : Type (max (u + 1) (?u.579 + 2))
with
  Category.{u, u + 1} AddCommGrpCat : Type (u + 1)
/tmp/forced-adaptation-uhss0499/lean/Sheaf/AlgebraicGeometry/ProperFlatImageGlobalHomBaseChangeIso.lean:194:12: error: failed to solve universe constraint
  u + 1 =?= u
while trying to unify
  Category.{u + 1, u + 1} AddCommGrpCat : Type (u + 2)
with
  Category.{u, u + 1} AddCommGrpCat : Type (u + 1)
/tmp/forced-adaptation-uhss0499/lean/Sheaf/AlgebraicGeometry/ProperFlatImageGlobalHomBaseChangeIso.lean:198:4: error: No goals to be solved

(with the modules compiled into /tmp/forced-adaptation-uhss0499/.lbuild) [11.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
