# AlgebraicGeometry.mixedPullbackSquareComparison_tensor

## Reason

Restore the assigned quarantined module at its original Sheaf import path. The archived
file has zero holes but fails to compile against the current public API at line 31:

```text
failed to set `[local irreducible]`, `derivedPullback` is currently `[irreducible]`
```

The complete adopted source implementation already provides both public declarations.
Every declaration, docstring and proof from mixedPullbackSquareComparison onward is
byte-identical between the archive and the adopted source. Re-export the source instead
of replaying the obsolete local reducibility command or declaring duplicate constants.
This restores the missing module and its complete mathematics; it is neither a withdrawal
nor a no-op. The quarantine archive and all source-library files remain unchanged.

## Old

The quarantined module publicly imports MixedHomTensorPullbackIso,
DerivedPullbackComposition and Mathlib.AlgebraicGeometry.Pullbacks, privately imports
DerivedPullbackCompositionTensorKFlat, and redeclares the following comparison and theorem
in namespace AlgebraicGeometry. Universes are u w, with the unchanged section assumption:

```lean
[∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
```

```lean
def mixedPullbackSquareComparison
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    derivedPullback g ⋙ derivedPullback (pullback.snd f g) ≅
      derivedPullback f ⋙ derivedPullback (pullback.fst f g) :=
  let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
      derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
    fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) a b
  c (pullback.snd f g) g ≪≫
    eqToIso (congrArg (fun k : pullback f g ⟶ Y => derivedPullback k)
      pullback.condition.symm) ≪≫ (c (pullback.fst f g) f).symm

theorem mixedPullbackSquareComparison_tensor
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (P Q : schemeDerivedCategory Y) :
    (derivedPullback (pullback.snd f g)).map
        ((mixedHomTensorPullbackIso g).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.snd f g)).hom.app
        ((derivedPullback g).obj P, (derivedPullback g).obj Q) ≫
      ((mixedPullbackSquareComparison f g).hom.app P ⊗ₘ
        (mixedPullbackSquareComparison f g).hom.app Q) =
    (mixedPullbackSquareComparison f g).hom.app (P ⊗ Q) ≫
      (derivedPullback (pullback.fst f g)).map
        ((mixedHomTensorPullbackIso f).hom.app (P, Q)) ≫
      (mixedHomTensorPullbackIso (pullback.fst f g)).hom.app
        ((derivedPullback f).obj P, (derivedPullback f).obj Q)
```

The theorem already has a complete proof using K-flat coordinates, composition/tensor
compatibility, naturality, inversion, composition and equality transport. The archived
local irreducibility command additionally names derivedPullback, now an irreducible_def.

## New

The restored module is a public compatibility import of
WeilConjectures.AlgebraicGeometry.MixedPullbackSquareTensorCoherence. That source module
has the exact definition body and theorem signature displayed above, and the exact
complete proof and private helpers from the archive. No declaration is renamed or
removed from the library. Their universes, section assumptions and visibility agree.
The obsolete local command is not replayed. No source-library file is edited.
The node's lean attachment identifies the actual source declaration, while its statement,
statement dependencies, proof, proof dependencies, proof origin and unit route are retained.

A compiled consumer imports only the restored public path for the statement API (its
additional imports exercise coexistence with the old dependencies and adopted downstream
parent). It proves the archived comparison formula by rfl and applies the theorem at its
verbatim archived signature. It coimports both source and Sheaf square modules, the
adopted MixedTensorPairingBaseChangeTransport consumer, and the three old Sheaf dependency
paths. The consumer and wrapper compile without errors or warnings. Both public
constants have exactly [propext, Classical.choice, Quot.sound] in #print axioms.
Zero objects, identity arrows and empty schemes are included in the unchanged universal
statement; no assumptions or normalization choices change.

## Users

The tools/downstream.py scan with --allow-missing finds zero live importers of the absent
Sheaf path and zero textual users through that path. This is not used to withdraw the
item: its DAG parent lem-sc-mixed-tensor-pairing-base-change-identity still needs it.
A separate quarantine scan finds only the item itself. The adopted source module has
the nine downstream modules listed below. No consumer adaptation is needed because the
restoration re-exports the identical existing constants. Current holders are recorded
from coord/claims; no other module is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.MixedPullbackSquareTensorCoherence | B2 | Restore the public import path with identical source constants. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | unclaimed | Source declarations unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | unclaimed | Source declarations unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange | unclaimed | Source declarations unchanged; no adaptation. |
| WeilConjectures | unclaimed | Source declarations unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.MixedGlobalHomBaseChangeCounitTransport | unclaimed | Source declarations unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.MixedGlobalHomBaseChangeExchange | unclaimed | Source declarations unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.MixedInternalHomBaseChangeExchange | unclaimed | Source declarations unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.MixedTensorPairingBaseChange | unclaimed | Source declarations unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.MixedTensorPairingBaseChangeTransport | unclaimed | Source declarations unchanged; no adaptation. |

No target statement, definition meaning or unit step changes. The statement-review
criterion for every target is preserved. No forced adaptations are delivered.

## Status

landed 20261022T022942-L-765954 2026-10-22 (merge of deliver/B2/Sheaf.AlgebraicGeometry.MixedPullbackSquareTensorCoherence)
