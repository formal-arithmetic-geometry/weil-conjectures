# AlgebraicGeometry.schemeGlobalHom_baseChange_exchange

## Reason

The rework dispatch is based on a historical failure already fixed in M2's landing
20261021T214830-L-1864636. The current source compiles, but still imports the unfinished
Sheaf internal-exchange duplicate. The adopted source now supplies a proved internal
exchange with the same data. Reuse it after a proved private tensorator equality,
removing that unfinished dependency. This is a real proof-dependency change rather
than resubmission of M2's repair. All public declarations, definitions, signatures,
visibility, and public imports stay identical. No target changes meaning.

## Old

```lean
import Sheaf.AlgebraicGeometry.InternalHomBaseChangeExchange
```

The internal exchange equation began:

```lean
  have hi := schemeInternalHom_baseChange_exchange f g M N
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.MixedInternalHomBaseChangeExchange
```

A proved private helper identifies the two tensorator wrappers:

```lean
private theorem schemeHomTensorPullbackIso_eq_mixed
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    schemeHomTensorPullbackIso f = mixedHomTensorPullbackIso f := by
  ext Z
  rfl
```

The helper is scoped under both backward transparency options set to true. Its
extensional hom equality is definitional: the compatibility wrapper rebuilds an
isomorphism from the same chosen hom. The proof then uses:

```lean
  have hi := mixedInternalHom_baseChange_exchange f g M N
  simp only [← schemeHomTensorPullbackIso_eq_mixed] at hi
  dsimp only [mixedHomDirectImageComparison] at hi
```

The existing change of type to the local internal exchange equation succeeds. The
two direct-image existence theorems have exactly the same proposition, so their
chosen comparisons agree by proof irrelevance. The remaining proof is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange | G3 (dispatched item) | Private proof import and proof changed; exact public signature preserved. |
| Sheaf.AlgebraicGeometry.GlobalHomBaseChangeCounitTransport | quarantined | Archived consumer only; original public exchange signature is identical, so no adaptation. |

`tools/downstream.py` reports zero active downstream modules. The sole textual
occurrence of the declaration in the active tree is its own declaration. A scratch
public consumer repeats the exact original signature and applies the theorem.
The artifact-producing compile passed for the revised module in 43.6 seconds and
the consumer in 4.8 seconds, without warnings. The scratch consumer is not delivered.
The old internal-exchange module is not deleted: no public declaration from the
adopted source is removed and no archived dependency is silently withdrawn.

## Status

landed 20261021T225127-L-3775558 2026-10-21 (merge of deliver/G3/Sheaf.AlgebraicGeometry.GlobalHomBaseChangeExchange)
