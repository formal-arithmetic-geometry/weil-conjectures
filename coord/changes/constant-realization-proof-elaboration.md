# CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension

## Reason

The static delivery checker requests a change record for new `open` and `attribute`
commands. These commands support only proof elaboration: opening the existing tensor notation
and retaining chosen adjoints as locally irreducible prevents repeated reduction of
`Functor.leftAdjoint`. The complete compiled module then finishes in 39 seconds under the
unchanged 60-second limit. No public declaration signature, public import, definition body, instance,
notation declaration or globally persistent attribute is changed. The private helper `realizationRingUnit_naturality` has definitionally identical universe
annotations added to its signature and its proof specifies the value category of
`toSheafify_naturality` explicitly. Restoring its implicit universe annotations made the full
build exceed 60 seconds again. This private theorem has no external consumers.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

The private helper's statement used implicit value-category universes:

```lean
private theorem realizationRingUnit_naturality (V : Cᵒᵖ) (a : R) :
    (((sheafCompose J (forget₂ CommRingCat RingCat)).map
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom q))).hom.app V)
        ((realizationRingUnit J R).app V a) =
      (realizationRingUnit J S).app V (q a)
```

No local irreducibility attributes were set in this module.

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
```

The following local attributes are introduced within the existing namespace and section:

```lean
attribute [local irreducible] Functor.leftAdjoint
attribute [local irreducible] adjunction derivedExtension moduleDerivedExtension
  derivedAdjunction moduleDerivedAdjunction
```

The private helper now supplies those same universes explicitly:

```lean
private theorem realizationRingUnit_naturality (V : Cᵒᵖ) (a : R) :
    (((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map
      ((constantSheaf J CommRingCat.{max u v}).map (CommRingCat.ofHom q))).hom.app V)
        ((realizationRingUnit J R).app V a) =
      (realizationRingUnit J S).app V (q a)
```

The two signatures elaborate to the same proposition; this adds no hypothesis or conclusion.
The attributes' scope ends within this module. All existing public signatures and data constructions
remain verbatim. New proved private helpers use the tensor notation and adjunction APIs.

## Users

`tools/downstream.py Sheaf.Paper.ConstantRealizationDerivedScalarExtension --uses
constantRealizationDerivedScalarExtension` reports three modules with uses of this theorem.
The 247 transitive downstream modules also retain the same interface: local `open` commands
and local irreducibility attributes do not export changes to importers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantRealizationDerivedScalarExtension | S3 | Two proof holes filled; local proof elaboration controls added. |
| Sheaf.Paper.ConstantDerivedNormalizationUniversal | unclaimed | None: same theorem statement and definitions. |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | None: same theorem statement and definitions. |

No downstream adaptation is necessary, and no target definition or statement is altered.

## Status

landed 20261021T004843-L-1795499 2026-10-21 (merge of deliver/S3/Sheaf.Paper.ConstantRealizationDerivedScalarExtension)
