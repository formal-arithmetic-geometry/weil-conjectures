# AlgebraicGeometry.Scheme local postcomposition continuity

## Reason

The proof constructs a sheaf adjunction from the existing site map/pullback adjunction.
Its left site functor is wrapped in `proEtaleIsoPostcompose`. Registering an existing
continuity proof locally lets the sheaf-transport APIs infer the topology instances.
The conservative source interface check detects the added `attribute` command, hence
this record. The registration is local to the file and changes no importing environment.

## Old

```lean
set_option autoImplicit false

universe u v w w'

open CategoryTheory CategoryTheory.Limits Opposite
```

There was no local continuity registration. All existing public signatures, public
imports and non-theorem bodies are retained verbatim.

## New

The existing options, universes and opens above are unchanged. The only extra command is:

```lean
attribute [local instance] isoPostcompose_continuous
```

It registers the new proved private helper:

```lean
private theorem isoPostcompose_continuous {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] :
    (proEtaleIsoPostcompose f).IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
  ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)
```

Other added helpers are private and hole-free. No imports are added or removed.
No definition meaning, theorem statement, target, or unit route changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage` | X8 | Local proof elaboration only. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage
--uses isoPostcompose_continuous` found zero modules using the private helper
(3,156 transitive importers were listed).

There are no public declarations with changed types, visibility, attributes or bodies
other than theorem proofs. The detected interface delta is exclusively the command
above; it names a private helper and its attribute is local. No downstream declaration
references that helper and no downstream adaptation is required.

## Status

landed 20261025T181335-L-4158357 2026-10-25 (merge of deliver/X8/Sheaf.AlgebraicGeometry.ProEtaleIsomorphismInverseImage)
