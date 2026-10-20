# AlgebraicGeometry.conormalExteriorModule

## Reason

The human-authorized retirement list, coord/retire-items.tsv, names
Sheaf.RingTheory.ConormalExteriorModule and its upstream twin. The Sheaf
definition duplicates the upstream root-namespace conormalExteriorModule.
The current tree has no importers of the Sheaf module and no external uses
of AlgebraicGeometry.conormalExteriorModule. Its former consumers now
import upstream modules and resolve the unqualified name to the upstream
definition. Withdraw the unused duplicate and attach its DAG node to the
upstream declaration.

## Old

In Sheaf.RingTheory.ConormalExteriorModule:

```lean
namespace AlgebraicGeometry

noncomputable abbrev conormalExteriorModule (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^n I.Cotangent))

end AlgebraicGeometry
```

## New

Withdraw lean/Sheaf/RingTheory/ConormalExteriorModule.lean through deleted.txt.
The delivery tool leaves an empty module in its place. The existing declaration
in WeilConjectures.RingTheory.ConormalExteriorModule is used verbatim:

```lean
noncomputable abbrev conormalExteriorModule (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^n I.Cotangent))
```

The node new-r4-conormal-exterior-module now points at that upstream module,
file and declaration. Its mathematical statement stays unchanged. A server
compile of the original construction and the upstream definition proves their
equality by rfl for arbitrary universes, rings, ideals and degrees, with separate
checks for degree zero and the bottom and top ideals. The definition and equality
use only propext, Classical.choice and Quot.sound.

## Users

tools/downstream.py Sheaf.RingTheory.ConormalExteriorModule
--uses AlgebraicGeometry.conormalExteriorModule reports zero downstream
modules and only the defining module as a use of the qualified name. A source
import scan agrees. No consumer is adapted and no target interpretation changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.ConormalExteriorModule | J4 | unused duplicate withdrawn |

## Status

landed 20261020T132016-L-1401449 2026-10-20 (merge of deliver/J4/Sheaf.RingTheory.ConormalExteriorModule)
