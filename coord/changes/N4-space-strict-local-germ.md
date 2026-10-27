# AlgebraicGeometry.AlgebraicSpace.strictLocalSchemeGerm

## Reason

Restore the quarantined module assigned by coord/rework.tsv. Its germ construction
referred to the removed Scheme.smallStrictHenselizationDiagram. In addition to the
removed name, that diagram is indexed by a small representative category, whereas
N is an actual affine pointed neighbourhood. The existing upstream
Scheme.strictHenselizationDiagram is indexed by exactly these neighbourhoods.
Its colimit is Scheme.strictHenselization; the inverse of the existing canonical
smallStrictHenselizationColimitIso transports its leg to strictHenselizationRing.
Thus the corrected construction realizes the existing docstring and signature.
It adds no arbitrary witness or unproved data and preserves the intended germ.

## Old

```lean
def strictLocalSchemeGerm {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (N : Scheme.AffinePointedEtaleNeighborhood t) :
    Γ(N.obj.1.left, ⊤) ⟶ Scheme.strictHenselizationRing t :=
  colimit.ι (AlgebraicGeometry.Scheme.smallStrictHenselizationDiagram t) (op N) ≫
    (Scheme.smallStrictHenselizationColimitIso t).inv
```

## New

```lean
def strictLocalSchemeGerm {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) (N : Scheme.AffinePointedEtaleNeighborhood t) :
    Γ(N.obj.1.left, ⊤) ⟶ Scheme.strictHenselizationRing t :=
  colimit.ι (AlgebraicGeometry.Scheme.strictHenselizationDiagram t) (op N) ≫
    (Scheme.smallStrictHenselizationColimitIso t).inv
```

## Users

The required tools/downstream.py query reports "unknown module(s)" because this
item is quarantined. A direct search of lean/Sheaf, lean/WeilConjectures and all
quarantine sources finds no external importer or declaration consumer. The only
uses are in the two retained statements in this same restored module. All five
existing declaration signatures and all public imports remain verbatim. No other
module requires adaptation. The DAG attachment and dependencies are preserved;
the lean.note now documents the corrected construction. No target statement is
changed, and the restoration implements the already specified canonical germ.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SpaceStrictLocalFlatness | N4 | Restore the module and repair strictLocalSchemeGerm; its two statement consumers compile unchanged. |

## Status

landed 20261024T190429-L-4052611 2026-10-24 (merge of deliver/N4/Sheaf.AlgebraicGeometry.SpaceStrictLocalFlatness)
