# AlgebraicGeometry.AlgebraicSpace.strictLocalSchemeGerm

## Reason

Restore the quarantined item listed in coord/rework.tsv after the upstream sync.
The archived definition refers to the removed smallStrictHenselizationDiagram.
The current full affine pointed-neighbourhood diagram is strictHenselizationDiagram.
Its object at op N is the global sections of N's scheme, and its colimit is the
upstream strictHenselization. The inverse of smallStrictHenselizationColimitIso
then has exactly the required target strictHenselizationRing. Thus the repaired
map is the same canonical germ described by the node, using the current API.
The construction uses actual colimit data and the proved equivalence comparison.

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
  colimit.ι (Scheme.strictHenselizationDiagram t) (op N) ≫
    (Scheme.smallStrictHenselizationColimitIso t).inv
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SpaceStrictLocalFlatness | N4 | Internal uses in schemeStrictLocal_presentation and strictLocalChartComparison now elaborate; their signatures are preserved. |

`tools/downstream.py` with `--allow-missing` reports zero downstream modules.
A search of both Lean roots and quarantine/Sheaf finds no external occurrence
of the module or its five declaration names. The missing live source is the
quarantined source named in the rework record, rather than a withdrawn node.
DAG parents still cite the item; its attachment and all dependencies are retained.
No target statement or definition used in a target signature changes meaning.
No external consumer or source-library module is edited.

Validation: the restored module compiles through lcompile.py in 9.2 seconds.
The canonical comparison has type
`colimit (strictHenselizationAffineDiagram t) ≅ strictHenselization t`;
the inverse is essential to the displayed construction.

## Status

landed 20261024T190429-L-4052611 2026-10-24 (merge of deliver/N4/Sheaf.AlgebraicGeometry.SpaceStrictLocalFlatness)
