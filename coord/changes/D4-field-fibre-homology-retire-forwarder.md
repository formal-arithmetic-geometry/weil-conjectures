# Sheaf.AlgebraicGeometry.FieldFibreHomology

## Reason

Withdraw the unused forwarding module after the reviewed Q5 restoration already
moved the theorem's implementation and DAG attachment to the adopted upstream
module. This is the remaining retirement of the compatibility path, not a new
proof or a change to the theorem. The assigned rework row has already disappeared
from the current tree during this session; coord/retire-items.tsv still lists the
Sheaf module. The live source exists and is the re-export below, so this delivery
does not withdraw an absent quarantine path.

## Old

```lean
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.FieldFibreHomology

/-!
# Field fibre homology

The upstream module supplies the identical `single_field_fibre_homology` theorem.
Re-export it here instead of maintaining a duplicate proof and private helpers.
Source: blueprint lem-pc-perfect-locus, proof step 4.
(blueprint: new-field-fibre-homology).
-/

@[expose] public section
```

## New

The path is withdrawn through deleted.txt. The delivery tool installs an empty
`module` stub. The complete theorem and all its upstream imports, signatures,
attributes, proof bodies, and private helpers remain unchanged in
`WeilConjectures.AlgebraicGeometry.FieldFibreHomology`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FieldFibreHomology | D4 | Unused forwarding path withdrawn. |
| WeilConjectures.AlgebraicGeometry.FieldFibreHomology | unmodified | Complete implementation retained. |
| WeilConjectures.AlgebraicGeometry.FiniteFreeSingleFieldFibre | unmodified | Already directly imports the upstream implementation. |

A direct import scan of lean/Sheaf, lean/WeilConjectures, and quarantine finds zero
importers of the withdrawn path. A full DAG scan finds no Lean attachment to it.
The only parent citing node new-field-fibre-homology is
lem-pc-finite-free-single-field-fibre, attached to the upstream consumer in the
table; its proof explicitly calls single_field_fibre_homology through its private
upstream import. The child node is already attached to the upstream theorem.
Thus the existing parent proof is the replacement argument; no mathematical
edge or unit step is removed and no parent dependency requires an update.

The unit sk-thm-picard-perfect and its realized record are unchanged. No statement,
definition, or target interpretation changes. No consumer adaptation is needed.

## Status

landed 20261020T160750-L-3404246 2026-10-20 (merge of deliver/D4/Sheaf.AlgebraicGeometry.FieldFibreHomology)
