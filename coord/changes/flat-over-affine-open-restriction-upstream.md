# AlgebraicGeometry.isFlatOver_affineOpenRestriction

## Reason

Retire the duplicate Sheaf module and attach its mathematical node to the already
proved upstream declaration. This is the listed retirement item in
coord/retire-items.tsv. The current source has zero holes. The earlier inventory
compared private helper declarations and recorded different derived-category
imports; these do not obstruct retirement against the current source: both copies
now publicly import the same upstream DerivedOpenRestrictionMaps module, and the
upstream theorem has exactly the original statement. Its different private proof
uses Scheme.Modules.IsFlatOver.of_iso instead of a local flatOver_of_iso.

The retained upstream module compiled in 3.8 seconds. An example with the complete
old theorem statement, proved by applying the upstream theorem, compiled in
3.0 seconds. Its #print axioms output contains only propext, Classical.choice and
Quot.sound. No statement or definition changes mathematically, and no target
statement needs a semantic re-review.

## Old

In lean/Sheaf/AlgebraicGeometry/FlatOverAffineOpenRestriction.lean:

```lean
theorem isFlatOver_affineOpenRestriction
    {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G f) (V : S.affineOpens) :
    Scheme.Modules.IsFlatOver ((schemeOpenRestriction X (f ⁻¹ᵁ V.1)).obj G)
      ((f ∣_ V.1) ≫ V.2.isoSpec.hom)
```

## New

Exactly the same declaration, already proved in
lean/WeilConjectures/AlgebraicGeometry/FlatOverAffineOpenRestriction.lean:

```lean
theorem isFlatOver_affineOpenRestriction
    {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G f) (V : S.affineOpens) :
    Scheme.Modules.IsFlatOver ((schemeOpenRestriction X (f ⁻¹ᵁ V.1)).obj G)
      ((f ∣_ V.1) ≫ V.2.isoSpec.hom)
```

The duplicate Sheaf file is withdrawn using deleted.txt. The node
lem-pc-flat-over-affine-open-restriction keeps its statement, statement dependencies
and mathematical identity; only its Lean attachment and proof description change.
The upstream module, public imports, declarations and proofs are untouched.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FlatOverAffineOpenRestriction | K8 | Withdrawn duplicate; downstream.py reports no downstream modules and only its own theorem-name occurrence. |
| WeilConjectures.AlgebraicGeometry.FlatOverAffineOpenRestriction | unclaimed | Existing complete replacement; unchanged and compiled alone. |
| WeilConjectures.AlgebraicGeometry.CanonicalModuleBaseChangeAffineLocality | unclaimed | Already imports the upstream replacement and applies the same theorem; unchanged, compiled in 11.6 seconds. |
| WeilConjectures.AlgebraicGeometry.ProperFlatCohomologyData | unclaimed | Already imports the upstream replacement and applies the same theorem; unchanged, compiled in 15.7 seconds. |
| WeilConjectures | unclaimed | Already publicly imports the retained upstream module; unchanged. |

A repository import search finds no Lean importer of the withdrawn Sheaf module.
A search of quarantine also finds no importer. Both DAG parents still use
lem-pc-flat-over-affine-open-restriction, now attached to the exact upstream theorem:
lem-pc-canonical-module-base-change-affine-locality and
lem-pc-proper-flat-cohomology-model-data. Their Lean attachments are the two
unchanged upstream consumers above. Thus the parent dependency update is the
shared child's attachment migration; no dependency or unit proof step is removed.
The unit sk-thm-picard-f-representable has no realized entry for this node.

## Status

landed 20261020T221238-L-4163182 2026-10-20 (merge of deliver/K8/Sheaf.AlgebraicGeometry.FlatOverAffineOpenRestriction)
