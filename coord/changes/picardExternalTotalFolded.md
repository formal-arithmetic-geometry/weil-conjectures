# AlgebraicGeometry.Scheme.Modules.picardExternalTotal

## Reason

Repair the 60-second compile return. The reducible abbreviation forces expansion of
mapBifunctor, its bicomplex and its totalization during homology type comparisons.
Use a semireducible definition with exactly the same type and body. This changes no
mathematical data or statement. The private proof also avoids costly concrete Ext
scalar-instance comparisons by composing linear maps over abstract modules and
constructing the tensor Ext pairing over an abstract abelian monoidal category.
The original profiler measured 29.7 seconds in kernel checking cupLinear_exists,
14.2 seconds for pullbackLinear_exists, and 4.1 seconds for cohomologyExtLinear_exists.
No file or proof has been split into separate modules.

## Old

```lean
noncomputable abbrev picardExternalTotal
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) : CochainComplex (ModuleCat.{w} k) ℤ :=
  HomologicalComplex.mapBifunctor (picardScalarModel f F) (picardScalarModel g G)
    (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ) 
```

## New

```lean
noncomputable def picardExternalTotal
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) : CochainComplex (ModuleCat.{w} k) ℤ :=
  HomologicalComplex.mapBifunctor (picardScalarModel f F) (picardScalarModel g G)
    (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
```

The body is identical; only abbrev becomes def. It remains definitionally equal to
the original total complex, with explicit unfolding available to callers. The item's
rewrite proof now changes the Kunneth formula's right side to T.homologyπ before rw.
No target statement or its meaning changes: the construction is definitionally identical.
As required by AGENTS.md §4 for a definition change, affected target interpretation
checks are reopened; this second reading verifies equality of the old and new data.
The maintainer records the corresponding target-review status.

Second reading removes the redundant direct public imports of ModuleCat.Colimits,
ModuleCat.Monoidal.Basic and ShortComplex.HomologicalComplex. All three remain
in the public import closure of PicardKunnethResolutionModel (and Coherent), so
the declarations those three modules expose remain available downstream.
Also removed ShortComplex.ModuleCat: it is available to this proof through the
plain TensorKunnethNat import and is not needed in the public signatures or
definitions. All eight unchanged downstream users were recompiled after this
cleanup (4.5–10.3 s); no forced adaptation was needed.

## Users

Read-only downstream.py --uses picardExternalTotal found these textual users.
All seven direct importers and the additional textual user PicardKunnethCechModels
were compiled independently against the sandbox overlay. All compiled unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardExternalCupAcyclic | unclaimed | Unchanged source compiled against the repaired definition; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupCochain | Y2 | Own rewrite repaired by explicitly identifying the total-homology projection. |
| Sheaf.AlgebraicGeometry.PicardExternalCupLeftHomologyLadder | C4 | Unchanged source compiled against the repaired definition; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupQuasiIso | unclaimed | Unchanged source compiled against the repaired definition; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightExactLadder | N1 | Unchanged source compiled against the repaired definition; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupRightShortExact | unclaimed | Unchanged source compiled against the repaired definition; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftLeft | unclaimed | Unchanged source compiled against the repaired definition; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupShiftRight | unclaimed | Unchanged source compiled against the repaired definition; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | Unchanged source compiled against the repaired definition; no adaptation. |

## Status

landed 20261013T082426-L-1652175 2026-10-13 (merge of deliver/Y2/Sheaf.AlgebraicGeometry.PicardExternalCupCochain)
