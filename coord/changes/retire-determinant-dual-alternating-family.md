# AlgebraicGeometry.exterior_dual_pairing_local

## Reason

Retirement item `Sheaf.AlgebraicGeometry.DeterminantDualAlternatingFamily`, listed
in `coord/retire-items.tsv`. Its adopted upstream twin already proves the same
intrinsic alternating determinant-family statement using `exteriorPower`.
The sole direct consumer uses `exteriorSheaf`; their canonical wedge-preserving
comparison already exists and is proved. Retire the duplicate and transport the
upstream family in that consumer. The item currently has zero holes.

## Old

The withdrawn Sheaf declaration has this signature:

```lean
theorem exterior_dual_pairing_local (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    ∃! A : ((Scheme.Modules.dual M).val.obj (op U)) [⋀^Fin n]→ₗ[X.presheaf.obj (op U)]
        ((Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op U)),
      ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V))
        (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
        (A φ).app (op (Over.mk g)) (Scheme.Modules.exteriorSheafSection M n V a) =
          (Matrix.of fun i j ↦ (show X.presheaf.obj (op V) from
            (φ j).app (op (Over.mk g)) (a i))).det
```

## New

The node now attaches to the existing, unchanged upstream declaration in
`WeilConjectures.AlgebraicGeometry.DeterminantDualAlternatingFamily`:

```lean
theorem exterior_dual_pairing_local (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    ∃! A : ((Scheme.Modules.dual M).val.obj (op U)) [⋀^Fin n]→ₗ[X.presheaf.obj (op U)]
        ((Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op U)),
      ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V))
        (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
        (A φ).app (op (Over.mk g)) (wedge (M := M) (r := n) (U := V) a) =
          (Matrix.of fun i j ↦ (show X.presheaf.obj (op V) from
            (φ j).app (op (Over.mk g)) (a i))).det
```

In `Sheaf.AlgebraicGeometry.DeterminantDualPairing`, replace the private import
with the upstream module and choose its uniquely characterized family `A₀`.
Put `e := exteriorSheafIsoExteriorPower M n` and define the earlier family on U
as the composition of `A₀ U` with the sectionwise linear map
`((dualMap e.hom).val.app (op U)).hom`, using `LinearMap.compAlternatingMap`.
This is an explicit transport of the unique upstream data, with all alternating
identities inherited from the linear map. Its evaluation is the upstream
functional evaluated on `e.hom` of the wedge. The proved
`exteriorSheafIsoExteriorPower_hom_wedge` rewrites this to the upstream wedge,
so the upstream determinant formula gives exactly the old formula on every
subopen. The rest of the consumer's proof is unchanged.

The consumer's signature, attributes, public imports and docstring stay verbatim.
No definition, target or adopted upstream file changes. The canonical comparison
is valid in degree zero, on the empty open and over the zero ring, and neither
the upstream theorem nor the transport assumes local freeness. The unit route
is preserved: the construction still uses the local alternating-family node,
which now records the upstream theorem. No target statement review is reopened.

Validation: the adapted consumer compiled cleanly in 11.9 seconds. An import-only
counterfactual failed in 7.9 seconds at line 61: `(A U) φ` has type
`((M.exteriorPower n).dual.val.obj (op U))` where the restriction map requires
`((M.exteriorSheaf n).dual.val.obj (op U))`; further uses failed at lines 80, 92
and 116 for the same codomain mismatch. The explicit transport and its wedge
formula repair this incompatibility. An axiom probe compiled in 11.6 seconds:
both `exterior_dual_pairing_local` and the adapted `exterior_dual_pairing_exists`
use only `propext`, `Classical.choice`, and `Quot.sound`.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DeterminantDualAlternatingFamily
--uses exterior_dual_pairing_local` reports the four downstream modules below.
Only `DeterminantDualPairing` imports or calls the withdrawn module. Current
claim files show the item held by B4 and all four downstream modules unclaimed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DeterminantDualAlternatingFamily | B4 | Withdrawn; node moved to upstream. |
| Sheaf.AlgebraicGeometry.DeterminantDualPairing | unclaimed | Private import migrated and family transported; same signature. |
| Sheaf.AlgebraicGeometry.DeterminantExteriorDualIso | unclaimed | Transitive user; unchanged interface. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive user; unchanged interface. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive user; unchanged interface. |

All DAG citers of the local-family node retain the same intrinsic mathematical
statement; its only direct Lean consumer is adapted in this packet. The node's
proof now describes the upstream proof and drops its former comparison dependency.
The construction node records its new transport step. No DAG node is removed.

## Status

landed 20261020T163938-L-3832985 2026-10-20 (merge of deliver/B4/Sheaf.AlgebraicGeometry.DeterminantDualAlternatingFamily)
