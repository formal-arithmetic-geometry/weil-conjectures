# AlgebraicGeometry.exteriorSheaf_dual_ext

## Reason

Retirement item `Sheaf.AlgebraicGeometry.ExteriorSheafDualExt`, listed in
`coord/retire-items.tsv`, under the human's 2026-10-20 retirement instruction in
`coord/changes/retire-sheaf-twins-20261020.md`. The old module and the upstream twin
both declare this name, but on different exterior-sheaf encodings. Import replacement
alone cannot typecheck their consumers. Retire the copied proof and transport the
upstream result across an explicitly constructed isomorphism instead.

## Old

The retired module `Sheaf.AlgebraicGeometry.ExteriorSheafDualExt` exported:

```lean
theorem exteriorSheaf_dual_ext (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens)
    (q r : (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op U))
    (h : ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)),
      q.app (op (Over.mk g)) (Scheme.Modules.exteriorSheafSection M n V a) =
        r.app (op (Over.mk g)) (Scheme.Modules.exteriorSheafSection M n V a)) :
    q = r
```

## New

The DAG attachment points to `WeilConjectures.AlgebraicGeometry.ExteriorSheafDualExt`:

```lean
theorem exteriorSheaf_dual_ext (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens)
    (q r : (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op U))
    (h : ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)),
      q.app (op (Over.mk g)) (Scheme.Modules.wedge (M := M) (r := n) (U := V) a) =
        r.app (op (Over.mk g)) (Scheme.Modules.wedge (M := M) (r := n) (U := V) a)) :
    q = r
```

The new module `Sheaf.AlgebraicGeometry.ExteriorSheafComparison` constructs
`Scheme.Modules.exteriorSheafPresheafIso` by identity components, then
`Scheme.Modules.exteriorSheafIsoExteriorPower` by applying sheafification. Theorems
`exteriorSheafIsoExteriorPower_hom_wedge` and `exteriorSheafIsoExteriorPower_inv_wedge`
prove its action on wedges. It supplies the proved API compatibility theorem:

```lean
theorem exteriorSheaf_dual_ext_compat (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens)
    (q r : (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op U))
    (h : ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)),
      q.app (op (Over.mk g)) (Scheme.Modules.exteriorSheafSection M n V a) =
        r.app (op (Over.mk g)) (Scheme.Modules.exteriorSheafSection M n V a)) :
    q = r
```

Its proof precomposes dual sections with the inverse comparison on Over U, applies
the unchanged upstream theorem, and cancels the isomorphism. This adds no assumption
and changes no consumer signature. Both definitions of the exterior sheaf remain
unchanged; their equivalence is proved rather than presumed. No source-library file
or target declaration is changed. The retired file is listed in `deleted.txt` and
has no remaining importer in the delivery overlay.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ExteriorSheafDualExt --uses
exteriorSheaf_dual_ext` reports the three direct consumers, plus the retired module
itself as a textual occurrence. All six downstream modules are accounted for below.
The three adapted consumers were unclaimed when checked. Each edit replaces the
private import by `ExteriorSheafComparison` and each extensionality application by
`exteriorSheaf_dual_ext_compat`; all other lines and signatures are preserved.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ExteriorSheafDualExt | C6 | Retired in favor of the upstream theorem. |
| Sheaf.AlgebraicGeometry.DeterminantDualPairingFunctional | unclaimed | Import and one application adapted; signature unchanged; compiled. |
| Sheaf.AlgebraicGeometry.DeterminantDualAlternatingFamily | unclaimed | Import and four applications adapted; signature unchanged; compiled. |
| Sheaf.AlgebraicGeometry.DeterminantDualPairing | unclaimed | Import and one application adapted; signature unchanged; compiled. |
| Sheaf.AlgebraicGeometry.DeterminantExteriorDualIso | unclaimed | Transitive user; no signature or proof edit needed. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive user; no signature or proof edit needed. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive user; no signature or proof edit needed. |

## Status

landed 20261020T144238-L-2258197 2026-10-20 (merge of deliver/C6/Sheaf.AlgebraicGeometry.ExteriorSheafDualExt)
