# AlgebraicGeometry.exterior_dual_pairing_functional

## Reason

Retirement item `Sheaf.AlgebraicGeometry.DeterminantDualPairingFunctional`, listed in
`coord/retire-items.tsv`. Its adopted upstream twin already proves the determinant
functional theorem using `Scheme.Modules.exteriorPower`. The sole consumer uses
`Scheme.Modules.exteriorSheaf`, whose canonical comparison with the upstream
construction is proved in `Sheaf.AlgebraicGeometry.ExteriorSheafComparison`.
Retire the duplicate and transport the upstream functional along that comparison.

## Old

The withdrawn Sheaf module exported the following statement:

```lean
theorem exterior_dual_pairing_functional (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)) :
    ∃! q : (Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n)).val.obj (op U),
      ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)),
        q.app (op (Over.mk g)) (Scheme.Modules.exteriorSheafSection M n V a) =
          (Matrix.of fun i j ↦ (show X.presheaf.obj (op V) from
            (φ j).app (op (Over.mk g)) (a i))).det
```

## New

The DAG attaches to the existing upstream module
`WeilConjectures.AlgebraicGeometry.DeterminantDualPairingFunctional`:

```lean
theorem exterior_dual_pairing_functional (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)) :
    ∃! q : (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op U),
      ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)),
        q.app (op (Over.mk g)) (wedge (M := M) (r := n) (U := V) a) =
          (Matrix.of fun i j ↦ (show X.presheaf.obj (op V) from
            (φ j).app (op (Over.mk g)) (a i))).det
```

No adopted upstream file is edited. In `DeterminantDualAlternatingFamily`, choose
`q₀` from the upstream theorem and explicitly construct the earlier functional as
`F.map e.hom.val ≫ q₀`, where `F` restricts to Over U and
`e = exteriorSheafIsoExteriorPower M n`. The comparison's proved hom-wedge formula
makes its determinant evaluation identical. The rest of the alternating-map proof
is unchanged. The consumer's signature, attributes, public imports and docstring
are unchanged; no extra hypothesis or changed definition is involved. This works
in degree zero, on the empty open and over the zero ring, since the comparison
and the upstream theorem have no exclusions. A functional is chosen only from
the upstream unique-existence theorem, then transported by an explicit map.

Validation: the adapted consumer compiled cleanly in 3.6 seconds. An import-only
counterfactual failed in 8.2 seconds at `toFun := q` (line 56): `q` returns
`(M.exteriorPower n).dual` sections where `(M.exteriorSheaf n).dual` sections are
required. Its later uses also failed on `exteriorSheafSection` versus `wedge`.
The explicit precomposition and hom-wedge formula repair exactly this mismatch.
An axiom probe of the adapted `exterior_dual_pairing_local` also compiled (4.7
seconds) and reports only `propext`, `Classical.choice`, and `Quot.sound`.

The duplicate module is listed in `deleted.txt`. All Lean importers have been
adapted. The functional DAG node points to the upstream theorem and records its
actual proof; the consumer node records the additional comparison step.
The unit statement and unit steps are preserved. No target needs a statement
review because no definition or target statement changes.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DeterminantDualPairingFunctional
--uses exterior_dual_pairing_functional` reports five downstream modules. Only
`DeterminantDualAlternatingFamily` directly imports or calls the retired module.
All holders below were checked in the current claim records.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DeterminantDualPairingFunctional | T1 | Withdrawn; node moved to upstream. |
| Sheaf.AlgebraicGeometry.DeterminantDualAlternatingFamily | unclaimed | Private import replaced; upstream functional transported; compiled. |
| Sheaf.AlgebraicGeometry.DeterminantDualPairing | unclaimed | Transitive user; same consumer theorem and public imports. |
| Sheaf.AlgebraicGeometry.DeterminantExteriorDualIso | unclaimed | Transitive user; unchanged. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive user; unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive user; unchanged. |

## Status

landed 20261020T154939-L-3175302 2026-10-20 (merge of deliver/T1/Sheaf.AlgebraicGeometry.DeterminantDualPairingFunctional)
