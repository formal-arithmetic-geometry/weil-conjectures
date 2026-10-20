# AlgebraicGeometry.exterior_dual_pairing_app_bijective

## Reason

Retire the duplicate Sheaf module as assigned in coord/retire-items.tsv, row 487.
The official theorem is fully proved, with exteriorPower and wedge in its API.
The three consumers retain statements using exteriorSheaf. Apply the existing
canonical exteriorSheafPowerIso to the source and its contravariant dual to the
target. Its inverse-wedge formula proves the transported determinant hypothesis.
Apply the official theorem and cancel the two bijective section comparisons.
No upstream module or target statement changes.

## Old

The withdrawn Sheaf module supplied:

```lean
theorem exterior_dual_pairing_app_bijective (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (f : Scheme.Modules.exteriorSheaf (Scheme.Modules.dual M) n ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorSheaf M n))
    (hf : ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U))
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
      (f.val.app (op U) (Scheme.Modules.exteriorSheafSection
        (Scheme.Modules.dual M) n U φ)).app (op (Over.mk (𝟙 U)))
        (Scheme.Modules.exteriorSheafSection M n U a) =
      (Matrix.of fun i j ↦
        (show X.presheaf.obj (op U) from
          (φ j).app (op (Over.mk (𝟙 U))) (a i))).det)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    (V : X.Opens) (g : V ⟶ U) :
    Function.Bijective (f.val.app (op V))
```

## New

The node points to the existing theorem in
WeilConjectures.AlgebraicGeometry.DeterminantDualPairingLocal:

```lean
theorem exterior_dual_pairing_app_bijective (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (f : Scheme.Modules.exteriorPower (Scheme.Modules.dual M) n ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorPower M n))
    (hf : ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U))
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
      (f.val.app (op U) (wedge (M := Scheme.Modules.dual M) (r := n) (U := U) φ)).app
          (op (Over.mk (𝟙 U)))
        (wedge (M := M) (r := n) (U := U) a) =
      (Matrix.of fun i j ↦
        (show X.presheaf.obj (op U) from
          (φ j).app (op (Over.mk (𝟙 U))) (a i))).det)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    (V : X.Opens) (g : V ⟶ U) :
    Function.Bijective (f.val.app (op V))
```

For each legacy pairing f, let a be exteriorSheafPowerIso of the dual and let b
be dualFunctor.mapIso of the inverse exterior comparison. The official pairing is
a.inv ≫ f ≫ b.hom. Both inverse-wedge identities identify its determinant formula
with the formula for f. On any open, its section map is the composite of f's
section map with two bijections. Function.Bijective.of_comp_iff and of_comp_iff'
therefore recover bijectivity of the original section map. The original consumers'
public imports, declarations, signatures, attributes, and docstrings are preserved.
Only private imports and the necessary proof expressions change.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal | B8 assignment | Withdraw the duplicate and attach its node to the official theorem. |
| Sheaf.AlgebraicGeometry.DeterminantExteriorDualIso | unclaimed | Import the official theorem and existing exterior comparison; transport the pairing and cancel the comparisons. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal | unclaimed | Same transport at the local conormal frame; retain the original stalk-surjectivity argument and statement. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection | unclaimed | Same transport at the local conormal frame; retain the original stalk-surjectivity argument and statement. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Indirect consumer; unchanged interface, no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop | unclaimed | Indirect consumer; unchanged interface, no adaptation. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtExterior | unclaimed | Indirect consumer; unchanged interface, no adaptation. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Indirect consumer; unchanged interface, no adaptation. |

The downstream.py import-closure scan lists the seven consumers above; its
symbol-use scan lists only the three adapted direct consumers and the withdrawn
module. No quarantined module imports the withdrawn module. All three adapted
consumers compile together against the sandbox overlay (3.1 s, 8.9 s, 8.6 s).
The comparison is defined by sheafifying identity maps on sectionwise exterior
powers, and its wedge formula is proved by naturality of the adjunction unit.
It requires no rank, nonzero-ring, or nonempty-open assumption. Degree zero,
degrees above the local rank, zero rings, and empty opens are preserved exactly.
No definition changes, so no target statement rereview is triggered.

## Status

landed 20261020T211636-L-3481975 2026-10-20 (merge of deliver/B8/Sheaf.AlgebraicGeometry.DeterminantDualPairingLocal)
