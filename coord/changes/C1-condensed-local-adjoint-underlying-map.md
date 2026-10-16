# AlgebraicGeometry.ProEtale.finiteCoefficientLocalAdjoint

## Reason

Give the existing canonical local adjoint an explicit underlying-map API. Its old body computes a transitivity isomorphism, transposes through an adjunction and composes with a restriction comparison. The proof needs its underlying mixed-scalar map. Construct that map directly, prove its linearity from the old canonical adjunct, and package it using Mod.Hom.mk'. The theorem `finiteCoefficientLocalAdjoint_eq_canonical` proves equality to the previous definition. Tensor models, tensor maps and all existing declaration signatures and visibility stay unchanged. The module was unclaimed.

The new public import of CondensedCoefficientComplexDiagram supplies the mixed-scalar construction used by the definition. Its unit identities `scalar_unit` and `mixedScalarMap_unit` are proved once generically in this module and exported for the overlap proof. The duplicate private proofs in CondensedOverlapFactorTranspose are removed; that module uses its existing import of this module. The existing monomorphism and scalar-adjunction proofs now rewrite through the equality API. No sorry is added. Any Challenge target that uses this definition receives the prescribed meaning review; the equality theorem proves its meaning unchanged.

## Old

```lean
noncomputable def finiteCoefficientLocalAdjoint :
    finiteCoefficientLocalModel T X f ℓ E Y g P F hEF ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj
          ((Mod.comap ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M) :=
  (Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F)))).homEquiv _ _
        (finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF) ≫
    ((upperStar Ab.{u + 1} g).mapModComapIso ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F))).inv.app M
```

## New

```lean
noncomputable def finiteCoefficientLocalAdjointHom :
    (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF).X ⟶
      (((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj
          ((Mod.comap ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M)).X :=
  (Mod.mixedScalarMap
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))
    ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F)))
    (finiteCoefficientLocalScalarTriangle T X f ℓ E Y g F hEF)
    (finiteCoefficientLocalScalarTriangle T X f ℓ E Y g F hEF) P).hom ≫ a.hom

set_option backward.isDefEq.respectTransparency false in
private theorem canonicalAdjoint_eq_explicit :
    ((Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F)))).homEquiv _ _
        (finiteCoefficientLocalTensorMap T X f ℓ E Y g P M a F hEF) ≫
    ((upperStar Ab.{u + 1} g).mapModComapIso ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ F))).inv.app M).hom =
      finiteCoefficientLocalAdjointHom T X f ℓ E Y g P M a F hEF := by
  let φ := (upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF))
  let ψ := (upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F))
  let χ := (upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))
  have he : φ ≫ ψ = χ :=
    finiteCoefficientLocalScalarTriangle T X f ℓ E Y g F hEF
  simp only [Mod.comp_hom', Functor.mapModComapIso_inv_app_hom]
  erw [Category.comp_id]
  change ((Mod.extendRestrictAdjunction ψ).homEquiv _ _
    ((Mod.extendScalarsComp φ ψ).inv.app P ≫
      (Mod.extendScalarsIsoOfEq he).hom.app P ≫ a)).hom =
    (Mod.mixedScalarMap φ χ φ χ ψ he he P).hom ≫ a.hom
  exact tensorAdjoint_eq_mixed φ ψ he P _ a

/-- The explicitly constructed local map is linear over the finite coefficient ring. -/
theorem finiteCoefficientLocalAdjointHom_linear :
    γ[
      (upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F)),
      (finiteCoefficientLocalModel T X f ℓ E Y g P F hEF).X] ≫
        finiteCoefficientLocalAdjointHom T X f ℓ E Y g P M a F hEF =
    (upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F)) ◁
      finiteCoefficientLocalAdjointHom T X f ℓ E Y g P M a F hEF ≫
    γ[
      (upperStar Ab.{u + 1} g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F)),
      (((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj
          ((Mod.comap ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M)).X] := by
  rw [← canonicalAdjoint_eq_explicit]
  exact Mod.act_hom _

/-- The canonical adjoint into the restriction of the given module, at stage `F`. -/
noncomputable def finiteCoefficientLocalAdjoint :
    finiteCoefficientLocalModel T X f ℓ E Y g P F hEF ⟶
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj
          ((Mod.comap ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M) :=
  Mod.Hom.mk' (finiteCoefficientLocalAdjointHom T X f ℓ E Y g P M a F hEF)
    (finiteCoefficientLocalAdjointHom_linear T X f ℓ E Y g P M a F hEF)
```

The named underlying map is `finiteCoefficientLocalAdjointHom`: the mixed-scalar map from E-to-F scalar extension to E-to-Omega scalar extension, followed by a.hom. `finiteCoefficientLocalScalarTriangle` is the pulled coefficient triangle; `finiteCoefficientLocalAdjointHom_linear` supplies the module-homomorphism law; `finiteCoefficientLocalAdjoint_eq_canonical` identifies the resulting module homomorphism with the old definition. All four supporting declarations are proved or explicit data constructions, and are attached to the existing local-adjoints node.

## Users

The table includes all modules printed by `tools/downstream.py --uses finiteCoefficientLocalAdjoint`, plus the new helper. The unchanged direct consumer CondensedFiniteLocalSubmodules compiled; the item and helper compile against this API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | C1 | Use the proved mixed-scalar formula for colimit legs. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedLocalCoefficientAdjoints | unclaimed | Explicit underlying map and proved equality to the old adjunct; adapt its two existing proofs. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedOverlapFactorTranspose | C1 (new module in this item) | Use the explicit formula and its scalar-unit identity. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| TargetsCheck | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No edit; the definition is equal to its previous construction, so statements retain their meaning. |

## Status

landed 20261016T221557-L-1611538 2026-10-16 (merge of deliver/C1/Sheaf.Paper.CondensedFiniteFamilyHomDescent)
