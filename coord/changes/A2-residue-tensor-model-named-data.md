# Tensor-model maps with named derived functors and counits

## Reason

The old bodies unfold the typed derived pullback and reconstruct its exact
counit inside tactic-mode definitions. Specializing the naturality argument
then compares terms through large functor and monoidal structures. The complete
abstract descent proof compiled, but concrete specializations repeatedly hit
the 60-second limit. Retaining the already existing named functor and counits
makes the concrete application compile without unfolding those structures.

The two concrete definitions retain their named functors and counits.
The new `Functor.tensorModelMapWith` is the same explicit composition with a
named derived functor and counit, paralleling the existing
`Functor.tensorModelTargetWith`. The legacy `Functor.tensorModelMap` is its
exact-derived-functor specialization. The private naturality proof now compares
the named common map instead of expanding tensor and Kan-extension data.
The first typed-definition version compiled at 57.7 seconds but timed out in
the delivery dry run; after this additional factory the full sandbox compile
takes 14.5 seconds for the model and 45.8 seconds for descent.

Every existing signature is preserved. Their signatures, visibility,
ordinary monoidal instance, and the canonical morphisms they construct stay the
same. Expanding `residueExchangeUpperStar`, `residueExchangeUpperStarCounit`,
`residueExchangeTensorCounit`, `Functor.tensorModelTarget`, and
`Functor.tensorModelMap` identifies the old and new constructions: braiding,
the coefficient comparison, the same two counits, and the same Qh tensor map
for the target; the same tensor counit, exact-pullback counit, and ordinary
oplax map for the common map. Neither a theorem-selected object nor a new
hypothesis is introduced.

The model module is unclaimed. No target signature is changed. Since these
definitions occur in the targets' dependency closure, their preserved meaning
is submitted for the required statement review as part of this change.

## Old

```lean
/-- The common map: the tensor counit, the exact-F counit, then the ordinary
comonoidal comparison.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def tensorModelMap (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (H.obj (DerivedCategory.Qh.obj P)) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  F.leftDerivedFunctor.map (ε.app P) ≫ F.leftDerivedFunctorCounit.app _ ≫
    DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map
          ((CategoryTheory.homotopyTensorSingleIso B).inv.app P) ≫
        ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
          (tensorModelCoefficient B)).app P)

@[irreducible]
noncomputable def residueExchangeTensorModelTarget :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P) ⊗
        (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
          (residueExchangeCoefficient ℓ E Y) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  unfold residueExchangeUpperStar
  exact Functor.tensorModelTarget (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeOrdinaryCoefficient ℓ E Y) P

noncomputable def residueExchangeTensorModelMap :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        ((residueExchangeRestriction ℓ E Y).obj
          ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P))) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) := by
  let := residueExchangeOrdinaryPullMonoidal ℓ E f
  unfold residueExchangeUpperStar
  exact Functor.tensorModelMap (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeOrdinaryCoefficient ℓ E Y)
    (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
    (by
      unfold residueExchangeReduction integralReduction residueExchangeRestriction
      exact Mod.tensorPresentationDerivedCounit (coefficientMap (integralReductionMap ℓ E) Y)) P
```

## New

```lean
/-- The common map built directly from a named derived functor and two named counits.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
@[irreducible] noncomputable def tensorModelMapWith
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (γ : DerivedCategory.Qh ⋙ G ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : HomotopyCategory C (.up ℤ)) :
    G.obj (H.obj (DerivedCategory.Qh.obj P)) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  G.map (ε.app P) ≫ γ.app _ ≫
    DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map
          ((CategoryTheory.homotopyTensorSingleIso B).inv.app P) ≫
        ((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app
          (tensorModelCoefficient B)).app P)


/-- The common map: the tensor counit, the exact-F counit, then the ordinary
comonoidal comparison.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; explicit tensor comparisons.
(blueprint: new-integral-residue-tensor-model) -/
noncomputable def tensorModelMap (B : C) (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : HomotopyCategory C (.up ℤ)) :
    F.leftDerivedFunctor.obj (H.obj (DerivedCategory.Qh.obj P)) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P) :=
  tensorModelMapWith F F.leftDerivedFunctor F.leftDerivedFunctorCounit B H ε P

@[irreducible]
noncomputable def residueExchangeTensorModelTarget :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj (DerivedCategory.Qh.obj P) ⊗
        (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
          (residueExchangeCoefficient ℓ E Y) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) :=
  Functor.tensorModelTargetWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y) P

noncomputable def residueExchangeTensorModelMap :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
        ((residueExchangeRestriction ℓ E Y).obj
          ((residueExchangeReduction ℓ E Y).obj (DerivedCategory.Qh.obj P))) ⟶
      DerivedCategory.Qh.obj
        (((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj
            (Functor.tensorModelCoefficient (residueExchangeOrdinaryCoefficient ℓ E Y)) ⊗
          ((f)^*⟦integralCoeff ℓ E⟧.mapHomotopyCategory (.up ℤ)).obj P) :=
  letI := residueExchangeOrdinaryPullMonoidal ℓ E f
  Functor.tensorModelMapWith (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangeUpperStar (integralCoeff ℓ E) f)
    (residueExchangeUpperStarCounit (integralCoeff ℓ E) f)
    (residueExchangeOrdinaryCoefficient ℓ E Y)
    (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
    (residueExchangeTensorCounit ℓ E Y) P
```

## Users

The union of the explicit declaration users reported by
`tools/downstream.py Sheaf.Paper.IntegralResidueTensorModel --uses
residueExchangeTensorModelTarget` and the analogous command for
`residueExchangeTensorModelMap` is listed below. The tool also reports 41
transitive downstream modules; their interfaces are unaffected because every
existing signature in the model module is identical. Each explicit consumer's
statement denotes the same composite after expansion of the named definitions.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.IntegralResidueScalarCounitModel` | unclaimed | Unchanged statement; unfold the named tensor counit instead of the removed generic-map wrapper. |
| `Sheaf.Paper.IntegralResidueScalarGeometryBridge` | unclaimed | Unchanged statement; the existing isomorphism theorem is applied with full unfolding confined to that application. |
| `Sheaf.Paper.IntegralResidueScalarRouteModel` | unclaimed | Existing statements and their mathematical meaning unchanged; checked against new model. |
| `Sheaf.Paper.IntegralResidueTensorGeometry` | unclaimed | Unchanged statement; the existing isomorphism theorem is applied with full unfolding confined to that application. |
| `Sheaf.Paper.IntegralResidueTensorModel` | unclaimed | Two definition bodies retain named canonical data; signatures unchanged. |
| `Sheaf.Paper.IntegralResidueTensorPullCounitCore` | unclaimed | Existing statements and their mathematical meaning unchanged; checked against new model. |
| `Sheaf.Paper.IntegralResidueTensorPullCounitModel` | unclaimed | Existing statements and their mathematical meaning unchanged; checked against new model. |
| `Sheaf.Paper.IntegralResidueTensorRouteDescent` | A2 | Proof of existing theorem completed. |
| `Sheaf.Paper.IntegralResidueTensorRouteKFlat` | active claim; no adaptation | Existing statements and their mathematical meaning unchanged; checked against new model. |
| `Sheaf.Paper.IntegralResidueTensorRouteModel` | unclaimed | Existing statements and their mathematical meaning unchanged; checked against new model. |

The original `IntegralResidueTensorGeometry` and
`IntegralResidueScalarGeometryBridge` fail at their applications of
`Functor.tensorModelTarget_isIso`: the goal now displays `tensorModelTargetWith`
with `residueExchangeUpperStarCounit`, whereas the theorem concludes
`tensorModelTarget` with the underlying exact-functor counit. Only the local
isomorphism proofs are changed: retain the concrete target unfolding and use
`with_unfolding_all` for the existing generic isomorphism theorem application.
This permits the type conversion through the named derived functor and counit.

The original `IntegralResidueScalarCounitModel` fails at line 287:
`Tactic unfold failed to unfold Functor.tensorModelMap`.
Its definition-unfolding line now unfolds `residueExchangeTensorCounit`
and `Functor.tensorModelMapWith` instead of `Functor.tensorModelMap`. The final naturality rewrite now closes
the goal directly, so the old trailing unfold and identity simplification
commands are removed (leaving them gives `No goals to be solved`).
All three consumer modules are unclaimed; no other group's module is adapted.

## Status

landed 20261017T233159-L-758405 2026-10-17 (merge of deliver/A2/Sheaf.Paper.IntegralResidueTensorRouteDescent)
