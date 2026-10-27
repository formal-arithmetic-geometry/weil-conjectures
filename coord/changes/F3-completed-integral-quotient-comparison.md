# WeilConjectures.completedIntegralQuotientModelComparison

## Reason

Prove the existing theorem by constructing the normalized finite quotient tensor
comparison, assembling the strict tower isomorphism, and applying normalized localization
uniqueness. The preflight command-surface check requires this record for the new namespace,
universe, variable, open and local attribute commands used by the private proof helpers.

The four original public imports and the existing theorem signature are verbatim unchanged.
Every added helper is private and proved. Added imports are proof-only. All new instance and
reducibility attributes are local; the original instance-disabling commands are unchanged.
The additional variables and universes belong to the private generic tensor and category
arguments. A private projection-transition equation lets the main proof keep
`completedIntegralCoefficientSheafUnrestricted` locally irreducible, avoiding repeated
unfolding of the inverse-limit ring; this local attribute is not exported. No existing definition, instance, public signature or target meaning is changed.

## Old

```lean
theorem completedIntegralQuotientModelComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})
    (φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y)
    (hφ : ∀ n : ℕ, φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        integralScalarQuotientSheafMap l E L ι Y n)
    (F : @SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max u (t + 1),
      max u (t + 1) + 1, max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (integralCoefficientAbSheafify.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l L Y) φ
      (integralTowerHasDerivedCategory l E Y) (integralTowerHasDerivedCategory l L Y))
    (C : @PrincipalQuotientCompletion.Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbSheafify.{t, u} Y)
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l L Y)
      (integralTowerHasDerivedCategory l L Y)
      (PrincipalKoszulStrictReplacement.uniformizer l L Y))
    (β : F.E.mapHomologicalComplex (.up ℤ) ⟶ integralScalarComplexFunctor l E L ι Y)
    (hβ :
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((β.app P).f i ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
              (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P)))).f i ≫
          (Pi.π
            (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i).val.app U)
          ((eqToHom (F.obj_eq (P.X i)).symm).val.app U
            ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf φ (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  (φ.hom.app U).hom] x))) =
            integralScalarTensorSection l E L ι Y n (P.X i) U
              ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ),
        (β.app P).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
              (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P)))).v
                i (i - 1) (by omega) = 0)) :
    ∃ c : F.T ⋙ C.completion ≅ integralScalarExtensionOfUniverses l E L ι Y,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        C.unit.app (F.T.obj (DerivedCategory.Q.obj P.obj)) ≫
            c.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P =
          F.ε.app P.obj ≫ DerivedCategory.Q.map (β.app P.obj)
```

The old proof body is `by sorry`.

## New

```lean
theorem completedIntegralQuotientModelComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (Y : AlgebraicGeometry.Scheme.{t})
    (φ : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      completedIntegralCommRingSheafUnrestricted l L Y)
    (hφ : ∀ n : ℕ, φ ≫ completedIntegralCommRingProjectionUnrestricted l L Y n =
      completedIntegralCommRingProjectionUnrestricted l E Y n ≫
        integralScalarQuotientSheafMap l E L ι Y n)
    (F : @SheafOfModules.DerivedChangeOfRingsCochainModel.{t + 1, t, max u (t + 1),
      max u (t + 1) + 1, max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (integralCoefficientAbSheafify.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l L Y) φ
      (integralTowerHasDerivedCategory l E Y) (integralTowerHasDerivedCategory l L Y))
    (C : @PrincipalQuotientCompletion.Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbSheafify.{t, u} Y)
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l L Y)
      (integralTowerHasDerivedCategory l L Y)
      (PrincipalKoszulStrictReplacement.uniformizer l L Y))
    (β : F.E.mapHomologicalComplex (.up ℤ) ⟶ integralScalarComplexFunctor l E L ι Y)
    (hβ :
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ)
        (U : Y.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj U)
        (x : (P.X i).val.obj U),
        (((β.app P).f i ≫
          (CochainComplex.mappingCocone.fst
            (towerTransitionEndomorphism
              (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
              (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P)))).f i ≫
          (Pi.π
            (fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n)) n).f i).val.app U)
          ((eqToHom (F.obj_eq (P.X i)).symm).val.app U
            ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
              (SheafOfModules.changeOfRingsPresheaf φ (P.X i)).presheaf).app U
                (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
                  (φ.hom.app U).hom] x))) =
            integralScalarTensorSection l E L ι Y n (P.X i) U
              ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s) x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ),
        (β.app P).f i ≫
          (CochainComplex.mappingCocone.snd
            (towerTransitionEndomorphism
              (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj P).obj (op n))
              (integralOperationsTowerStep ((integralScalarTowerFunctor l E L ι Y).obj P)))).v
                i (i - 1) (by omega) = 0)) :
    ∃ c : F.T ⋙ C.completion ≅ integralScalarExtensionOfUniverses l E L ι Y,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        C.unit.app (F.T.obj (DerivedCategory.Q.obj P.obj)) ≫
            c.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralScalarExtensionComparisonOfUniverses l E L ι Y).hom.app P =
          F.ε.app P.obj ≫ DerivedCategory.Q.map (β.app P.obj)
```

The proof constructs the tensor, tower and Roos isomorphisms using private proved helpers;
there are zero local holes and no newly deferred results. No signature is weakened or
strengthened. The node's proof, proof dependencies and proof origin follow this argument.

## Users

`tools/downstream.py Sheaf.Paper.CompletedIntegralQuotientModelComparison --uses
completedIntegralQuotientModelComparison` finds the following two declaration users.
The sole direct importing module is `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
Transitive import reachability alone requires no statement adaptation here: the public
interface and public imports are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedIntegralQuotientModelComparison | F3 | Existing theorem proved with its original signature; private proof helpers only. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | unclaimed | Existing application retains exactly the same hypothesis and conclusion; no adaptation. |

The theorem signature and public imports were compared verbatim with the shared source.
The unchanged direct consumer compiled in 34.0 seconds against the replacement, which
compiled in 51.0 seconds in the same ordered sandbox check. The consumer's source and
temporary build artifacts were then removed from the sandbox; it is not part of the delivery.

No definition used by a Challenge target changes, so no statement-meaning review is reopened.
The independent delivery reader reviews the proof route and the new local command scopes.

## Status

landed 20261022T040201-L-2827864 2026-10-22 (merge of deliver/F3/Sheaf.Paper.CompletedIntegralQuotientModelComparison)
