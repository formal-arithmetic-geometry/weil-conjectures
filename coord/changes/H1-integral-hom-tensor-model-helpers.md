# WeilConjectures.IntegralHom.integralReductionTower_koszul_model

## Reason

The assigned theorem needs two distinct constructions: a tensor model of ordinary
integral reduction, and K-injectivity after tensoring with the two-term free
coefficient complex. Record these separately, prove the latter, and assemble the
assigned theorem from the former and the existing Hom localization factorization.
No existing statement, definition, instance, or public import changes.

## Old

Neither of the following declarations existed. The assigned module contained only
its original public theorem, with a `sorry` proof.

## New

```lean
theorem integralReductionTower_koszul_model
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P G N : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (e : DerivedCategory.Q.obj N ≅ DerivedCategory.Q.obj G) :
    Nonempty (integralReductionTower l E Y D hl P ≅
      principalKoszulTower (completedIntegralCommRingSheaf l E Y D hl)
        (PrincipalKoszulStrictReplacement.uniformizer l E Y) ⋙
          (totalTensor.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj N ⋙
            DerivedCategory.Q)
```

```lean
theorem isKInjective_tensor_principalKoszul
    (Y : AlgebraicGeometry.Scheme.{t})
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (a : (SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)).sections)
    (I : CochainComplex (Modules.{t, u} Y R) ℤ) [I.IsKInjective] (n : ℕ) :
    (((totalTensor.{t, u} Y R).obj I).obj (principalKoszul R a n)).IsKInjective
```

The first theorem remains the sole new hole. The second has a complete cone proof.
The assigned theorem retains its original signature and public import; it gains
private proof imports and a proved private naturality lemma.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralHomReductionTowerTensorModels | H1 | Uses the two new helpers in its proof; its statement is unchanged. |

The new modules have no existing consumers. Existing consumers of the item see
its unchanged declaration and unchanged public imports. No forced adaptation is needed.

## Status

landed 20261028T034803-L-3545264 2026-10-28 (merge of deliver/H1/Sheaf.Paper.IntegralHomReductionTowerTensorModels)
