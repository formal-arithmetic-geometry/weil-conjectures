# AlgebraicGeometry.Scheme.lisse_finite_level_etale_model_comparison

## Reason

The supplied etale D was unrelated to the actual pullback or its local algebraic models.
This was already marked STATEMENT-DISPUTED by the previous worker. With E=N=0, a nonzero
bounded constant D on a nonempty scheme with nonzero finite coefficients satisfies every
old hypothesis but cannot have the asserted realization isomorphism to zero.
The parent used a helper which chose D=0 regardless of the actual pullback.

The correction is the classical derived descent of a specified proetale object K
(Stacks Tags 09B1 and 099Z). The parent's unchanged statement is recovered by defining K
as the inverse fixed realization of its actual pullback, proving its cohomological
properties, descending K, and composing the comparison with the scalar-equivalence counit.
No target signature or definition used by a target is changed.

## Old

```lean
theorem lisse_finite_level_etale_model_comparison
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (U : Y.ProEt) (n : ℕ)
    (N : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (D : DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (hDbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj D))
    (hDlisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor _ q).obj D))
    (hmodels : ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj N)) :
    Nonempty ((lisseTowerFixedRealization (U.hom ≫ g) d n).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) U.left).mapDerivedCategory.obj D) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj N)
```

## New

```lean
theorem lisse_finite_level_etale_model_comparison
    (Z : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (K : DerivedCategory (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
    (hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hcohom : ∀ q : ℤ, ∃ G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsFiniteLocallyConstantSheaf G ∧
        Nonempty ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Z).obj G ≅
          (DerivedCategory.homologyFunctor _ q).obj K)) :
    ∃ D : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj D)) ∧
      (∀ q : ℤ, IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor _ q).obj D)) ∧
      Nonempty ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} Λ) Z).mapDerivedCategory.obj D ≅ K)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LisseFiniteLevelEtaleModelComparison | N1 | Correct false statement and prove the replacement by the classical derived counit. |
| Sheaf.Paper.LisseFiniteLevelEtaleModel | unclaimed | Preserve signature and public imports; construct K from the actual pullback, apply the new cohomology lemma and corrected comparison, then compose the scalar counit. |

A complete downstream-name scan found only these two modules referring to the declaration.
The sole DAG citer is new-lem-weil-pbc-lisse-finite-level-etale-model: its conclusion holds
with the adapted proof in this packet. The direct importer of that parent is
Sheaf.Paper.LisseFiniteLevelEtaleDescent; its source and signature need no change.
Public imports of both existing modules stay identical. All other transitive consumers
continue to use the unchanged parent theorem, so their statements are unchanged.

## Status

landed 20261028T055722-L-800494 2026-10-28 (merge of deliver/N1/Sheaf.Paper.LisseFiniteLevelEtaleModelComparison)
