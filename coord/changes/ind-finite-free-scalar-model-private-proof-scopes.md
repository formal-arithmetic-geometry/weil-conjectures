# SheafOfModules.IndFiniteFree.ind_finite_free_scalar_model

## Reason

The stage-3 preflight classifies new `variable`, `section`, and `omit` commands as
potential public-interface changes and requests this record. They scope private,
fully proved helpers for the independent-universe tensor comparison. No existing
signature, definition body, public import, or persistent option is changed.

The two `variable {R : Sheaf J CommRingCat.{r}} in` commands each scope one private
naturality lemma. `section OrdinaryComparison` scopes `{R S : Sheaf J CommRingCat.{r}}`;
its nested section scopes `{R₀ B₀ : Sheaf J RingCat.{r}}`. Both sections close before
`extensionPure` and the original `{R S}`, `{φ}`, and derived-category variables.
The three `omit ... in` commands affect only private proved theorems. The heartbeat
option is also local to one private theorem. None of these commands leaks to the
existing declarations. The supplied algebra-colimit witness is explicitly retained
in the proof to avoid an unused-variable warning without changing its binder.

## Old

The existing theorem signature, verbatim:

```lean
theorem ind_finite_free_scalar_model
    {I : Type r} [SmallCategory I] [IsFiltered I]
    [HasExactColimitsOfShape I (Modules R)]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit c) (hcModules : IsColimit ((algebraModules R).mapCocone c))
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty ((algebraModules R).obj (D.obj i) ≅
      ∏ᶜ fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R)))
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom) :
    ∃ (_ : PreservesFiniteLimits m.E) (_ : PreservesFiniteColimits m.E)
      (_ : PreservesFiniteLimits (restriction c.pt.hom))
      (_ : PreservesFiniteColimits (restriction c.pt.hom)),
      (∀ (A B : CochainComplex (Modules R) ℤ) (f : A ⟶ B),
        QuasiIso f → QuasiIso ((m.E.mapHomologicalComplex (.up ℤ)).map f)) ∧
      IsIso m.ε ∧
      (∀ (P A : CochainComplex (Modules R) ℤ) (p : P ⟶ A) [QuasiIso p],
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        ∃ e : m.T.obj (DerivedCategory.Q.obj A) ≅
            DerivedCategory.Q.obj ((m.E.mapHomologicalComplex (.up ℤ)).obj P),
          e.hom = m.T.map (inv (DerivedCategory.Q.map p)) ≫ m.ε.app P ∧
          e.hom ≫ DerivedCategory.Q.map ((m.E.mapHomologicalComplex (.up ℤ)).map p) =
            m.ε.app A) ∧
      ∃ κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
          (restriction c.pt.hom).mapHomologicalComplex (.up ℤ),
        Normalized D c m κ ∧
        (∀ (A B : CochainComplex (Modules R) ℤ) (f : A ⟶ B),
          QuasiIso f → QuasiIso ((tensorColimit D).map f)) ∧
        (∃ (KD : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R))
          (θ : DerivedCategory.Q ⋙ KD ≅ tensorColimit D ⋙ DerivedCategory.Q)
          (κD : KD ≅ m.T ⋙ (restriction c.pt.hom).mapDerivedCategory),
          ∀ A : CochainComplex (Modules R) ℤ,
            θ.hom.app A ≫ DerivedCategory.Q.map (κ.hom.app A) =
              κD.hom.app (DerivedCategory.Q.obj A) ≫
                (restriction c.pt.hom).mapDerivedCategory.map (m.ε.app A) ≫
                (restriction c.pt.hom).mapDerivedCategoryFactors.hom.app
                  ((m.E.mapHomologicalComplex (.up ℤ)).obj A)) ∧
        CoefficientCompatible.{u, v, r, wR, wS, wT} D c m κ
```

There were no private proof sections before this delivery.

## New

The theorem signature remains verbatim:

```lean
theorem ind_finite_free_scalar_model
    {I : Type r} [SmallCategory I] [IsFiltered I]
    [HasExactColimitsOfShape I (Modules R)]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit c) (hcModules : IsColimit ((algebraModules R).mapCocone c))
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty ((algebraModules R).obj (D.obj i) ≅
      ∏ᶜ fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R)))
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom) :
    ∃ (_ : PreservesFiniteLimits m.E) (_ : PreservesFiniteColimits m.E)
      (_ : PreservesFiniteLimits (restriction c.pt.hom))
      (_ : PreservesFiniteColimits (restriction c.pt.hom)),
      (∀ (A B : CochainComplex (Modules R) ℤ) (f : A ⟶ B),
        QuasiIso f → QuasiIso ((m.E.mapHomologicalComplex (.up ℤ)).map f)) ∧
      IsIso m.ε ∧
      (∀ (P A : CochainComplex (Modules R) ℤ) (p : P ⟶ A) [QuasiIso p],
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        ∃ e : m.T.obj (DerivedCategory.Q.obj A) ≅
            DerivedCategory.Q.obj ((m.E.mapHomologicalComplex (.up ℤ)).obj P),
          e.hom = m.T.map (inv (DerivedCategory.Q.map p)) ≫ m.ε.app P ∧
          e.hom ≫ DerivedCategory.Q.map ((m.E.mapHomologicalComplex (.up ℤ)).map p) =
            m.ε.app A) ∧
      ∃ κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
          (restriction c.pt.hom).mapHomologicalComplex (.up ℤ),
        Normalized D c m κ ∧
        (∀ (A B : CochainComplex (Modules R) ℤ) (f : A ⟶ B),
          QuasiIso f → QuasiIso ((tensorColimit D).map f)) ∧
        (∃ (KD : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R))
          (θ : DerivedCategory.Q ⋙ KD ≅ tensorColimit D ⋙ DerivedCategory.Q)
          (κD : KD ≅ m.T ⋙ (restriction c.pt.hom).mapDerivedCategory),
          ∀ A : CochainComplex (Modules R) ℤ,
            θ.hom.app A ≫ DerivedCategory.Q.map (κ.hom.app A) =
              κD.hom.app (DerivedCategory.Q.obj A) ≫
                (restriction c.pt.hom).mapDerivedCategory.map (m.ε.app A) ≫
                (restriction c.pt.hom).mapDerivedCategoryFactors.hom.app
                  ((m.E.mapHomologicalComplex (.up ℤ)).obj A)) ∧
        CoefficientCompatible.{u, v, r, wR, wS, wT} D c m κ
```

All ten existing definition/abbreviation signatures and bodies are byte-identical
to the current source. The only added declarations are private proved helpers;
the theorem body now uses them. No target meaning changes and no statement review
is reopened.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.IndFiniteFreeScalarModel --uses` with
all eleven public names reports zero downstream modules and only this module as
a user of each declaration. This check is about interface adaptation only: the
DAG parents and the item's attachment remain present and are not withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.IndFiniteFreeScalarModel` | U9 | Existing API unchanged; private proof scaffolding and complete theorem proof added. |

No other module is adapted, including modules held by another group.

## Status

landed 20261021T140935-L-2777756 2026-10-21 (merge of deliver/U9/Sheaf.Algebra.Homology.IndFiniteFreeScalarModel)
