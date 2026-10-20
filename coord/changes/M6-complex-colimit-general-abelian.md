# CategoryTheory.complex_colimit_homotopyColimit

## Reason

Expose the existing proved telescope construction for arbitrary abelian categories with exact sequential colimits. The current site-specific theorem requires covering pullbacks absent from this item's hypotheses. The module is unclaimed.

## Old

No declaration of this name. Existing declarations are unchanged.

## New

```lean
theorem complex_colimit_homotopyColimit
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableCoproducts A]
    [HasFilteredColimitsOfSize.{0, 0} A] [AB5OfSize.{0, 0} A]
    (E : ℕ ⥤ CochainComplex A ℤ)
    (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (L : Cocone E) (hL : IsColimit L)
    (u : B.pt ⟶ B.pt)
    (hu : ∀ n : ℕ, B.inj n ≫ u =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (q : B.pt ⟶ L.pt) (hq : ∀ n : ℕ, B.inj n ≫ q = L.ι.app n) :
    ∃ p : mappingCone u ⟶ L.pt,
      mappingCone.inr u ≫ p = q ∧
      (mappingCone.inl u).comp (Cochain.ofHom p) (add_zero _) = 0 ∧
      QuasiIso p ∧
      Nonempty (IsColimit
        (Cofan.mk (DerivedCategory.Q.obj B.pt)
          (fun n : ℕ ↦ DerivedCategory.Q.map (B.inj n)))) ∧
      ∃ e : DerivedCategory.Q.obj (mappingCone u) ≅ DerivedCategory.Q.obj L.pt,
        e.hom = DerivedCategory.Q.map p ∧
        DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u) ∈
          distTriang (DerivedCategory A) ∧
        Triangle.mk (DerivedCategory.Q.map u) (DerivedCategory.Q.map q)
          (e.inv ≫ (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u)).mor₃) ∈
          distTriang (DerivedCategory A) ∧
        ∃ h : HasCountableCoproducts (DerivedCategory A),
          @IsSequentialHomotopyColimit
            (DerivedCategory A) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj (mappingCone u)) ∧
          @IsSequentialHomotopyColimit
            (DerivedCategory A) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj L.pt)
```

The existing node lem-kun-complex-colimit-hocolim also attaches this proved general API
through lean.declarations. Its original primary declaration and mathematical statement stay
unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope | M6 | Uses the new theorem for a Grothendieck module-sheaf category. |
| Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit | unclaimed | Adds a proved declaration; all original signatures, visibility and proofs stay unchanged. |

The downstream --uses query finds zero existing uses of the new name. Existing consumers see an additive API extension and require no changes. No target statement or definition changes.

## Status

landed 20261020T122112-L-477212 2026-10-20 (merge of deliver/M6/Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope)
