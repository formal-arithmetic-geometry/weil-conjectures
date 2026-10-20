# RingTensorCohomology.exists_mixedTensorUnderlyingHomology

## Reason

The Sheaf module duplicates the adopted source module. Their main theorem signatures
and complete proofs are identical. The only declaration-level difference is that
`mapHomologyIso_hom_comp` is public in Sheaf and private in WeilConjectures.
There are zero direct or transitive importers of the Sheaf module. The upstream
balanced-tensor consumer already imports the upstream module; the upstream affine
pushforward consumer already uses `import all` to access its private helper.
Retire the redundant Sheaf file and attach its DAG node to the existing source theorem.
No source-library declaration, signature, attribute, import or body changes.

## Old

```text
lean.module = Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology
lean.declaration = RingTensorCohomology.exists_mixedTensorUnderlyingHomology
lean.declarations = [RingTensorCohomology.exists_mixedTensorUnderlyingHomology,
                    RingTensorCohomology.mapHomologyIso_hom_comp]
```

The Sheaf file contained these signatures, verbatim:

```lean
theorem mapHomologyIso_hom_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom

theorem exists_mixedTensorUnderlyingHomology
    (R : Type u) [CommRing R] (i : ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    let T := (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex
    ∃ e : ∀ (A : Type u) [CommRing A] [Algebra R A]
        (Q : CochainComplex (ModuleCat.{u} A) ℤ),
      (((T.obj ((restrict R A).obj Q)).obj F).homology i) ≃+
        ((((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F).homology i),
      (∀ (A : Type u) [CommRing A] [Algebra R A]
        (Q : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) x,
        e A Q (HomologicalComplex.homologyMap
          ((T.map ((restrict R A).map (a • 𝟙 Q))).app F) i x) = a • e A Q x) ∧
      (∀ (A Aq : Type u) [CommRing A] [CommRing Aq]
        [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]
        (Q : CochainComplex (ModuleCat.{u} A) ℤ)
        (Qq : CochainComplex (ModuleCat.{u} Aq) ℤ)
        (g : (restrict R A).obj Q ⟶ (restrict R Aq).obj Qq)
        (v : (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ⟶
          (restrict A Aq).obj
            (((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F)),
        (∀ (p q n : ℤ) (h : p + q = n) (x : Q.X p) (y : F.X q),
          v.f n ((HomologicalComplex.ιMapBifunctor Q F
            (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h)
              (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y))) =
          (HomologicalComplex.ιMapBifunctor Qq F
            (ModuleCat.mixedTensor (algebraMap R Aq)) (.up ℤ) p q n h)
              ((g.f p x) ⊗ₜ[Aq] ((1 : Aq) ⊗ₜ[R,algebraMap R Aq] y))) →
        ∀ x,
          (((((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F).sc i).mapHomologyIso
             (ModuleCat.restrictScalars (algebraMap A Aq))).inv
              (e Aq Qq (HomologicalComplex.homologyMap ((T.map g).app F) i x)) =
          HomologicalComplex.homologyMap v i (e A Q x))
```

## New

```text
lean.module = WeilConjectures.Algebra.Homology.MixedTensorUnderlyingHomology
lean.declaration = RingTensorCohomology.exists_mixedTensorUnderlyingHomology
lean.declarations = [RingTensorCohomology.exists_mixedTensorUnderlyingHomology]
```

The retained source signatures, verbatim (the helper remains private):

```lean
private theorem mapHomologyIso_hom_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D] [Limits.HasZeroMorphisms E]
    (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom =
      (S.mapHomologyIso (F ⋙ G)).hom

theorem exists_mixedTensorUnderlyingHomology
    (R : Type u) [CommRing R] (i : ℤ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    let T := (MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map₂CochainComplex
    ∃ e : ∀ (A : Type u) [CommRing A] [Algebra R A]
        (Q : CochainComplex (ModuleCat.{u} A) ℤ),
      (((T.obj ((restrict R A).obj Q)).obj F).homology i) ≃+
        ((((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F).homology i),
      (∀ (A : Type u) [CommRing A] [Algebra R A]
        (Q : CochainComplex (ModuleCat.{u} A) ℤ) (a : A) x,
        e A Q (HomologicalComplex.homologyMap
          ((T.map ((restrict R A).map (a • 𝟙 Q))).app F) i x) = a • e A Q x) ∧
      (∀ (A Aq : Type u) [CommRing A] [CommRing Aq]
        [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]
        (Q : CochainComplex (ModuleCat.{u} A) ℤ)
        (Qq : CochainComplex (ModuleCat.{u} Aq) ℤ)
        (g : (restrict R A).obj Q ⟶ (restrict R Aq).obj Qq)
        (v : (((ModuleCat.mixedTotalTensor (algebraMap R A)).obj Q).obj F) ⟶
          (restrict A Aq).obj
            (((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F)),
        (∀ (p q n : ℤ) (h : p + q = n) (x : Q.X p) (y : F.X q),
          v.f n ((HomologicalComplex.ιMapBifunctor Q F
            (ModuleCat.mixedTensor (algebraMap R A)) (.up ℤ) p q n h)
              (x ⊗ₜ[A] ((1 : A) ⊗ₜ[R,algebraMap R A] y))) =
          (HomologicalComplex.ιMapBifunctor Qq F
            (ModuleCat.mixedTensor (algebraMap R Aq)) (.up ℤ) p q n h)
              ((g.f p x) ⊗ₜ[Aq] ((1 : Aq) ⊗ₜ[R,algebraMap R Aq] y))) →
        ∀ x,
          (((((ModuleCat.mixedTotalTensor (algebraMap R Aq)).obj Qq).obj F).sc i).mapHomologyIso
             (ModuleCat.restrictScalars (algebraMap A Aq))).inv
              (e Aq Qq (HomologicalComplex.homologyMap ((T.map g).app F) i x)) =
          HomologicalComplex.homologyMap v i (e A Q x))
```

The main theorem has exactly the same Lean signature, unchanged. The Sheaf module
is withdrawn through `deleted.txt`; landing leaves an empty module. The source
module and its private helper remain verbatim. The node proof and dependencies
remain accurate for the identical retained proof. No target meaning changes.

## Users

`tools/downstream.py` reports zero downstream modules for each exported declaration;
whole-library import and name searches confirm no Sheaf consumers. The two existing
source consumers below are recorded explicitly to document the retained proof route.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology | B4 | Withdraw duplicate file. |
| WeilConjectures.Algebra.Homology.MixedTensorUnderlyingHomology | unclaimed | Retained verbatim; canonical DAG attachment. |
| WeilConjectures.Algebra.Homology.BalancedTensorUnitModelComparison | unclaimed | Already imports source main theorem; unchanged. |
| WeilConjectures.Algebra.Homology.AffineTildePushforwardHomologyFactorization | unclaimed | Already imports all from source for private helper; unchanged. |

## Status

landed 20261020T141302-L-2031820 2026-10-20 (merge of deliver/B4/Sheaf.Algebra.Homology.MixedTensorUnderlyingHomology)
