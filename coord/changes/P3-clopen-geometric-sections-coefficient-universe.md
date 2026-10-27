# AlgebraicGeometry.Etale.clopenGeometricSections_derivedEvaluation

## Reason

The standalone global-sections equivalence clause did not constrain the universe
of `ModuleCat A`. Lean generalized it independently of the coefficient universe
used throughout the derived-category calculation. The recorded geometric-point
module equivalence uses `ModuleCat.{u + 1} A`; this is also the universe of the
module sheaves in the theorem's other clauses. Pin this one occurrence explicitly.
No target signature or source-library declaration changes.

## Old

```lean
theorem clopenGeometricSections_derivedEvaluation :
    letI : IsOpenImmersion j := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).1
    letI : IsClosedImmersion j :=
      (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.1
    let hv := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.2
    let Z := Scheme.openComplementOfIsClosedImmersion j
    let E := D((j)_!open[ModuleCat A])
    let B := clopenEtaleDerivedSum A v hv
    let Ki := fun K i ↦ (D((s i)^*[ModuleCat A])).obj (E.obj K)
    (∀ J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat A)) ℤ,
      J.IsKInjective ↔
        (∀ i, CochainComplex.IsKInjective
          ((((s i)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J)) ∧
        CochainComplex.IsKInjective
          ((((Z.ι)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J)) ∧
    (∀ C : CochainComplex (Sheaf (U).smallEtaleTopology (ModuleCat A)) ℤ,
      ∃ (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat A)) ℤ)
        (q : (((j)_!open[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj C ⟶ J),
        QuasiIso q ∧ J.IsKInjective ∧
          IsZero ((((Z.ι)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J) ∧
          (∀ i, CochainComplex.IsKInjective
            ((((s i)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J))) ∧
    (∀ K, IsZero ((D((Z.ι)^*[ModuleCat A])).obj (E.obj K))) ∧
    (∀ K, IsIso (clopenGeometricEvaluation A r s hs (E.obj K))) ∧
    (∀ K L (f : K ⟶ L),
      (R((r)_*[ModuleCat A])).map (E.map f) ≫
          clopenGeometricEvaluation A r s hs (E.obj L) =
        clopenGeometricEvaluation A r s hs (E.obj K) ≫
          CategoryTheory.Limits.Pi.map (fun i ↦ (D((s i)^*[ModuleCat A])).map (E.map f))) ∧
    ((sheafSections (P).smallEtaleTopology (ModuleCat A)).obj
      (op (Scheme.Etale.mk (𝟙 P)))).IsEquivalence ∧
    ∃ (e : ∀ K, B.obj K ≅ ⨁ (Ki K))
      (δ : ∀ K, (D((r)^*[ModuleCat A])).obj (B.obj K) ⟶ E.obj K),
      (∀ K i, biproduct.ι (Ki K) i ≫ (e K).inv =
        clopenGeometricSumInjection A (t i) j (s i) (Sigma.ι_desc s i) v hv
          (by rw [← Category.assoc, Sigma.ι_desc]; exact hs i) K) ∧
      (∀ K L (f : K ⟶ L), B.map f ≫ (e L).hom =
        (e K).hom ≫ biproduct.map (fun i ↦ (D((s i)^*[ModuleCat A])).map (E.map f))) ∧
      (∀ K i, (D((s i)^*[ModuleCat A])).map (δ K) =
        (clopenSectionPullbackIso A r (s i) (hs i)).hom.app (B.obj K) ≫
          (e K).hom ≫ biproduct.π (Ki K) i) ∧
      (∀ K, (D((Z.ι)^*[ModuleCat A])).map (δ K) = 0) ∧
      (∀ K L (f : K ⟶ L),
        (D((r)^*[ModuleCat A])).map (B.map f) ≫ δ L = δ K ≫ E.map f) ∧
      (∀ K,
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).homEquiv _ _ (δ K) ≫
            clopenGeometricEvaluation A r s hs (E.obj K) =
          (e K).hom ≫ Pi.lift (fun i ↦ biproduct.π (Ki K) i)) ∧
      (∀ K, IsIso
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).homEquiv _ _ (δ K)))
```

## New

```lean
theorem clopenGeometricSections_derivedEvaluation :
    letI : IsOpenImmersion j := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).1
    letI : IsClosedImmersion j :=
      (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.1
    let hv := (clopenGeometricSections_union Ω r s hclosed hdisjoint hs).2.2
    let Z := Scheme.openComplementOfIsClosedImmersion j
    let E := D((j)_!open[ModuleCat A])
    let B := clopenEtaleDerivedSum A v hv
    let Ki := fun K i ↦ (D((s i)^*[ModuleCat A])).obj (E.obj K)
    (∀ J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat A)) ℤ,
      J.IsKInjective ↔
        (∀ i, CochainComplex.IsKInjective
          ((((s i)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J)) ∧
        CochainComplex.IsKInjective
          ((((Z.ι)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J)) ∧
    (∀ C : CochainComplex (Sheaf (U).smallEtaleTopology (ModuleCat A)) ℤ,
      ∃ (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat A)) ℤ)
        (q : (((j)_!open[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj C ⟶ J),
        QuasiIso q ∧ J.IsKInjective ∧
          IsZero ((((Z.ι)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J) ∧
          (∀ i, CochainComplex.IsKInjective
            ((((s i)^*[ModuleCat A]).mapHomologicalComplex (.up ℤ)).obj J))) ∧
    (∀ K, IsZero ((D((Z.ι)^*[ModuleCat A])).obj (E.obj K))) ∧
    (∀ K, IsIso (clopenGeometricEvaluation A r s hs (E.obj K))) ∧
    (∀ K L (f : K ⟶ L),
      (R((r)_*[ModuleCat A])).map (E.map f) ≫
          clopenGeometricEvaluation A r s hs (E.obj L) =
        clopenGeometricEvaluation A r s hs (E.obj K) ≫
          CategoryTheory.Limits.Pi.map (fun i ↦ (D((s i)^*[ModuleCat A])).map (E.map f))) ∧
    ((sheafSections (P).smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (op (Scheme.Etale.mk (𝟙 P)))).IsEquivalence ∧
    ∃ (e : ∀ K, B.obj K ≅ ⨁ (Ki K))
      (δ : ∀ K, (D((r)^*[ModuleCat A])).obj (B.obj K) ⟶ E.obj K),
      (∀ K i, biproduct.ι (Ki K) i ≫ (e K).inv =
        clopenGeometricSumInjection A (t i) j (s i) (Sigma.ι_desc s i) v hv
          (by rw [← Category.assoc, Sigma.ι_desc]; exact hs i) K) ∧
      (∀ K L (f : K ⟶ L), B.map f ≫ (e L).hom =
        (e K).hom ≫ biproduct.map (fun i ↦ (D((s i)^*[ModuleCat A])).map (E.map f))) ∧
      (∀ K i, (D((s i)^*[ModuleCat A])).map (δ K) =
        (clopenSectionPullbackIso A r (s i) (hs i)).hom.app (B.obj K) ≫
          (e K).hom ≫ biproduct.π (Ki K) i) ∧
      (∀ K, (D((Z.ι)^*[ModuleCat A])).map (δ K) = 0) ∧
      (∀ K L (f : K ⟶ L),
        (D((r)^*[ModuleCat A])).map (B.map f) ≫ δ L = δ K ≫ E.map f) ∧
      (∀ K,
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).homEquiv _ _ (δ K) ≫
            clopenGeometricEvaluation A r s hs (E.obj K) =
          (e K).hom ≫ Pi.lift (fun i ↦ biproduct.π (Ki K) i)) ∧
      (∀ K, IsIso
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat A) r).homEquiv _ _ (δ K)))
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.ClopenGeometricSectionsDerivedEvaluation
--uses AlgebraicGeometry.Etale.clopenGeometricSections_derivedEvaluation`
reported zero downstream modules and only the declaration's own module as a
textual user. The pending DAG parent still needs this theorem; it is preserved.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClopenGeometricSectionsDerivedEvaluation | P3 | Coefficient universe pinned in the sections clause; both proofs completed. |

## Status

landed 20261023T151914-L-422515 2026-10-23 (merge of deliver/P3/Sheaf.AlgebraicGeometry.ClopenGeometricSectionsDerivedEvaluation)
