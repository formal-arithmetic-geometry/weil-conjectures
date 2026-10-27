# proEtaleScalarTensorNormalization

## Reason

Remove the unused prime, primality and primary-torsion assumptions so that the published tensor/pullback normalization applies to the arbitrary finite commutative coefficient rings in proEtaleScalarMateNormalization. Its entire balanced-generator, K-flat counit and resolving-descent proof applies without them. No map or conclusion changes. This is a strengthening of an existing intermediate theorem, not a target change. No new hole is introduced; its existing proof obligation and proof plan remain.

The edge cases include zero rings, zero modules, nonflat ring maps, arbitrary scheme maps and finite rings with mixed prime characteristic (for example Z/6Z). The balancing and quasi-isomorphism arguments use no characteristic or torsion assumption. Source: Stacks sites-cohomology.tex Tag 07A4 (lemma-pullback-tensor-product) and Tags 06YS, 06YT; sites-modules.tex Tag 03EL (lemma-tensor-product-pullback).

## Old

```lean
theorem proEtaleScalarTensorNormalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y A))
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X A)) :
    (∀ K : proEtaleDerivedCategory Y A,
      (proEtaleConstantRingDerivedPullback A f).map
          ((scalarMateDerivedTensorIso φ Y aY).inv.app K) ≫
        (proEtaleRingRestrictionDerivedPullback f
          (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm).inv.app
              ((directImageScalarExtension φ Y).obj K) ≫
        (scalarMateRestriction φ X).mapDerivedCategory.map
          ((directImageScalarPullbackIso φ f).hom.app K) ≫
        (scalarMateDerivedTensorIso φ X aX).hom.app
          ((proEtaleConstantRingDerivedPullback A f).obj K) =
      (proEtaleCanonicalTensorComparison f
        (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
        (proEtaleConstantRingComparison f A) aY aX).hom.app
          (K, DerivedCategory.Q.obj (scalarMateCoefficientComplex φ Y)) ≫
        aX.tensor.map (Prod.mkHom
          (𝟙 ((proEtaleConstantRingDerivedPullback A f).obj K))
          (scalarMateDerivedCoefficientPullback φ f).hom)) ∧
    (∀ P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ,
      CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
        (R := proEtaleConstantRing Y A) P →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (P.X i)) →
      ∃ t :
        ((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj
          (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
            ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≅
        ((scalarMateRestriction φ X).mapHomologicalComplex (.up ℤ)).obj
          ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
            (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)),
        (∀ (i : ℤ) (V : Y.ProEt)
          (x : (P.X i).val.obj (Opposite.op V))
          (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op V)),
          (t.hom.f i).val.app (Opposite.op ((proEtaleBaseChange f).obj V))
            (((proEtaleConstantRingAdjunction A f).unit.app
              ((scalarMateRestriction φ Y).obj
                ((reductionChange Y (proEtaleConstantRingMap (T := Y) φ)).obj
                  (P.X i)))).val.app (Opposite.op V)
                    (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ)
                      (P.X i) (Opposite.op V) s x)) =
          reductionTensorSection X (proEtaleConstantRingMap (T := X) φ)
            ((proEtaleConstantRingPullback A f).obj (P.X i))
            (Opposite.op ((proEtaleBaseChange f).obj V))
            (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
              (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
                (Opposite.op V)) s)
            (((proEtaleConstantRingAdjunction A f).unit.app (P.X i)).val.app
              (Opposite.op V) x)) ∧
        (proEtaleConstantRingDerivedPullback A f).map
          ((scalarMateRestriction φ Y).mapDerivedCategory.map
              (scalarExtensionFunctorCounit φ Y P) ≫
            (scalarMateRestriction φ Y).mapDerivedCategoryFactors.hom.app
              ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
          (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app
            (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
              ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
          DerivedCategory.Q.map t.hom =
        (proEtaleRingRestrictionDerivedPullback f
          (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm).inv.app
              ((directImageScalarExtension φ Y).obj (DerivedCategory.Q.obj P)) ≫
          (scalarMateRestriction φ X).mapDerivedCategory.map
            ((directImageScalarPullbackIso φ f).hom.app (DerivedCategory.Q.obj P) ≫
              (directImageScalarExtension φ X).map
                ((proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
              scalarExtensionFunctorCounit φ X
                (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
          (scalarMateRestriction φ X).mapDerivedCategoryFactors.hom.app
            ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
              (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)))
```

## New

```lean
theorem proEtaleScalarTensorNormalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y A))
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X A)) :
    (∀ K : proEtaleDerivedCategory Y A,
      (proEtaleConstantRingDerivedPullback A f).map
          ((scalarMateDerivedTensorIso φ Y aY).inv.app K) ≫
        (proEtaleRingRestrictionDerivedPullback f
          (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm).inv.app
              ((directImageScalarExtension φ Y).obj K) ≫
        (scalarMateRestriction φ X).mapDerivedCategory.map
          ((directImageScalarPullbackIso φ f).hom.app K) ≫
        (scalarMateDerivedTensorIso φ X aX).hom.app
          ((proEtaleConstantRingDerivedPullback A f).obj K) =
      (proEtaleCanonicalTensorComparison f
        (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
        (proEtaleConstantRingComparison f A) aY aX).hom.app
          (K, DerivedCategory.Q.obj (scalarMateCoefficientComplex φ Y)) ≫
        aX.tensor.map (Prod.mkHom
          (𝟙 ((proEtaleConstantRingDerivedPullback A f).obj K))
          (scalarMateDerivedCoefficientPullback φ f).hom)) ∧
    (∀ P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ,
      CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
        (R := proEtaleConstantRing Y A) P →
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
        (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (P.X i)) →
      ∃ t :
        ((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj
          (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
            ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≅
        ((scalarMateRestriction φ X).mapHomologicalComplex (.up ℤ)).obj
          ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
            (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)),
        (∀ (i : ℤ) (V : Y.ProEt)
          (x : (P.X i).val.obj (Opposite.op V))
          (s : (proEtaleConstantRing Y B).obj.obj (Opposite.op V)),
          (t.hom.f i).val.app (Opposite.op ((proEtaleBaseChange f).obj V))
            (((proEtaleConstantRingAdjunction A f).unit.app
              ((scalarMateRestriction φ Y).obj
                ((reductionChange Y (proEtaleConstantRingMap (T := Y) φ)).obj
                  (P.X i)))).val.app (Opposite.op V)
                    (reductionTensorSection Y (proEtaleConstantRingMap (T := Y) φ)
                      (P.X i) (Opposite.op V) s x)) =
          reductionTensorSection X (proEtaleConstantRingMap (T := X) φ)
            ((proEtaleConstantRingPullback A f).obj (P.X i))
            (Opposite.op ((proEtaleBaseChange f).obj V))
            (((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
              (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)).hom.app
                (Opposite.op V)) s)
            (((proEtaleConstantRingAdjunction A f).unit.app (P.X i)).val.app
              (Opposite.op V) x)) ∧
        (proEtaleConstantRingDerivedPullback A f).map
          ((scalarMateRestriction φ Y).mapDerivedCategory.map
              (scalarExtensionFunctorCounit φ Y P) ≫
            (scalarMateRestriction φ Y).mapDerivedCategoryFactors.hom.app
              ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
          (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app
            (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
              ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
          DerivedCategory.Q.map t.hom =
        (proEtaleRingRestrictionDerivedPullback f
          (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm).inv.app
              ((directImageScalarExtension φ Y).obj (DerivedCategory.Q.obj P)) ≫
          (scalarMateRestriction φ X).mapDerivedCategory.map
            ((directImageScalarPullbackIso φ f).hom.app (DerivedCategory.Q.obj P) ≫
              (directImageScalarExtension φ X).map
                ((proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
              scalarExtensionFunctorCounit φ X
                (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
          (scalarMateRestriction φ X).mapDerivedCategoryFactors.hom.app
            ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
              (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Remove unused prime/torsion binders; preserve conclusion and proof obligation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Remove the three now-obsolete explicit arguments at its sole theorem call. Public signature unchanged. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Transitive consumer from tools/downstream.py; no direct use; unchanged. |
| Sheaf.Paper.ProEtaleScalarMateNormalization | H1 | New direct consumer, using its first conjunct for arbitrary finite rings. |

No Challenge target statement is changed. The coefficient operations and their normalization are unchanged.

## Status

landed 20261025T101113-L-3657498 2026-10-25 (merge of deliver/H1/Sheaf.Paper.ProEtaleScalarMateNormalization)
