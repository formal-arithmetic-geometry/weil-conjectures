# AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_derived_square_comparison

## Reason

Expose the proved representative-square component of the assigned native-data theorem,
including uniqueness. The original theorem and its signature are preserved; its coherence
obligation is explicitly disputed. No new unproved theorem is introduced.

## Old

No declaration with this new name existed. The original public imports included:

```lean
public import Sheaf.Paper.NativeWeilTensorRingedModelNaturality
public import Sheaf.Paper.NativeWeilTensorRingedDerivedSquareOrdinary
```

## New

ModelNaturality becomes a proof-only import. The unused DerivedSquareOrdinary import
is removed. The existing native_data signature is unchanged. The new proved signature is:

```lean
theorem native_weil_tensor_ringed_derived_square_comparison
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    (T : ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤
      ProEtaleWeilSheaf k₀ l X)
    [T.Additive] [∀ P, (T.obj P).Additive]
    (adj : T ⊣₂ ihomBifunctor k₀ l X)
    (e : Functor.uncurry.obj T ⋙
        Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ≅
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).prod
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) ⋙
          Functor.uncurry.obj
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    [∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ, P.HasMapBifunctor Q T]
    (chain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
      ((Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj
          (CochainComplex.mapBifunctor P Q T) ≅
        ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q))
    (hchain : ∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (p q n : ℤ) (h : p + q = n),
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)).map
          (HomologicalComplex.ιMapBifunctor P Q T (.up ℤ) p q n h) ≫
            (chain P Q).hom.f n =
        e.hom.app (P.X p, Q.X q) ≫ HomologicalComplex.ιMapBifunctor
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (.up ℤ) p q n h)
    (b : NativeWeilTensorRingedBridge k₀ l X)
    [HasDerivedCategory.{u + 2} (RingedTensorModules.{u + 1, u + 1, u + 1} b.J b.R)]
    (A : NativeWeilRingedTensorComplexes b T adj)
    (M : NativeClosedHomModels k₀ l X)
    (S : CoefficientClosedStructure M.ordinaryHom)
    (SB : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u + 1, u + 1, u + 2} b.J b.R))
    (TB : CoefficientTensorModels.{u + 1, u + 1, u + 1, u + 2} b.J b.R SB)
    (βB : @SymmetricCategory _ _ SB.monoidal)
    (cB : RingedDerivedTensorCoherence b.J b.R SB TB βB)
    (ordinaryModel : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (_ : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P),
          S.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≅
            DerivedCategory.Q.obj
              (ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q))
    (hnaturality : ∀ (P Q P' Q' : CochainComplex (ProEtale.AdicSheaf l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
          (hP : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P)
          (hP' : NativeOrdinaryKFlat l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P')
          (f : P ⟶ P') (g : Q ⟶ Q'),
        S.tensor.map
            (X := (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P))
            (Y := (DerivedCategory.Q.obj Q', DerivedCategory.Q.obj P'))
            (Prod.mkHom (DerivedCategory.Q.map g) (DerivedCategory.Q.map f)) ≫
            (ordinaryModel P' Q' hP').hom =
          (ordinaryModel P Q hP).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorMap f g
              (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
              (.up ℤ))) :
    ∃! t : @MonoidalCategory.tensor _ _ (nativeWeilRingedMonoidal b SB) ⋙
        nativeForget k₀ l X ≅
      (nativeForget k₀ l X).prod (nativeForget k₀ l X) ⋙ S.tensor,
    (∀ (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
      (hP : NativeTensorKFlat k₀ l X T P),
    (nativeForget k₀ l X).map (nativeWeilRingedTensorModel b T adj A SB TB βB cB P Q hP).hom ≫
        ((Endofunctor.IsoAlgebra.forget
          (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app
            (CochainComplex.mapBifunctor P Q T)) ≫
        DerivedCategory.Q.map (chain P Q).hom =
      t.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) ≫
        S.tensor.map
          (X := ((nativeForget k₀ l X).obj (DerivedCategory.Q.obj Q),
            (nativeForget k₀ l X).obj (DerivedCategory.Q.obj P)))
          (Y := (DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q),
            DerivedCategory.Q.obj
            (((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)))
          (Prod.mkHom
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app Q)
            ((Endofunctor.IsoAlgebra.forget
              (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors.hom.app P)) ≫
        (ordinaryModel
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Endofunctor.IsoAlgebra.forget
            (WeilSheaf.frobeniusPullback k₀ l X)).mapHomologicalComplex (.up ℤ)).obj Q)
          (native_weil_tensor_forget_kflat k₀ l X T chain P hP)).hom)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeWeilTensorRingedDerivedSquare | unclaimed in the inspected claims | Existing theorem unchanged; it imports DerivedSquareOrdinary itself. Compile unchanged against this packet. |

The new declaration has no existing consumer. No source-library interface changes.
All irreducibility attributes used to control elaboration are local to this file.

## Status

landed 20261027T205927-L-1634956 2026-10-27 (merge of deliver/E6/Sheaf.Paper.NativeWeilTensorRingedDerivedSquareNative)
