# CategoryTheory.RingedSliceEvaluationNormalized

## Reason

Extract the twelve existing definitions into
`Sheaf.Algebra.Homology.RingedSliceEvaluationModels`, publicly re-exported by the original
module. This permits independent comparison-existence and evaluation-coherence theorems
without an import cycle. No declaration, type, universe, visibility, attribute or definition
body changes. The original theorem signature stays byte-for-byte identical. No source-library
file changes. The block below is identical in both locations; a direct text comparison passes.
This is a module relocation, not a new model or a changed meaning of any target.

## Old

In `lean/Sheaf/Algebra/Homology/RingedSliceEvaluationTranspose.lean`:

```lean
/-- Restriction of complexes is the actual termwise slice functor.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def ringedSliceComplexRestriction (U : C) : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ ⥤ CochainComplex
  (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v u}
  RingCat.{max c v u})).obj (A.over U))) ℤ :=
  haveI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).1
  (SheafOfModules.overFunctor.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
      U).mapHomologicalComplex (.up ℤ)

/-- The actual augmentation to the fixed functorial K-injective model.
Source: Stacks 079P (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def coefficientHomAugmentation (I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
  (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    I ⟶ (coefficientHomResolution.{u, c, v} J A).obj I :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  (CochainComplex.toKInjectiveResolution.{max c v u} _).app I

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- The recorded exact derived restriction with its slice ring written as A.over U.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def ringedSliceDerivedRestriction (U : C) [hU : HasDerivedCategory.{w'} (SheafOfModules.{max c v u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
  :
    DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v u}
      RingCat.{max c v u})).obj A)) ⥤ DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose
      (J.over U) (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U))) :=
  letI : HasDerivedCategory.{w'}
      (SheafOfModules.{max c v u}
        (((sheafCompose J
          (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) := hU
  ringedDerivedRestrictionGeneral.{c, v, max c v u, max c v u, w, w'}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U

/-- The fixed localization comparison for exact slice restriction.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def ringedSliceLocalizationIso (U : C) [hU : HasDerivedCategory.{w'} (SheafOfModules.{max c v u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
  :
    DerivedCategory.Q ⋙ ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U ≅
      ringedSliceComplexRestriction.{c, v, u} J A U ⋙ DerivedCategory.Q :=
  haveI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).1
  haveI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).2.1
  haveI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).2.2
  letI : HasDerivedCategory.{w'}
      (SheafOfModules.{max c v u}
        (((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
          hU
  (SheafOfModules.overFunctor.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
      U).mapDerivedCategoryFactors

/-- The canonical identification with an already K-injective target, specified by the
actual augmentation to the fixed replacement. The displayed equation uniquely fixes it.
Source: Stacks 08J7, 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedKInjectiveHomModel (L I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
  (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (κ : (derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
      (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
        DerivedCategory.Q.obj (homComplex (R := A) L I)) : Prop :=
  κ.hom ≫ DerivedCategory.Q.map
    ((homComplexFunctor (R := A)).obj (op L) |>.map
      (coefficientHomAugmentation.{c, v, u} J A I)) =
    (coefficientHomResolutionIso.{u, c, v, w} J A L I).hom

/-- The resolving class preserved by the identity-ring-map localization.
Source: Stacks 0G7E, 07A4 (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceFlatRestriction (U : C) : Prop :=
  ∀ P : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v u}
    RingCat.{max c v u})).obj A)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := A) (P.X n)) →
    CochainComplex.IsKFlatIndependentCoefficients (J := J.over U) (R := A.over U)
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P) ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{max c v, v, max c v u, max c v u} (J := J.over U) (R :=
      A.over U)
      (((ringedSliceComplexRestriction.{c, v, u} J A U).obj P).X n)

set_option maxHeartbeats 600000 in
-- The two-variable representative squares have long dependent endpoint types.
/-- Categorical data for the slice comparisons, normalized by the following predicates.
The tensor comparisons are identity on sheafified pure-tensor summands. The Hom
comparison is identity on local families of maps, and symmetry is the Koszul sign.
Source: Stacks 07A4, 08J9, 08JB, 03EL
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
structure RingedSliceEvaluationComparisons
    {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
    (H : Dᵒᵖ × D ⥤ D) (HU : Eᵒᵖ × E ⥤ E) (r : D ⥤ E)
    (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU) (K : Prop) where
  /-- Restriction of derived tensor, natural simultaneously in both objects. -/
  rho : ∀ L M : D,
    (r).obj (S.tensor.obj (L, M)) ≅
      SU.tensor.obj ((r).obj L, (r).obj M)
  /-- The Hom comparison, with its two components displayed explicitly. -/
  eta : ∀ L M : D,
    (r).obj ((H).obj (op L, M)) ≅
      (HU).obj (op ((r).obj L), (r).obj M)
  /-- Simultaneous naturality of the tensor comparison. -/
  rho_naturality : ∀ (L M L' M' : D) (f : L ⟶ L') (g : M ⟶ M'),
    (r).map (S.tensor.map (f, g)) ≫ (rho L' M').hom =
    (rho L M).hom ≫ SU.tensor.map ((r).map f, (r).map g)
  /-- Contravariant/covariant naturality of the Hom comparison. -/
  eta_naturality : ∀ (L M L' M' : D) (f : L' ⟶ L) (g : M ⟶ M'),
    (r).map ((H).map (f.op, g)) ≫ (eta L' M').hom =
    (eta L M).hom ≫ (HU).map (((r).map f).op, (r).map g)
  /-- Koszul symmetry on the source derived category. -/
  sigma : ∀ L M : D, S.tensor.obj (L, M) ≅ S.tensor.obj (M, L)
  /-- Naturality transports the representative Koszul formula to all derived objects. -/
  sigma_naturality : ∀ (L M L' M' : D) (f : L ⟶ L') (g : M ⟶ M'),
    S.tensor.map (f, g) ≫ (sigma L' M').hom =
      (sigma L M).hom ≫ S.tensor.map (g, f)
  /-- Koszul symmetry on the localized derived category. -/
  sigmaU : ∀ L M : E, SU.tensor.obj (L, M) ≅ SU.tensor.obj (M, L)
  /-- Naturality on the slice also covers objects isomorphic to K-flat models. -/
  sigmaU_naturality : ∀ (L M L' M' : E) (f : L ⟶ L') (g : M ⟶ M'),
    SU.tensor.map (f, g) ≫ (sigmaU L' M').hom =
      (sigmaU L M).hom ≫ SU.tensor.map (g, f)
  /-- Preservation of the specified resolving class. -/
  kflat : K

set_option maxHeartbeats 600000 in
-- Elaborate the dependent representative square without changing the file time limit.
/-- Canonical pure-tensor normalization of rho, including its localization square.
Source: Stacks 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceTensorModel (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v
    u} RingCat.{max c v u})).obj A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q)
    (fP : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := A) (P.X
      n))
    (fQ : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := A) (Q.X
      n)),
    ∃ γ : (ringedSliceComplexRestriction.{c, v, u} J A U).obj
        ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P,
          (ringedSliceComplexRestriction.{c, v, u} J A U).obj Q),
      (∀ (p q k : ℤ) (h : p + q = k) (V : Over U)
        (x : (P.X p).val.obj (op V.left)) (y : (Q.X q).val.obj (op V.left)),
        (γ.hom.f k).val.app (op V)
          (coefficientTensorGenerator.{u, c, v} J A P Q p q k h (op V.left) x y) =
        coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q) p q k h (op V) x y) ∧
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map
          (T.iso J A S P Q hP hQ).hom ≫
        (d.rho (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        SU.tensor.map
          (X := ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj
            P), (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj
            Q)))
          (Y := (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P),
            DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q)))
          ((ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app P,
            (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app Q) =
      (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app
        ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≫
        DerivedCategory.Q.map γ.hom ≫
        (TU.iso (J.over U) (A.over U) SU
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q)
          (d.kflat P hP fP).1 (d.kflat Q hQ fQ).1).hom

set_option maxHeartbeats 600000 in
-- Elaborate the dependent representative square without changing the file time limit.
/-- Canonical local-family normalization of eta, including the fixed K-injective comparisons.
Source: Stacks 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceHomModel (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (_T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (_TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  ∀ (L I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v
    u} RingCat.{max c v u})).obj A)) ℤ) [I.IsKInjective],
    ∃ (κ : (derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
          (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
          DerivedCategory.Q.obj (homComplex (R := A) L I))
      (κU : (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).obj
        (op (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)),
          DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)) ≅
        DerivedCategory.Q.obj (homComplex (R := A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)))
      (γ : (ringedSliceComplexRestriction.{c, v, u} J A U).obj (homComplex (R := A) L I) ≅
        homComplex (R := A.over U) ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)),
      RingedKInjectiveHomModel.{c, v, u, w} J A L I κ ∧
      RingedKInjectiveHomModel.{max c v, v, u, w'} (J.over U) (A.over U)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I) κU ∧
      (∀ (n p q : ℤ) (h : p + n = q) (V : Over U)
        (W : Over V) (x : (L.X p).val.obj (op W.left.left))
        (z : ((homComplex (R := A) L I).X n).val.obj (op V.left)),
        (((coefficientHomComponent.{u, max c v, v} (J.over U) (A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I) n p q h).val.app (op V)
            ((γ.hom.f n).val.app (op V) z)).app (op W)).hom x =
        (((coefficientHomComponent.{u, c, v} J A L I n p q h).val.app (op V.left) z).app
          (op (Over.mk W.hom.left))).hom x) ∧
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map κ.hom ≫
        (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app (homComplex (R := A) L I) ≫
        DerivedCategory.Q.map γ.hom =
      (d.eta (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).hom ≫
        (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).map
          (X := (op ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
            (DerivedCategory.Q.obj L)), (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
            (DerivedCategory.Q.obj I)))
          (Y := (op (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)),
            DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)))
          (((ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).inv.app L).op,
            (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app I) ≫ κU.hom

set_option maxHeartbeats 600000 in
-- Elaborate the dependent representative square without changing the file time limit.
/-- Koszul normalization of the source symmetry on total-tensor representatives.
Source: Stacks 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceKoszulModel (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (_TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v
    u} RingCat.{max c v u})).obj A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q),
    ∃ β : (coefficientTotalTensor.{u, c, v} J A).obj (P, Q) ≅
        (coefficientTotalTensor.{u, c, v} J A).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (V : Cᵒᵖ)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (β.hom.f k).val.app V
          (coefficientTensorGenerator.{u, c, v} J A P Q p q k h V x y) =
        (p * q).negOnePow •
          coefficientTensorGenerator.{u, c, v} J A Q P q p k h' V y x) ∧
      (T.iso J A S P Q hP hQ).hom ≫
        (d.sigma (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map β.hom ≫ (T.iso J A S Q P hQ hP).hom

set_option maxHeartbeats 600000 in
-- Elaborate the dependent representative square without changing the file time limit.
/-- Koszul normalization of the slice symmetry on total-tensor representatives.
Source: Stacks 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceKoszulModelU (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (_T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
    CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U))) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J.over U) (R := A.over U) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J.over U) (R := A.over U) Q),
    ∃ β : (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj (P, Q) ≅
        (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (V : (Over U)ᵒᵖ)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (β.hom.f k).val.app V
          (coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
            P Q p q k h V x y) =
        (p * q).negOnePow •
          coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
            Q P q p k h' V y x) ∧
      (TU.iso (J.over U) (A.over U) SU P Q hP hQ).hom ≫
        (d.sigmaU (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map β.hom ≫ (TU.iso (J.over U) (A.over U) SU Q P hQ hP).hom

/-- The simultaneous representative normalization of all four comparisons.
Source: Stacks 07A4, 08J9, 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceEvaluationNormalized (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  RingedSliceTensorModel.{c, v, u, w, w'} J A U S T SU TU d ∧
  RingedSliceHomModel.{c, v, u, w, w'} J A U S T SU TU d ∧
  RingedSliceKoszulModel.{c, v, u, w, w'} J A U S T SU TU d ∧
  RingedSliceKoszulModelU.{c, v, u, w, w'} J A U S T SU TU d
```

## New

In `lean/Sheaf/Algebra/Homology/RingedSliceEvaluationModels.lean`, publicly imported by the
original module:

```lean
/-- Restriction of complexes is the actual termwise slice functor.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def ringedSliceComplexRestriction (U : C) : CochainComplex (SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ ⥤ CochainComplex
  (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v u}
  RingCat.{max c v u})).obj (A.over U))) ℤ :=
  haveI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).1
  (SheafOfModules.overFunctor.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
      U).mapHomologicalComplex (.up ℤ)

/-- The actual augmentation to the fixed functorial K-injective model.
Source: Stacks 079P (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def coefficientHomAugmentation (I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
  (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    I ⟶ (coefficientHomResolution.{u, c, v} J A).obj I :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  (CochainComplex.toKInjectiveResolution.{max c v u} _).app I

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
  CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- The recorded exact derived restriction with its slice ring written as A.over U.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def ringedSliceDerivedRestriction (U : C) [hU : HasDerivedCategory.{w'} (SheafOfModules.{max c v u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
  :
    DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v u}
      RingCat.{max c v u})).obj A)) ⥤ DerivedCategory (SheafOfModules.{max c v u} ((sheafCompose
      (J.over U) (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U))) :=
  letI : HasDerivedCategory.{w'}
      (SheafOfModules.{max c v u}
        (((sheafCompose J
          (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) := hU
  ringedDerivedRestrictionGeneral.{c, v, max c v u, max c v u, w, w'}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U

/-- The fixed localization comparison for exact slice restriction.
Source: Stacks 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def ringedSliceLocalizationIso (U : C) [hU : HasDerivedCategory.{w'} (SheafOfModules.{max c v u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
  :
    DerivedCategory.Q ⋙ ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U ≅
      ringedSliceComplexRestriction.{c, v, u} J A U ⋙ DerivedCategory.Q :=
  haveI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).1
  haveI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).2.1
  haveI := (ringedOverFunctor_exactGeneral.{c, v, max c v u, max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A) U).2.2
  letI : HasDerivedCategory.{w'}
      (SheafOfModules.{max c v u}
        (((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A).over U)) :=
          hU
  (SheafOfModules.overFunctor.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)
      U).mapDerivedCategoryFactors

/-- The canonical identification with an already K-injective target, specified by the
actual augmentation to the fixed replacement. The displayed equation uniquely fixes it.
Source: Stacks 08J7, 08JB (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedKInjectiveHomModel (L I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J
  (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (κ : (derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
      (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
        DerivedCategory.Q.obj (homComplex (R := A) L I)) : Prop :=
  κ.hom ≫ DerivedCategory.Q.map
    ((homComplexFunctor (R := A)).obj (op L) |>.map
      (coefficientHomAugmentation.{c, v, u} J A I)) =
    (coefficientHomResolutionIso.{u, c, v, w} J A L I).hom

/-- The resolving class preserved by the identity-ring-map localization.
Source: Stacks 0G7E, 07A4 (blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceFlatRestriction (U : C) : Prop :=
  ∀ P : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v u}
    RingCat.{max c v u})).obj A)) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := A) (P.X n)) →
    CochainComplex.IsKFlatIndependentCoefficients (J := J.over U) (R := A.over U)
      ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P) ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{max c v, v, max c v u, max c v u} (J := J.over U) (R :=
      A.over U)
      (((ringedSliceComplexRestriction.{c, v, u} J A U).obj P).X n)

set_option maxHeartbeats 600000 in
-- The two-variable representative squares have long dependent endpoint types.
/-- Categorical data for the slice comparisons, normalized by the following predicates.
The tensor comparisons are identity on sheafified pure-tensor summands. The Hom
comparison is identity on local families of maps, and symmetry is the Koszul sign.
Source: Stacks 07A4, 08J9, 08JB, 03EL
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
structure RingedSliceEvaluationComparisons
    {D : Type a} [Category.{x} D] {E : Type b} [Category.{y} E]
    (H : Dᵒᵖ × D ⥤ D) (HU : Eᵒᵖ × E ⥤ E) (r : D ⥤ E)
    (S : CoefficientClosedStructure H) (SU : CoefficientClosedStructure HU) (K : Prop) where
  /-- Restriction of derived tensor, natural simultaneously in both objects. -/
  rho : ∀ L M : D,
    (r).obj (S.tensor.obj (L, M)) ≅
      SU.tensor.obj ((r).obj L, (r).obj M)
  /-- The Hom comparison, with its two components displayed explicitly. -/
  eta : ∀ L M : D,
    (r).obj ((H).obj (op L, M)) ≅
      (HU).obj (op ((r).obj L), (r).obj M)
  /-- Simultaneous naturality of the tensor comparison. -/
  rho_naturality : ∀ (L M L' M' : D) (f : L ⟶ L') (g : M ⟶ M'),
    (r).map (S.tensor.map (f, g)) ≫ (rho L' M').hom =
    (rho L M).hom ≫ SU.tensor.map ((r).map f, (r).map g)
  /-- Contravariant/covariant naturality of the Hom comparison. -/
  eta_naturality : ∀ (L M L' M' : D) (f : L' ⟶ L) (g : M ⟶ M'),
    (r).map ((H).map (f.op, g)) ≫ (eta L' M').hom =
    (eta L M).hom ≫ (HU).map (((r).map f).op, (r).map g)
  /-- Koszul symmetry on the source derived category. -/
  sigma : ∀ L M : D, S.tensor.obj (L, M) ≅ S.tensor.obj (M, L)
  /-- Naturality transports the representative Koszul formula to all derived objects. -/
  sigma_naturality : ∀ (L M L' M' : D) (f : L ⟶ L') (g : M ⟶ M'),
    S.tensor.map (f, g) ≫ (sigma L' M').hom =
      (sigma L M).hom ≫ S.tensor.map (g, f)
  /-- Koszul symmetry on the localized derived category. -/
  sigmaU : ∀ L M : E, SU.tensor.obj (L, M) ≅ SU.tensor.obj (M, L)
  /-- Naturality on the slice also covers objects isomorphic to K-flat models. -/
  sigmaU_naturality : ∀ (L M L' M' : E) (f : L ⟶ L') (g : M ⟶ M'),
    SU.tensor.map (f, g) ≫ (sigmaU L' M').hom =
      (sigmaU L M).hom ≫ SU.tensor.map (g, f)
  /-- Preservation of the specified resolving class. -/
  kflat : K

set_option maxHeartbeats 600000 in
-- Elaborate the dependent representative square without changing the file time limit.
/-- Canonical pure-tensor normalization of rho, including its localization square.
Source: Stacks 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceTensorModel (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v
    u} RingCat.{max c v u})).obj A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q)
    (fP : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := A) (P.X
      n))
    (fQ : ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v u, max c v u} (J := J) (R := A) (Q.X
      n)),
    ∃ γ : (ringedSliceComplexRestriction.{c, v, u} J A U).obj
        ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≅
      (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P,
          (ringedSliceComplexRestriction.{c, v, u} J A U).obj Q),
      (∀ (p q k : ℤ) (h : p + q = k) (V : Over U)
        (x : (P.X p).val.obj (op V.left)) (y : (Q.X q).val.obj (op V.left)),
        (γ.hom.f k).val.app (op V)
          (coefficientTensorGenerator.{u, c, v} J A P Q p q k h (op V.left) x y) =
        coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q) p q k h (op V) x y) ∧
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map
          (T.iso J A S P Q hP hQ).hom ≫
        (d.rho (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        SU.tensor.map
          (X := ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj
            P), (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj (DerivedCategory.Q.obj
            Q)))
          (Y := (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P),
            DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q)))
          ((ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app P,
            (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app Q) =
      (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app
        ((coefficientTotalTensor.{u, c, v} J A).obj (P, Q)) ≫
        DerivedCategory.Q.map γ.hom ≫
        (TU.iso (J.over U) (A.over U) SU
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q)
          (d.kflat P hP fP).1 (d.kflat Q hQ fQ).1).hom

set_option maxHeartbeats 600000 in
-- Elaborate the dependent representative square without changing the file time limit.
/-- Canonical local-family normalization of eta, including the fixed K-injective comparisons.
Source: Stacks 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceHomModel (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (_T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (_TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  ∀ (L I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v
    u} RingCat.{max c v u})).obj A)) ℤ) [I.IsKInjective],
    ∃ (κ : (derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
          (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
          DerivedCategory.Q.obj (homComplex (R := A) L I))
      (κU : (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).obj
        (op (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)),
          DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)) ≅
        DerivedCategory.Q.obj (homComplex (R := A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)))
      (γ : (ringedSliceComplexRestriction.{c, v, u} J A U).obj (homComplex (R := A) L I) ≅
        homComplex (R := A.over U) ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)),
      RingedKInjectiveHomModel.{c, v, u, w} J A L I κ ∧
      RingedKInjectiveHomModel.{max c v, v, u, w'} (J.over U) (A.over U)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
        ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I) κU ∧
      (∀ (n p q : ℤ) (h : p + n = q) (V : Over U)
        (W : Over V) (x : (L.X p).val.obj (op W.left.left))
        (z : ((homComplex (R := A) L I).X n).val.obj (op V.left)),
        (((coefficientHomComponent.{u, max c v, v} (J.over U) (A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I) n p q h).val.app (op V)
            ((γ.hom.f n).val.app (op V) z)).app (op W)).hom x =
        (((coefficientHomComponent.{u, c, v} J A L I n p q h).val.app (op V.left) z).app
          (op (Over.mk W.hom.left))).hom x) ∧
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map κ.hom ≫
        (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app (homComplex (R := A) L I) ≫
        DerivedCategory.Q.map γ.hom =
      (d.eta (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I)).hom ≫
        (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).map
          (X := (op ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
            (DerivedCategory.Q.obj L)), (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
            (DerivedCategory.Q.obj I)))
          (Y := (op (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)),
            DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)))
          (((ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).inv.app L).op,
            (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app I) ≫ κU.hom

set_option maxHeartbeats 600000 in
-- Elaborate the dependent representative square without changing the file time limit.
/-- Koszul normalization of the source symmetry on total-tensor representatives.
Source: Stacks 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceKoszulModel (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (_TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v
    u} RingCat.{max c v u})).obj A)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q),
    ∃ β : (coefficientTotalTensor.{u, c, v} J A).obj (P, Q) ≅
        (coefficientTotalTensor.{u, c, v} J A).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (V : Cᵒᵖ)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (β.hom.f k).val.app V
          (coefficientTensorGenerator.{u, c, v} J A P Q p q k h V x y) =
        (p * q).negOnePow •
          coefficientTensorGenerator.{u, c, v} J A Q P q p k h' V y x) ∧
      (T.iso J A S P Q hP hQ).hom ≫
        (d.sigma (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map β.hom ≫ (T.iso J A S Q P hQ hP).hom

set_option maxHeartbeats 600000 in
-- Elaborate the dependent representative square without changing the file time limit.
/-- Koszul normalization of the slice symmetry on total-tensor representatives.
Source: Stacks 07A4, 08J9 and 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceKoszulModelU (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (_T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
    CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U))) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J.over U) (R := A.over U) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J.over U) (R := A.over U) Q),
    ∃ β : (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj (P, Q) ≅
        (coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U)).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (V : (Over U)ᵒᵖ)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (β.hom.f k).val.app V
          (coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
            P Q p q k h V x y) =
        (p * q).negOnePow •
          coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
            Q P q p k h' V y x) ∧
      (TU.iso (J.over U) (A.over U) SU P Q hP hQ).hom ≫
        (d.sigmaU (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
      DerivedCategory.Q.map β.hom ≫ (TU.iso (J.over U) (A.over U) SU Q P hQ hP).hom

/-- The simultaneous representative normalization of all four comparisons.
Source: Stacks 07A4, 08J9, 08JB
(blueprint: lem-weil-pbc-ringed-slice-evaluation-transpose). -/
def RingedSliceEvaluationNormalized (U : C)
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U)) : Prop :=
  RingedSliceTensorModel.{c, v, u, w, w'} J A U S T SU TU d ∧
  RingedSliceHomModel.{c, v, u, w, w'} J A U S T SU TU d ∧
  RingedSliceKoszulModel.{c, v, u, w, w'} J A U S T SU TU d ∧
  RingedSliceKoszulModelU.{c, v, u, w, w'} J A U S T SU TU d
```

## Users

The downstream closure was computed with `tools/downstream.py`; all public transitive imports
of the original module remain public through the new model module. Every declaration name
remains identical. No consumer adaptation is needed. The exact-use search for
`RingedSliceEvaluationNormalized` finds the item, `ModuleObjectRingedSiteDerivedComparison`
and `RationalSliceCompletedEvaluation`; the table also includes the full downstream closure.
All listed modules are unclaimed at inspection time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose | M1 | Identical public declarations and public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeArrowLocalization | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.DeltaRestriction | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.InternalSliceDerivedHomComparison | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.RingedDerivedSliceData | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.RingedDerivedSliceLocalization | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.RingedPushforwardCompletion | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.RingedSliceDerivedAdjunction | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.RingedSliceDerivedComparisons | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.RingedSliceDerivedMate | unclaimed | Identical public declarations and public import closure; no adaptation. |
| Sheaf.Paper.RingedSliceLocalizationModel | unclaimed | Identical public declarations and public import closure; no adaptation. |

## Status

landed 20261020T221240-L-4163737 2026-10-20 (merge of deliver/M1/Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose)
