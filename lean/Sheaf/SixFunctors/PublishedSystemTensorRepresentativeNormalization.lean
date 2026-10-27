/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.SixFunctors.PublishedSystemAmbientPresentation

/-! Representative normalization for the transported ambient tensor comparison.
Source: Stacks 03D3, 03EL, 07A4 and 07A7.
(blueprint: lem-sf-published-system-tensor-identification-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus HasDerivedCategory.standard
  WeilConjectures.CoefficientClosedStructure.tensor
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures

/-- Generic component cancellation for transport of a tensor comparison along an
isomorphism of inverse-image functors. -/
theorem tensor_comparison_transport_hom_eq
    {A B : Type*} [Category A] [Category B]
    (TA : A × A ⥤ A) (TB : B × B ⥤ B)
    (F G : A ⥤ B) (d : F ≅ G)
    (m : TA ⋙ F ≅ (F.prod F) ⋙ TB)
    (n : TA ⋙ G ≅ (G.prod G) ⋙ TB)
    (h : (Functor.isoWhiskerLeft TA d ≪≫ n ≪≫
        Functor.isoWhiskerRight (NatIso.prod d d).symm TB) = m) :
    ∀ M N, d.hom.app (TA.obj (M, N)) ≫ n.hom.app (M, N) =
      m.hom.app (M, N) ≫ TB.map (Prod.mkHom (d.hom.app M) (d.hom.app N)) := by
  intro M N
  have hh := congrArg (fun e ↦ e.hom.app (M, N)) h
  calc
    d.hom.app (TA.obj (M, N)) ≫ n.hom.app (M, N) =
        d.hom.app (TA.obj (M, N)) ≫ n.hom.app (M, N) ≫
          TB.map ((NatIso.prod d d).inv.app (M, N)) ≫
          TB.map ((NatIso.prod d d).hom.app (M, N)) := by
      rw [← TB.map_comp]
      simp [NatIso.prod]
    _ = (Functor.isoWhiskerLeft TA d ≪≫ n ≪≫
        Functor.isoWhiskerRight (NatIso.prod d d).symm TB).hom.app (M, N) ≫
          TB.map ((NatIso.prod d d).hom.app (M, N)) := by
      simp only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
        NatTrans.comp_app, NatIso.prod, Iso.symm_hom, Category.assoc]
    _ = m.hom.app (M, N) ≫
          TB.map ((NatIso.prod d d).hom.app (M, N)) := by
      rw [hh]
    _ = m.hom.app (M, N) ≫ TB.map (Prod.mkHom (d.hom.app M) (d.hom.app N)) := by
      rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Transport the ambient tensor comparison back along the specified inverse-image
identification. Its representative normalization is the remaining chain-level step
in the proof of the published-system tensor identification. -/
noncomputable def publishedSystemTransportedTensor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorCalculus l E Y).systemClosed.tensor ⋙
        pullbackTensorSequenceDerived l E f ≅
      ((pullbackTensorSequenceDerived l E f).prod
        (pullbackTensorSequenceDerived l E f)) ⋙
        (pullbackTensorCalculus l E X).systemClosed.tensor :=
  (isoWhiskerLeft (pullbackTensorCalculus l E Y).systemClosed.tensor
      (publishedSystemAmbientPullIso l E f)) ≪≫
    (publishedSystemAmbientData l E).tensor f ≪≫
    (Functor.isoWhiskerRight
      (NatIso.prod (publishedSystemAmbientPullIso l E f)
        (publishedSystemAmbientPullIso l E f)).symm
      (pullbackTensorCalculus l E X).systemClosed.tensor)

/-- On flat K-flat representatives, the transported ambient comparison has the
same inverse representative rectangle as `pullbackTensorSystemComparison`.
Source: Stacks 03D3, 03EL, 07A4 and 07A7, representative normalization of the
pullback tensor comparison. The proof identifies the ordinary pure-tensor map,
its signed total complex map, and the exact-localization model maps on every
summand; the `sequence_inverse_eq` transport removes the ambient presentation.
(blueprint: lem-sf-published-system-tensor-identification-representative).
-/
theorem publishedSystemTransportedTensor_normalized {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y)
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y)
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) Q) :
    (pullbackTensorSequenceDerived l E f).map
        (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
      (publishedSystemTransportedTensor l E f).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)) ≫
      (pullbackTensorSystemModel l E X _ _
        (pullbackTensorSequenceGood l E f P hP)
        (pullbackTensorSequenceGood l E f Q hQ)).hom := by
  sorry

/-- The representative normalization determines the transported comparison by the
existing uniqueness theorem. -/
theorem publishedSystemTransportedTensor_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (hn : ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) Q),
      (pullbackTensorSequenceDerived l E f).map
          (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
        (publishedSystemTransportedTensor l E f).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P, Q)) ≫
        (pullbackTensorSystemModel l E X _ _
          (pullbackTensorSequenceGood l E f P hP)
          (pullbackTensorSequenceGood l E f Q hQ)).hom) :
    publishedSystemTransportedTensor l E f =
      pullbackTensorSystemComparison l E f := by
  exact (pullbackTensorSystemComparison_existsUnique l E f).unique
    hn (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec


end WeilConjectures
