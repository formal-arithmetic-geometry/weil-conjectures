/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module

public import Sheaf.SixFunctors.PublishedSystemAmbientPresentation
import Sheaf.Algebra.Homology.CochainTensorModelRigidity

/-! Representative normalization for the transported ambient tensor comparison.
Source: Stacks 03D3, 03EL, 07A4 and 07A7.
(blueprint: lem-sf-published-system-tensor-identification-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
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

/-- The ambient representative rectangle on flat-term K-flat complexes. This is the
flat representative part of the descent argument for arbitrary K-flat complexes.
Source: Stacks 03D3, 03EL, 07A4 and 07A7.
(blueprint: lem-sf-published-system-tensor-identification-representative-flat).

Proof: the constant-section coefficient formulas identify the two direct images,
so their chosen left adjoints and the adjunction units agree after transport.
The ambient ordinary comparison sends the unit of a pure tensor to the tensor
of the two units. On a total summand in degrees p,q, its chain model is the
inverse of this ordinary comparison followed by the pulled-back summand inclusion.
Naturality of the adjunction unit at that inclusion therefore shows that the inverse
chain map satisfies the unit formula defining pullbackTensorSequenceCochain. The
signed total differential is already built into both chain maps. Adjunction and
pure-tensor extensionality in every summand, or the uniqueness clause of that
cochain comparison, identify the inverse chain map with the specified cochain map.
In the ambient model's derived equation, invert the chain isomorphism and cancel
the four model and exact-localization isomorphisms to obtain the forward rectangle.
Finally transport back along sequence_inverse_eq; the induced equality on exact
derived functors is publishedSystemAmbientPullIso, so its component transports
are precisely those in publishedSystemTransportedTensor. K-flat preservation
identifies the target model, independently of its proof witness.
-/
theorem publishedSystemTransportedTensor_normalized_flat {X Y : Scheme.{u}}
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
      (coefficientSequenceCommRingSheaf l E Y) Q)
    (flatP : SemilinearSections.flatTerms.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P)
    (flatQ : SemilinearSections.flatTerms.{u + 1, u, u + 1}
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

/-- Faithful restriction and cancellation, with both comparisons abstract. -/
private theorem tensor_comparison_eq_of_flat_rectangles {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (m n : (pullbackTensorCalculus l E Y).systemClosed.tensor ⋙
        pullbackTensorSequenceDerived l E f ≅
      ((pullbackTensorSequenceDerived l E f).prod
        (pullbackTensorSequenceDerived l E f)) ⋙
        (pullbackTensorCalculus l E X).systemClosed.tensor)
    (hrect : ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) Q)
      (_flatP : SemilinearSections.flatTerms.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (_flatQ : SemilinearSections.flatTerms.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) Q),
      (pullbackTensorSequenceDerived l E f).map
          (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
        m.hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
      (pullbackTensorSequenceDerived l E f).map
          (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
        n.hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
            ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q))) :
    m = n := by
  apply Iso.ext
  obtain ⟨_, _, _, faithful⟩ := SheafOfModules.cochain_tensor_model_rigidity
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y)
  apply (faithful _ inferInstance _ _).1
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨P, Q⟩
  change m.hom.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
    n.hom.app
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)
  let a := (pullbackTensorSequenceDerived l E f).mapIso
    (pullbackTensorSystemModel l E Y P.obj Q.obj P.property.1 Q.property.1)
  let b := (pullbackTensorCalculus l E X).systemClosed.tensor.mapIso (Iso.prod
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app P.obj)
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app Q.obj))
  apply (cancel_epi a.hom).1
  apply (cancel_mono b.hom).1
  simpa only [a, b, Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom,
    Category.assoc] using
    hrect P.obj Q.obj P.property.1 Q.property.1 P.property.2 Q.property.2

set_option linter.unusedVariables false in
/-- The flat representative rectangle determines the transported comparison by
K-flat tensor descent. The conclusion is an equality of tensor comparison isomorphisms,
which is then used to extend the flat representative equation to all independent
K-flat complexes.
Source: Stacks 06YU and 07A4.
(blueprint: lem-sf-published-system-tensor-identification-representative-descent).

Proof: restriction to pairs of flat-term K-flat representatives is faithful by
cochain tensor model rigidity. For each such pair, the assumed forward rectangle
and the canonical comparison's defining rectangle have the same right-hand side.
Cancel the derived image of the source tensor-model isomorphism on the left,
and tensor applied to the two exact-factorization isomorphisms on the right.
The resulting component equalities prove equality of the restricted hom maps;
faithfulness and isomorphism extensionality give the stated equality.
-/
theorem publishedSystemTransportedTensor_eq_of_flat_normalized {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (hflat : ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
        (pullbackTensorSequenceSmall Y)
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) Q)
      (flatP : SemilinearSections.flatTerms.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) P)
      (flatQ : SemilinearSections.flatTerms.{u + 1, u, u + 1}
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
  apply tensor_comparison_eq_of_flat_rectangles l E f
  intro P Q hP hQ flatP flatQ
  refine (hflat P Q hP hQ flatP flatQ).trans ?_
  symm
  exact (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec P Q hP hQ

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
  have heq := publishedSystemTransportedTensor_eq_of_flat_normalized l E f
    (fun P Q hP hQ flatP flatQ ↦
      publishedSystemTransportedTensor_normalized_flat l E f P Q hP hQ flatP flatQ)
  rw [heq]
  exact (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec P Q hP hQ


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
