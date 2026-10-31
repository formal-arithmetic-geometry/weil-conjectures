/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarBalancingChain
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedCoefficientPullbackModel
import all WeilConjectures.AlgebraicGeometry.PulledNormalization.PulledReductionNormalizationComparison
import all WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition

/-! # Scalar chain comparison and its universal counit square

Source: Stacks Project, Tags 03EL, 06YY and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- Apply the ordinary tensor identifications and balancing isomorphism degreewise.
This construction contains no derived functor and no choice of chain map.
Source: Stacks 03EL and 012Z (blueprint: lem-sp-scalar-chain-counit-square). -/
def scalarTensorChainIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (t : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X)
    (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ) :
    ((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj
      (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
        ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≅
    ((scalarMateRestriction φ X).mapHomologicalComplex (.up ℤ)).obj
      ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
        (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) :=
  (NatIso.mapHomologicalComplex
    (Functor.isoWhiskerRight (scalarMateOrdinaryTensorIso φ Y)
      (proEtaleConstantRingPullback A f) ≪≫ t ≪≫
        Functor.isoWhiskerLeft (proEtaleConstantRingPullback A f)
          (scalarMateOrdinaryTensorIso φ X).symm) (.up ℤ)).app P

attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local irreducible] scalarMateOrdinaryTensorIso

/-- The ordinary balanced chain comparison computes the specified scalar mate
in the universal scalar-counit and exact localization coordinates. This square is
valid on every complex; the scalar counits need not be invertible here.

Source: Stacks 03EL, 06YY and 0D6D; Step 2 of the parent normalization argument
(blueprint: lem-sp-scalar-chain-counit-square).

Proof: the balanced pure-section formula determines the ordinary comparison
uniquely. Its transported map is B-linear by the coefficient-action compatibility
in the balancing-chain lemma. Lift it to B-modules. Transpose first through the
scalar adjunction and then through geometric pullback: on a unit section both
maps send x to 1 tensor inverse-image(x). The two adjunction bijections and tensor
universality identify the lifted inverse with the ordinary scalar mate. Apply the
universal derived-counit square for this ordinary mate, then restrict scalars.
The exact restriction/pullback comparison is the termwise localization of beta;
its factorization square transports the result to the displayed coordinates.
The ordinary tensor identifications cancel beta and give scalarTensorChainIso.
This uses the universal counit on arbitrary complexes, not its invertibility.
-/
theorem scalarTensorChainCounitSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (t : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X)
    (ht : IsScalarBalancing φ f t)
    (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ) :
    (proEtaleConstantRingDerivedPullback A f).map
      ((scalarMateRestriction φ Y).mapDerivedCategory.map
          (scalarExtensionFunctorCounit φ Y P) ≫
        (scalarMateRestriction φ Y).mapDerivedCategoryFactors.hom.app
          ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
      (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app
        (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
          ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
      DerivedCategory.Q.map (scalarTensorChainIso φ f t P).hom =
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
          (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨_, hβ, t₀, ht₀, hu, hb, _⟩ := proEtaleScalarBalancingChain φ f
  have het := hu t ht
  rw [← het] at hb
  obtain ⟨s, hs⟩ := balancingLift φ f t hb
  have hes := balancingLift_eq_mate φ f t ht hβ s hs
  let F := proEtaleConstantRingPullback A f
  let H := proEtaleConstantRingPullback B f
  let rY := scalarMateRestriction φ Y
  let rX := scalarMateRestriction φ X
  let EY := reductionChange Y (proEtaleConstantRingMap (T := Y) φ)
  let EX := reductionChange X (proEtaleConstantRingMap (T := X) φ)
  let β := scalarBalancingBeta φ f
  let b := proEtaleRingRestrictionDerivedPullback f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  let θ := directImageScalarPullbackIso φ f
  let N := (EY.mapHomologicalComplex (.up ℤ)).obj P
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let sP : (H.mapHomologicalComplex (.up ℤ)).obj N ≅
      (EX.mapHomologicalComplex (.up ℤ)).obj FP :=
    (NatIso.mapHomologicalComplex s (.up ℤ)).app P
  let βN : (F.mapHomologicalComplex (.up ℤ)).obj
      ((rY.mapHomologicalComplex (.up ℤ)).obj N) ≅
      (rX.mapHomologicalComplex (.up ℤ)).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj N) :=
    (NatIso.mapHomologicalComplex β.symm (.up ℤ)).app N
  have hchain : (scalarTensorChainIso φ f t P).hom =
      βN.hom ≫ (rX.mapHomologicalComplex (.up ℤ)).map sP.hom := by
    apply HomologicalComplex.hom_ext
    intro i
    change F.map ((scalarMateOrdinaryTensorIso φ Y).hom.app (P.X i)) ≫
        t.hom.app (P.X i) ≫
        (scalarMateOrdinaryTensorIso φ X).inv.app (F.obj (P.X i)) =
      β.inv.app (EY.obj (P.X i)) ≫ rX.map (s.hom.app (P.X i))
    have hsi : rX.map (s.hom.app (P.X i)) =
        β.hom.app (EY.obj (P.X i)) ≫
          F.map ((scalarMateOrdinaryTensorIso φ Y).hom.app (P.X i)) ≫
            t.hom.app (P.X i) ≫
              (scalarMateOrdinaryTensorIso φ X).inv.app (F.obj (P.X i)) := hs _
    rw [hsi, Iso.inv_hom_id_app_assoc]
  have hbD : b.inv = (Functor.mapDerivedCategorySquareIso β.symm).hom := by
    change (Functor.mapDerivedCategorySquareIso β).inv = _
    exact (Functor.square_symm_hom β).symm
  have hfac := Functor.exactSquare_fac β.symm N
  rw [← hbD] at hfac
  change b.inv.app (DerivedCategory.Q.obj N) ≫
      rX.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app N) ≫
      rX.mapDerivedCategoryFactors.hom.app
        ((H.mapHomologicalComplex (.up ℤ)).obj N) =
    F.mapDerivedCategory.map (rY.mapDerivedCategoryFactors.hom.app N) ≫
      F.mapDerivedCategoryFactors.hom.app ((rY.mapHomologicalComplex (.up ℤ)).obj N) ≫
      DerivedCategory.Q.map βN.hom at hfac
  have hm := PulledNormalization.derivedMate_rep f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm P
  have hsinv : DerivedCategory.Q.map sP.inv =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (PulledNormalization.ordinaryMate f
          (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
          (proEtaleConstantRing X A) (proEtaleConstantRing X B)
          (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := X) φ)
          (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
          (proEtaleConstantInverseImageMap_naturality f
            (CommRingCat.ofHom (RingHom.ulift φ))).symm) (.up ℤ)).hom.app P) := by
    simp only [sP, hes]
    rfl
  rw [← hsinv] at hm
  change θ.inv.app (DerivedCategory.Q.obj P) ≫
      H.mapDerivedCategory.map (scalarExtensionFunctorCounit φ Y P) ≫
      H.mapDerivedCategoryFactors.hom.app N =
    (directImageScalarExtension φ X).map (F.mapDerivedCategoryFactors.hom.app P) ≫
      scalarExtensionFunctorCounit φ X FP ≫ DerivedCategory.Q.map sP.inv at hm
  have hm' : H.mapDerivedCategory.map (scalarExtensionFunctorCounit φ Y P) ≫
      H.mapDerivedCategoryFactors.hom.app N ≫ DerivedCategory.Q.map sP.hom =
    θ.hom.app (DerivedCategory.Q.obj P) ≫
      (directImageScalarExtension φ X).map (F.mapDerivedCategoryFactors.hom.app P) ≫
      scalarExtensionFunctorCounit φ X FP := by
    apply (cancel_epi (θ.inv.app (DerivedCategory.Q.obj P))).mp
    simp only [Iso.inv_hom_id_app_assoc]
    rw [reassoc_of% hm, ← DerivedCategory.Q.map_comp, sP.inv_hom_id]
    erw [(DerivedCategory.Q : CochainComplex
      (proEtaleRingModules X (proEtaleConstantRing X B)) ℤ ⥤ _).map_id]
    simp only [Category.comp_id]
  have hn := b.inv.naturality (scalarExtensionFunctorCounit φ Y P)
  change F.mapDerivedCategory.map (rY.mapDerivedCategory.map
      (scalarExtensionFunctorCounit φ Y P)) ≫ b.inv.app (DerivedCategory.Q.obj N) =
    b.inv.app ((directImageScalarExtension φ Y).obj (DerivedCategory.Q.obj P)) ≫
      rX.mapDerivedCategory.map
        (H.mapDerivedCategory.map (scalarExtensionFunctorCounit φ Y P)) at hn
  have hr := rX.mapDerivedCategoryFactors.hom.naturality sP.hom
  change rX.mapDerivedCategory.map (DerivedCategory.Q.map sP.hom) ≫
      rX.mapDerivedCategoryFactors.hom.app ((EX.mapHomologicalComplex (.up ℤ)).obj FP) =
    rX.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj N) ≫
      DerivedCategory.Q.map ((rX.mapHomologicalComplex (.up ℤ)).map sP.hom) at hr
  change F.mapDerivedCategory.map
      (rY.mapDerivedCategory.map (scalarExtensionFunctorCounit φ Y P) ≫
        rY.mapDerivedCategoryFactors.hom.app N) ≫
      F.mapDerivedCategoryFactors.hom.app ((rY.mapHomologicalComplex (.up ℤ)).obj N) ≫
      DerivedCategory.Q.map (scalarTensorChainIso φ f t P).hom =
    b.inv.app ((directImageScalarExtension φ Y).obj (DerivedCategory.Q.obj P)) ≫
      rX.mapDerivedCategory.map
        (θ.hom.app (DerivedCategory.Q.obj P) ≫
          (directImageScalarExtension φ X).map (F.mapDerivedCategoryFactors.hom.app P) ≫
          scalarExtensionFunctorCounit φ X FP) ≫
      rX.mapDerivedCategoryFactors.hom.app ((EX.mapHomologicalComplex (.up ℤ)).obj FP)
  rw [hchain, Functor.map_comp, Functor.map_comp, Category.assoc,
    ← reassoc_of% hfac, reassoc_of% hn]
  erw [← hr]
  simp only [← Functor.map_comp_assoc]
  rw [hm']

end AlgebraicGeometry.ProEtale
