/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H7
-/
module

public import Sheaf.SecSmoothPurity.ProEtaleScalarChainCounitSquare

/-! # The coefficient-resolution tensor square on a fixed flat K-flat complex

Source: Stacks Project, Tags 03EL, 06YY and 0D6D.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] SheafOfModules.monoidalCategory

attribute [local irreducible] scalarTensorChainIso scalarExtensionFunctorCounit
  scalarMateDerivedTensorIso proEtaleCanonicalTensorComparison
  scalarMateDerivedCoefficientPullback

/-- Resolve only the degree-zero coefficient to compare tensor pullback with the
ordinary chain comparison on a fixed flat-term K-flat first factor. No geometric
scalar mate or derived restriction/pullback comparison occurs in this statement.

Source: Stacks 06YS and 07A4; Step 3 of the parent normalization argument
(blueprint: lem-sp-scalar-tensor-representative-square).

Proof: choose a flat-term K-flat resolution H of B_Y[0]. Apply the existing
coefficient-resolution square to (P,H). The normalized scalar-to-tensor maps
identify its alpha maps with the scalar counits and ordinary complex tensor
identifications. The ordinary balancing-chain total formula identifies its bottom
map, after the coefficient identification c_B, with scalarTensorChainIso.
On X use F(H) with augmentation F(q) followed by the degree-zero coefficient
identification F(B_Y[0]) -> B_X[0]. Its quasi-isomorphism follows from exactness
and the coefficient isomorphism. Tensoring these augmentations with P and FP
gives quasi-isomorphisms by
K-flatness. Pullback is exact and preserves flat K-flat representatives. Cancel
the localized quasi-isomorphisms in the coefficient-resolution square. Naturality
of the tensor identification with respect to the exact pullback factor on P gives
the stated right-hand scalar-counit coordinates. No flatness of B over A is used.
-/
theorem scalarTensorRepresentativeSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aY : ProEtaleTensorModel Y (proEtaleConstantRing Y A))
    (aX : ProEtaleTensorModel X (proEtaleConstantRing X A))
    (t : scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
      proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X)
    (ht : IsScalarBalancing φ f t)
    (P : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ)
    (hp : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing Y A) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology Y) (R := proEtaleConstantRing Y A) (P.X i)) :
    (proEtaleConstantRingDerivedPullback A f).map
      ((scalarMateDerivedTensorIso φ Y aY).inv.app (DerivedCategory.Q.obj P) ≫
        (scalarMateRestriction φ Y).mapDerivedCategory.map
          (scalarExtensionFunctorCounit φ Y P) ≫
        (scalarMateRestriction φ Y).mapDerivedCategoryFactors.hom.app
          ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
      (proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app
        (((scalarMateRestriction φ Y).mapHomologicalComplex (.up ℤ)).obj
          ((reductionChangeComplex Y (proEtaleConstantRingMap (T := Y) φ)).obj P)) ≫
      DerivedCategory.Q.map (scalarTensorChainIso φ f t P).hom =
    (proEtaleCanonicalTensorComparison f
      (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
      (proEtaleConstantRingComparison f A) aY aX).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (scalarMateCoefficientComplex φ Y)) ≫
      aX.tensor.map (Prod.mkHom
        (𝟙 ((proEtaleConstantRingDerivedPullback A f).obj (DerivedCategory.Q.obj P)))
        (scalarMateDerivedCoefficientPullback φ f).hom) ≫
      (scalarMateDerivedTensorIso φ X aX).inv.app
        ((proEtaleConstantRingDerivedPullback A f).obj (DerivedCategory.Q.obj P)) ≫
      (scalarMateRestriction φ X).mapDerivedCategory.map
        ((directImageScalarExtension φ X).map
          ((proEtaleConstantRingPullback A f).mapDerivedCategoryFactors.hom.app P) ≫
          scalarExtensionFunctorCounit φ X
            (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (scalarMateRestriction φ X).mapDerivedCategoryFactors.hom.app
        ((reductionChangeComplex X (proEtaleConstantRingMap (T := X) φ)).obj
          (((proEtaleConstantRingPullback A f).mapHomologicalComplex (.up ℤ)).obj P)) := by sorry

end AlgebraicGeometry.ProEtale
