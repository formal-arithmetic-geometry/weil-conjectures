/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison

/-! # Ordinary tensor pullback composition after localization

Source: Stacks Project, cohomology.tex, Tags 079U and 0D5S.
(blueprint: lem-sc-pullback-tensor-total-composition-localized).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory MonoidalCategory
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Localization of the ordinary tensor/composition square.
Source: Stacks Project, cohomology.tex, Tags 079U and 0D5S.
(blueprint: lem-sc-pullback-tensor-total-composition-localized).

Proof: the localization tensor map is natural in both complex inputs. Apply
this naturality to the ordinary composition mate on P and N. The two ordinary
chain maps from f*g*Tot(P,N) to Tot((fg)*P,(fg)*N) agree on each (p,q)
summand: transpose by the pinned adjunctions, and evaluate on pure tensor
sections. The composite adjunction unit inserts the same successive unit
images in both factors. Tensor universality proves the module equality, and
joint epimorphy of total-complex summand inclusions proves the chain equality.
More explicitly, write b_R for the chain composition mate and Tot(b_P,b_N)
for its induced map on total tensor complexes. The chain equality is
f*(psi.hom);theta.hom;Tot(b_P,b_N) = b_Tot;phi.hom. The mate identity
identifies the direct adjunction unit followed by b_R with the successive
adjunction unit, transported along pushforwardComp. Thus the transposed
summand maps both send s tensor t to the tensor of those successive unit
images. Pullbacks are left adjoints, so they preserve the coproducts of
summands; the mapped inclusions are jointly epimorphic as required above.
Naturality gives (Q(b_P) tensor Q(b_N));mu_direct =
mu_successive;Q(Tot(b_P,b_N)). Precompose the chain equality with
theta.inv followed by f*(psi.inv), then localize and substitute it here.
No K-flatness is required. Identity arrows, zero complexes and empty schemes
satisfy the same universal-property calculation.
-/
theorem pullback_tensor_total_composition_localized
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (ψ : ((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Z P N) ≅
      pullbackTensorTotal Y
        (((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj N))
    (hψ :
      letI := pullbackDescentModuleTensor Z
      letI := pullbackDescentModuleTensor Y
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (g)).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor (SheafOfModules.{u}
      (moduleRings Z.toRingedSpace))) (.up ℤ) p q n h) ≫
          ψ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (g)))
          (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback (g)).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
            (.up ℤ) p q n h)
    (θ : ((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Y (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up
      ℤ)).obj P) (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ≅
      pullbackTensorTotal X
        (((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P))
        (((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)))
    (hθ :
      letI := pullbackDescentModuleTensor Y
      letI := pullbackDescentModuleTensor X
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (f)).map
            (HomologicalComplex.ιMapBifunctor (((Scheme.Modules.tensorPullback
      g).mapHomologicalComplex (.up ℤ)).obj P) (((Scheme.Modules.tensorPullback
      g).mapHomologicalComplex (.up ℤ)).obj N) (curriedTensor (SheafOfModules.{u} (moduleRings
      Y.toRingedSpace))) (.up ℤ) p q n h) ≫
          θ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (f)))
          ((((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P).X p)
      ((((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N).X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P))
            (((Scheme.Modules.tensorPullback (f)).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N))
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
            (.up ℤ) p q n h)
    (φ : ((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Z P N) ≅
      pullbackTensorTotal X
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N))
    (hφ :
      letI := pullbackDescentModuleTensor Z
      letI := pullbackDescentModuleTensor X
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (f ≫ g)).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (f ≫ g)))
          (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
            (.up ℤ) p q n h) :
    let β := Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm) (.up ℤ)
    (((DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map (β.hom.app
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)).obj P))) ⊗ₘ
      ((DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map (β.hom.app
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)).obj N)))) ≫
      pullbackTensorModelMap X (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex
      (.up ℤ)).obj P) (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up
      ℤ)).obj N) =
    pullbackTensorModelMap X (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up
      ℤ)).obj (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P))
      (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj N)) ≫
      DerivedCategory.Q.map θ.inv ≫
      DerivedCategory.Q.map
        (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)).map ψ.inv) ≫
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map (β.hom.app
        ((HomotopyCategory.quotient
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)).obj
          (pullbackTensorTotal Z P N))) ≫
      DerivedCategory.Q.map φ.hom := by sorry

end AlgebraicGeometry
