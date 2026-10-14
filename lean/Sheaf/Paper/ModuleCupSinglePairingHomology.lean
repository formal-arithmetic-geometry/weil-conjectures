/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.Paper.ModuleCupDerivedClassComparison
public import Sheaf.Paper.ModuleCupNaiveDerivedCompatibility

/-! # Homology formula for one realized resolution pairing

Source: Stacks Project, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-single-pairing-homology)
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {X : Scheme.{u}}
  [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

@[instance_reducible] local instance cupSingleFormulaCommRing :
    CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  cupRealizationHasColimitsOfSize cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

attribute [local irreducible] Functor.rightDerivedFunctor
  moduleCup_globalComparison moduleCup_comparisonNatTrans

set_option maxHeartbeats 1000000 in
-- Matching the sheaf tensor instances needs extra definitional equality work.
/-- A realized pairing evaluates to the derived tensor of its input classes.
Source: Stacks Project, Tag 0FKU, global diagram following Lemma 20.31.3.
(blueprint: lem-sc-module-cup-single-pairing-homology)
Proof: use C.on_cycles to lift the three nonnegative cycles to the extended
integer complexes. The two input lifts give a tensor cycle by P.on_cycles.
The summand formula for ν and ht identify its image under ν followed by global
t with the output lift, since extendXIso is invertible and iCycles is monic.
Naturality of the homology factorization of Q therefore identifies the localized
output class with homology of Q(ν followed by global t) on this tensor class.
Postcompose hdiagram with R(Q(t)) and R(inv target augmentation). Naturality
of the comparison unit moves Q(t) across the diagram. Naturality hμ moves the
inverse input augmentations across μ. The definition of D.derivedMap cancels
these inverse augmentations against the input augmentations. Apply homology
and P.natural to obtain the displayed identity, using C.on_cycles for all
three class identifications. This argument works in degree zero and for zero
cycles and zero modules, and requires no flatness of the resolution complexes. -/
theorem moduleCup_single_pairing_homology
    (C : CupDerivedClassComparison X) (P : CupDerivedHomologyTensor Γ(X, ⊤))
    (μ : ∀ A B : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B ⟶
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj (A ⊗ B))
    (hμ : ∀ (A A' B B' : DerivedCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))) (f : A ⟶ A') (g : B ⟶ B'),
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map f ⊗ₘ
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map g) ≫
        μ A' B' = μ A B ≫
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map (f ⊗ₘ g))
    {F G : X.Modules} (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (ht : D.Realizes t)
    (ν : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj D.left.integerComplex ⊗
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj D.right.integerComplex ⟶
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (D.left.integerComplex ⊗ D.right.integerComplex))
    (hν : ∀ (i j n : ℤ) (h : i + j = n)
      (x : Γ(D.left.integerComplex.X i, ⊤)) (y : Γ(D.right.integerComplex.X j, ⊤)),
      (ν.f n).hom
        ((HomologicalComplex.ιTensorObj
          (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D.left.integerComplex)
          (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj D.right.integerComplex) i j n h).hom
          (TensorProduct.tmul Γ(X, ⊤) x y)) =
        (HomologicalComplex.ιTensorObj D.left.integerComplex D.right.integerComplex
          i j n h).val.app (op ⊤) (tmulSection x y))
    (hdiagram :
      (moduleCup_globalComparison X D.left.integerComplex ⊗ₘ
        moduleCup_globalComparison X D.right.integerComplex) ≫
          μ (DerivedCategory.Q.obj D.left.integerComplex)
            (DerivedCategory.Q.obj D.right.integerComplex) ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
            (Functor.LaxMonoidal.μ DerivedCategory.Q
              D.left.integerComplex D.right.integerComplex) =
      Functor.LaxMonoidal.μ DerivedCategory.Q
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj D.left.integerComplex)
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj D.right.integerComplex) ≫
        DerivedCategory.Q.map ν ≫
        moduleCup_globalComparison X (D.left.integerComplex ⊗ D.right.integerComplex))
    (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    C.equiv (F ⊗ G) (p + q) (D.target.class (p + q) c) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) ((p + q : ℕ) : ℤ)).map
        (μ ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
            (D.derivedMap t))
        (P.pair (cupDerivedSections X F) (cupDerivedSections X G) p q
          (C.equiv F p (D.left.class p a)) (C.equiv G q (D.right.class q b))) := by sorry
end
end AlgebraicGeometry.Scheme.Modules
