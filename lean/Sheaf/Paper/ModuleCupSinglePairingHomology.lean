/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.ModuleCupDerivedClassComparison

/-! # Evaluating one realized pairing in derived homology

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

attribute [local instance] cupRealizationMonoidalCategory cupRealizationSymmetricCategory
  cupRealizationHasColimitsOfSize cupRealizationMonoidalPreadditive cupRealizationMonoidalClosed
  cupRealizationHasFunctorialFlatResolution cupRealizationIsGrothendieckAbelian
  cupRealizationDerivedMonoidal cupRealizationQLax

local instance : CommRing ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) :=
  inferInstanceAs (CommRing Γ(X, ⊤))

attribute [local irreducible] Functor.rightDerivedFunctor moduleCup_globalComparison

/-- A single realized pairing is evaluated by the tensor operation on derived
homology and the supplied global cup diagram.
Source: Stacks Project, Tag 0FKU, Lemma 20.31.3 and its global specialization.
(blueprint: lem-sc-module-cup-single-pairing-homology)
Proof: use J.on_cycles to extend the two input cycles and the output cycle to
integer degrees. Apply hdiagram to the two integer resolution complexes.
Postcompose it with RΓ(Q(t)) and RΓ(inv target.derivedAugmentation).
Naturality of the comparison moves Q(t) past the target comparison; hnatural
moves the two input augmentations across μ. Thus the bottom composite is
μ on the coefficient objects, followed by RΓ(D.derivedMap t).
Use V.natural for the input comparisons, and V.on_cycles for their localized
integer cycles. The section formula for ν and ht identify the image of the
tensor cycle with the extended output cycle: after extendXIso its component is
D.pair p q top a.val b.val, which equals c.val by hc. Injectivity of the cycle
inclusion gives equality of those cycles. Naturality of homologyπ and of the
homology factorization then identify the upper composite with J.equiv applied
to D.target.class. The input formulas from J.on_cycles identify the other
composite with the right side below. No comparison of two resolutions, equality
of input classes, or normalization of the derived morphism is assumed. The
argument also applies when p or q is zero, since extension by zero and the tensor
summand formula hold in those degrees without a predecessor. -/
theorem moduleCup_single_pairing_homology
    (V : CupDerivedHomologyTensor Γ(X, ⊤)) (J : CupDerivedClassComparison X)
    (μ : ∀ A B : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)),
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj A ⊗
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj B ⟶
        (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.obj (A ⊗ B))
    (hnatural : ∀ (A A' B B' : DerivedCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))) (f : A ⟶ A') (g : B ⟶ B'),
    ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map f ⊗ₘ
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map g) ≫
        μ A' B' = μ A B ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map (f ⊗ₘ g))
    (hdiagram : ∀ K L : CochainComplex
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
    let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let R := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor
    ∃ ν : T.obj K ⊗ T.obj L ⟶ T.obj (K ⊗ L),
      (∀ (i j n : ℤ) (h : i + j = n) (x : Γ(K.X i, ⊤)) (y : Γ(L.X j, ⊤)),
        (ν.f n).hom
            ((HomologicalComplex.ιTensorObj (T.obj K) (T.obj L) i j n h).hom
              (TensorProduct.tmul Γ(X, ⊤) x y)) =
          (HomologicalComplex.ιTensorObj K L i j n h).val.app (op ⊤)
            (tmulSection x y)) ∧
      (moduleCup_globalComparison X K ⊗ₘ moduleCup_globalComparison X L) ≫
          μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
          R.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) =
        Functor.LaxMonoidal.μ DerivedCategory.Q (T.obj K) (T.obj L) ≫
          DerivedCategory.Q.map ν ≫ moduleCup_globalComparison X (K ⊗ L))
    {F G : X.Modules}
    (D : CupResolutionPairing F G)
    (t : D.left.integerComplex ⊗ D.right.integerComplex ⟶ D.target.integerComplex)
    (ht : D.Realizes t) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    J.equiv (F ⊗ G) (p + q) (D.target.class (p + q) c) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) ((p + q : ℕ) : ℤ)).map
        (μ ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
          (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor.map
            (D.derivedMap t))
        (V.pair (cupDerivedSections X F) (cupDerivedSections X G) p q
          (J.equiv F p (D.left.class p a)) (J.equiv G q (D.right.class q b))) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
