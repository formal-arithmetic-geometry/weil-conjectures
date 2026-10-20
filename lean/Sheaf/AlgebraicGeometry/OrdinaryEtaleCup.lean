/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import Sheaf.Paper.ModuleCupCanonicalHZeroIdentification
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-! # Ordinary integral etale cup products

Source: Stacks Project, Tags 03FD and 0FPJ, Remark 0B6C.
(blueprint: def-wf-ordinary-etale-cup)

The integer-module presentation is an equivalence, so all abelian coefficient sheaves
are included. The tensor augmentation is the existing lax tensorator of localization,
followed by the existing tensor/single-complex identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Forget the unique integral action. Source: Stacks 03FD
(blueprint: def-wf-ordinary-etale-cup). -/
abbrev integralForget (X : Scheme.{u}) :=
  RawModuleScalarComparison.forget (ULift.{u + 1} ℤ) X

/-- Integral module sheaves and abelian sheaves are equivalent.
Source: Stacks 03FD (blueprint: def-wf-ordinary-etale-cup).
Proof: an abelian group has its unique integer action. Transport it across the ring
isomorphism ULift Z = Z, section by section; every additive map is linear. These inverse
functors preserve the sheaf condition because their underlying groups and restriction
maps agree. The identity maps of underlying groups give the unit and counit. -/
@[instance] theorem integralForget_isEquivalence (X : Scheme.{u}) :
    (integralForget X).IsEquivalence := by
  sorry

/-- The inverse of the integral-forgetting equivalence, with its canonical counit.
Source: Stacks 03FD (blueprint: def-wf-ordinary-etale-cup). -/
abbrev integralLift (X : Scheme.{u}) := (integralForget X).inv

/-- The canonical underlying-abelian-sheaf identification.
Source: Stacks 03FD (blueprint: def-wf-ordinary-etale-cup). -/
def integralLiftIso (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (integralForget X).obj ((integralLift X).obj F) ≅ F :=
  (integralForget X).asEquivalence.counitIso.app F

/-- Integral tensor of abelian sheaves, via the unique integral module structures.
Source: Stacks 03EK (blueprint: def-wf-ordinary-etale-cup). -/
def ordinaryEtaleTensor (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (integralForget X).obj ((integralLift X).obj F ⊗ (integralLift X).obj G)

/-- Tensor of coefficient maps in the same integral presentation.
Source: Stacks 03EK (blueprint: def-wf-ordinary-etale-cup). -/
def ordinaryEtaleTensorMap (X : Scheme.{u})
    {F G F' G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : F ⟶ F') (b : G ⟶ G') :
    ordinaryEtaleTensor X F G ⟶ ordinaryEtaleTensor X F' G' :=
  (integralForget X).map ((integralLift X).map a ⊗ₘ (integralLift X).map b)

/-- The canonical module-derived class comparison is bijective over the integers.
Source: Stacks 03FD (blueprint: def-wf-ordinary-etale-cup).
Proof: integral forgetting is an exact equivalence, hence gives bijections on Ext.
The integral generator is the identity under its constant-sheaf comparison, so
precomposition with it is also a bijection. Compose the two bijections. -/
theorem integralClass_bijective (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (n : ℕ) :
    Function.Bijective (ordinaryFiniteClass (ULift.{u + 1} ℤ) X M n) := by
  sorry

/-- Realize an ordinary class as a derived integral-module morphism. The inverse is
uniquely determined by bijectivity. Source: Stacks 03FD
(blueprint: def-wf-ordinary-etale-cup). -/
def integralClassLift (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x : Sheaf.H F n) :
    (DerivedCategory.singleFunctor _ 0).obj
        (ordinaryFiniteConstant (ULift.{u + 1} ℤ) X) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj ((integralLift X).obj F))⟦(n : ℤ)⟧ :=
  Function.surjInv (integralClass_bijective X ((integralLift X).obj F) n).surjective
    (Sheaf.H.map (integralLiftIso X F).inv n x)

end AlgebraicGeometry.Etale

namespace DerivedCategory
variable {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{v} C]

/-- Diagonal of the derived integral generator, induced by the tensor unit.
Source: Stacks 0FPJ (blueprint: def-wf-ordinary-etale-cup). -/
def ordinaryCupDiagonal :
    (singleFunctor C 0).obj (𝟙_ C) ⟶
      (singleFunctor C 0).obj (𝟙_ C) ⊗ (singleFunctor C 0).obj (𝟙_ C) :=
  (singleFunctorObjUnitIso C).hom ≫ (λ_ (𝟙_ (DerivedCategory C))).inv ≫
    ((singleFunctorObjUnitIso C).inv ⊗ₘ (singleFunctorObjUnitIso C).inv)

/-- Canonical augmentation from derived to ordinary tensor, without a flatness assumption.
Source: Stacks 06YY and 0FPJ (blueprint: def-wf-ordinary-etale-cup). -/
def ordinaryCupAugmentation (F G : C) :
    (singleFunctor C 0).obj F ⊗ (singleFunctor C 0).obj G ⟶
      (singleFunctor C 0).obj (F ⊗ G) :=
  ((singleFunctorIsoCompQ C 0).hom.app F ⊗ₘ
      (singleFunctorIsoCompQ C 0).hom.app G) ≫
    Functor.LaxMonoidal.μ Q ((CochainComplex.singleFunctor C 0).obj F)
      ((CochainComplex.singleFunctor C 0).obj G) ≫
    Q.map (moduleCup_singleTensorIso F G).hom ≫
    (singleFunctorIsoCompQ C 0).inv.app (F ⊗ G)

/-- Shift comparison in the existing derived tensor, in nonnegative degrees.
The right shift is moved first: on cycles this is the unsigned z tensor w convention.
Source: Stacks 0FPJ (blueprint: def-wf-ordinary-etale-cup). -/
def ordinaryCupShiftIso (F G : DerivedCategory C) (p q : ℕ) :
    F⟦(p : ℤ)⟧ ⊗ G⟦(q : ℤ)⟧ ≅ (F ⊗ G)⟦((p + q : ℕ) : ℤ)⟧ :=
  ((tensorLeft (F⟦(p : ℤ)⟧)).commShiftIso (q : ℤ)).app G ≪≫
    (shiftFunctor _ (q : ℤ)).mapIso (((tensorRight G).commShiftIso (p : ℤ)).app F) ≪≫
      ((shiftFunctorAdd' _ (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ)
        (by simp)).app _).symm

/-- Cup of derived unit classes followed by the given ordinary coefficient pairing.
Source: Stacks 0FPJ and Remark 0B6C (blueprint: def-wf-ordinary-etale-cup). -/
def ordinaryCupOfClasses {F G H : C} (e : F ⊗ G ⟶ H) (p q : ℕ)
    (x : (singleFunctor C 0).obj (𝟙_ C) ⟶ (singleFunctor C 0).obj F⟦(p : ℤ)⟧)
    (y : (singleFunctor C 0).obj (𝟙_ C) ⟶ (singleFunctor C 0).obj G⟦(q : ℤ)⟧) :
    (singleFunctor C 0).obj (𝟙_ C) ⟶
      (singleFunctor C 0).obj H⟦((p + q : ℕ) : ℤ)⟧ :=
  ordinaryCupDiagonal ≫ (x ⊗ₘ y) ≫
    (ordinaryCupShiftIso _ _ p q).hom ≫
    (ordinaryCupAugmentation F G ≫ (singleFunctor C 0).map e)⟦((p + q : ℕ) : ℤ)⟧'

end DerivedCategory

namespace AlgebraicGeometry.Etale

/-- Ordinary cup on arbitrary abelian etale sheaves. The pairing is lifted through
fully faithful integral forgetting; the two ordinary classes are lifted through its
canonical cohomology comparison. Source: Stacks 0FPJ, 03FD and Remark 0B6C
(blueprint: def-wf-ordinary-etale-cup). -/
def ordinaryEtaleCup (X : Scheme.{u})
    {F G H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : ordinaryEtaleTensor X F G ⟶ H) (p q : ℕ)
    (x : Sheaf.H F p) (y : Sheaf.H G q) : Sheaf.H H (p + q) :=
  Sheaf.H.map (integralLiftIso X H).hom (p + q)
    (ordinaryFiniteClass (ULift.{u + 1} ℤ) X ((integralLift X).obj H) (p + q)
      (DerivedCategory.ordinaryCupOfClasses
        ((integralForget X).preimage (e ≫ (integralLiftIso X H).inv)) p q
        (integralClassLift X F p x) (integralClassLift X G q y)))

/-- Integral presentation of the ordinary inverse-image comparison.
Source: Stacks 03D7 and 03FD (blueprint: def-wf-ordinary-etale-cup). -/
def integralLiftPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj ((integralLift X).obj F) ≅
      (integralLift Y).obj ((upperStar AddCommGrpCat.{u + 1} f).obj F) :=
  (integralForget Y).preimageIso
    ((RawModuleScalarComparison.pullbackIso (ULift.{u + 1} ℤ) f).app
        ((integralLift X).obj F) ≪≫
      (upperStar AddCommGrpCat.{u + 1} f).mapIso (integralLiftIso X F) ≪≫
        (integralLiftIso Y ((upperStar AddCommGrpCat.{u + 1} f).obj F)).symm)

/-- The canonical identification of inverse image of integral tensor with tensor of
inverse images. It is the existing module oplax tensorator, conjugated by the canonical
scalar-forgetting comparisons. Source: Stacks 07A4
(blueprint: def-wf-ordinary-etale-cup). -/
def ordinaryEtaleTensorPullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStar AddCommGrpCat.{u + 1} f).obj (ordinaryEtaleTensor X F G) ⟶
      ordinaryEtaleTensor Y ((upperStar AddCommGrpCat.{u + 1} f).obj F)
        ((upperStar AddCommGrpCat.{u + 1} f).obj G) :=
  (RawModuleScalarComparison.pullbackIso (ULift.{u + 1} ℤ) f).inv.app
      ((integralLift X).obj F ⊗ (integralLift X).obj G) ≫
    (integralForget Y).map
      (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f)
        ((integralLift X).obj F) ((integralLift X).obj G)) ≫
    (integralForget Y).map
      ((integralLiftPullbackIso f F).hom ⊗ₘ (integralLiftPullbackIso f G).hom)

end AlgebraicGeometry.Etale
end
