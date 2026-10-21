/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import Sheaf.Paper.CoefficientSystemImageData

/-! # Ordinary geometric images of strict coefficient systems

Source: Zheng, Construction 4.1; Stacks Project, Tags 03DA and 03DB.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v u' v' w d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

/-- Levelwise ordinary lifts, before forming the category of strict systems.
Source: Stacks 03D7; Zheng Construction 4.1
(blueprint: lem-pur-coefficient-level-ordinary-images). -/
structure CoefficientLevelOrdinaryImage where
  singleton : L.obj ((constantSheaf J (Type w)).obj PUnit) ≅
    (constantSheaf K (Type w)).obj PUnit
  lift : ∀ n, AlgebraicInverseImage L
    (coefficientQuotientSheaf (J := J) O ell n)
    (coefficientQuotientSheaf (J := K) O ell n)
  constants : ∀ n x,
    L.map (coefficientConstantSection (J := J) O ell n x) ≫ (lift n).ringUnderlying.hom =
      singleton.hom ≫ coefficientConstantSection (J := K) O ell n x
  [inverseAdditive : ∀ n, (lift n).modules.Additive]
  inverseExact : ∀ n, PreservesFiniteLimits (lift n).modules ∧
    PreservesFiniteColimits (lift n).modules
  right : ∀ n, coefficientLevelModules (J := K) O ell n ⥤
    coefficientLevelModules (J := J) O ell n
  [rightAdditive : ∀ n, (right n).Additive]
  rightUnderlying : ∀ n, right n ⋙ coefficientUnderlying (J := J) O ell n ≅
    coefficientUnderlying (J := K) O ell n ⋙ V
  levelAdj : ∀ n, (lift n).modules ⊣ right n
  levelTranspose : ∀ n M N (f : (lift n).modules.obj M ⟶ N),
    (coefficientUnderlying (J := J) O ell n).map ((levelAdj n).homEquiv M N f) ≫
      (rightUnderlying n).hom.app N =
    adj.homEquiv _ _ ((lift n).moduleUnderlying.inv.app M ≫
      (coefficientUnderlying (J := K) O ell n).map f)
  restrictInverse : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := J) O ell h ⋙ (lift m).modules ≅
      (lift n).modules ⋙ coefficientRestriction (J := K) O ell h
  restrictInverseUnderlying : ∀ {m n : ℕ} (h : n ≤ m) M,
    (coefficientUnderlying (J := K) O ell m).map ((restrictInverse h).hom.app M) ≫
      (coefficientRestrictionUnderlying (J := K) O ell h).hom.app
        ((lift n).modules.obj M) ≫ (lift n).moduleUnderlying.hom.app M =
    (lift m).moduleUnderlying.hom.app ((coefficientRestriction (J := J) O ell h).obj M) ≫
      L.map ((coefficientRestrictionUnderlying (J := J) O ell h).hom.app M)
  restrictRight : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := K) O ell h ⋙ right m ≅
      right n ⋙ coefficientRestriction (J := J) O ell h
  restrictTranspose : ∀ {m n : ℕ} (h : n ≤ m) M N
    (f : (lift n).modules.obj M ⟶ N),
    (levelAdj m).homEquiv _ _
      ((restrictInverse h).hom.app M ≫ (coefficientRestriction (J := K) O ell h).map f) =
    (coefficientRestriction (J := J) O ell h).map ((levelAdj n).homEquiv _ _ f) ≫
      (restrictRight h).inv.app N

attribute [instance] CoefficientLevelOrdinaryImage.inverseAdditive
  CoefficientLevelOrdinaryImage.rightAdditive

/-- Constant-coefficient level lifts, coherent with scalar restriction.
Source: Stacks 00YV, 03D2, 03DA, 03DB and 03D7; Zheng Construction 4.1.

Proof: identify constant sheaves with copowers of the terminal sheaf. The given
left adjoint preserves copowers and the terminal sheaf, hence its constant-ring
comparison fixes every constant generator. Transport ring and module operations
through its finite-product comparisons. The module right adjoint is the lift of
V, with its action defined by transposing the module action. The original sheaf
adjunction restricts to linear maps and has the displayed underlying transpose.
Limits and colimits of the module lift are preserved because their underlying
abelian sheaf constructions are preserved. For a quotient map, restricting scalars
and then transporting the action gives the same action as transporting first and
then restricting. The underlying identity gives restrictInverse. The right lift
has the same scalar action by adjunction, giving restrictRight. Transposition of
the identity on underlying sheaves gives restrictTranspose. These comparisons
hold for every pair of indices, including equal indices and the zero quotient ring.
(blueprint: lem-pur-coefficient-level-ordinary-images). -/
theorem coefficientLevelOrdinaryImage_exists [PreservesFiniteLimits L] :
    Nonempty (CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) := by
  sorry

end SheafOfModules
