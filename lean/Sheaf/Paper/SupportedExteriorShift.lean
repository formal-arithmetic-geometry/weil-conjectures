/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.CompactProductArrows
public import Sheaf.Paper.PurityFiniteSetting

/-! # SupportedExteriorShift

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-supported-exterior-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v c d e w v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry AlgebraicGeometry.Etale

/-- The recorded derived tensor bifunctor is the existing monoidal tensor on objects.
Source: blueprint Step 1, derived tensor convention
(blueprint: def-pur-supported-exterior-shift).
Proof: unfold Etale.derivedTensor and curriedTensor; their object is the tensor
of the very same canonical derived monoidal structure. -/
theorem compactProductTensor_eq (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (X : Scheme.{u})
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    ((derivedTensor C X).obj K).obj L = K ⊗ L := by
  sorry

/-- Compose the shift comparisons in abstract source and target categories.
Source: blueprint Step 1, exterior twist product and sign convention
(blueprint: def-pur-supported-exterior-shift). -/
def compactProductShiftCore {D : Type c} {E : Type d} {H : Type e}
    [Category.{v₁} D] [Category.{v₂} E] [Category.{v₃} H]
    [HasShift D ℤ] [HasShift E ℤ] [HasShift H ℤ]
    (T : H ⥤ H ⥤ H)
    [∀ V : H, (T.obj V).CommShift ℤ]
    [∀ V : H, (T.flip.obj V).CommShift ℤ]
    (F : D ⥤ H) (G : E ⥤ H) [F.CommShift ℤ] [G.CommShift ℤ]
    (K : D) (L : E) (a b : ℤ) :
    (T.obj (F.obj (K⟦a⟧))).obj (G.obj (L⟦b⟧)) ⟶
      ((T.obj (F.obj K)).obj (G.obj L))⟦a + b⟧ :=
  (ProEtale.supportBifunctorIso T ((F.commShiftIso a).app K)
    ((G.commShiftIso b).app L)).hom ≫
    ((T.obj ((F.obj K)⟦a⟧)).commShiftIso b).hom.app (G.obj L) ≫
    (shiftFunctor H b).map
      (((T.flip.obj (G.obj L)).commShiftIso a).hom.app (F.obj K)) ≫
    (shiftFunctorAdd H a b).inv.app _

/-- The same exterior shift comparison before specializing the coefficient category.
Source: blueprint Step 1, exterior twist product and sign convention
(blueprint: def-pur-supported-exterior-shift). -/
def compactProductShiftGeneric (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C] {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (a b : ℤ) :
    externalProduct C f g (K⟦a⟧) (L⟦b⟧) ⟶
      (externalProduct C f g K L)⟦a + b⟧ :=
  compactProductShiftCore (derivedTensor C (pullback f g))
    (upperStar C (pullback.fst f g)).leftDerivedFunctor
    (upperStar C (pullback.snd f g)).leftDerivedFunctor K L a b

/-- The canonical exterior shift comparison, moving the second shift first.
Source: blueprint Step 1, exterior twist product and sign convention
(blueprint: def-pur-supported-exterior-shift). -/
def compactProductShift (P : PurityFiniteSetting.{u}) {B X Y : Scheme.{u}}
    (f : X ⟶ B) (g : Y ⟶ B)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
    (a b : ℤ) :
    externalProduct (ModuleCat.{u + 1} P.Coefficient) f g (K⟦a⟧) (L⟦b⟧) ⟶
      (externalProduct (ModuleCat.{u + 1} P.Coefficient) f g K L)⟦a + b⟧ :=
  compactProductShiftGeneric (ModuleCat.{u + 1} P.Coefficient) f g K L a b

end WeilConjectures.PurityFiniteSetting
