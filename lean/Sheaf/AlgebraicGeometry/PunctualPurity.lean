/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus
public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-!
# Punctual purity of regular schemes

Source: ILO, Exposé XVI, Definitions 3.2.1--3.2.2, printed p.244
(blueprint: def-per-punctual-purity).

The map is the transpose of the published supported Kummer class, using the closed
support adjunction and the canonical exact-direct-image comparison. The inclusion of
D+ into D is fully faithful, so the same map tests purity in either category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The unique normalized Kummer class family supplied by the class-calculus theorem.
The existence theorem determines the family uniquely; no arbitrary supported class is chosen.
Source: ILO XVI 2.3.1--2.3.2 (blueprint: def-per-punctual-purity). -/
def regularImmersionClasses (ℓ : ℕ) (hℓ : ℓ.Prime) : RegularImmersionClassFamily.{u} ℓ :=
  (regular_immersion_class_calculus ℓ hℓ).exists.choose

/-- View a supported Ext element in D+, via the fully faithful inclusion into D.
Source: ILO XVI 3.2.1 (blueprint: def-per-punctual-purity). -/
def supportedExtPlusHom (ℓ : ℕ) (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)))
    (m : ℕ) (κ : Ext F G m) :
    (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F ⟶
      ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)⟦(m : ℤ)⟧ :=
  _root_.DerivedCategory.Plus.ι.preimage
    ((_root_.DerivedCategory.Plus.singleFunctorιIso _ 0).hom.app F ≫ κ.hom ≫
      ((_root_.DerivedCategory.Plus.singleFunctorιIso _ 0).inv.app G)⟦(m : ℤ)⟧' ≫
      (_root_.DerivedCategory.Plus.ι.commShiftIso (m : ℤ)).inv.app
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G))

/-- Finiteness of the lifted prime coefficient ring, used by the closed support adjunction.
Source: ILO XVI 3.2.1 (blueprint: def-per-punctual-purity). -/
abbrev punctualPurityCoefficientsFinite (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Finite (regularClassCoefficients.{u} ℓ 1) :=
  letI : NeZero (ℓ ^ 1) := ⟨pow_ne_zero 1 hℓ.ne_zero⟩
  inferInstance

/-- The canonical class A_Z -> i^! A_X(c)[2c] for coefficients F_ell.
The right adjoint is the existing derived closed support functor. Its left adjoint is
identified with termwise closed direct image by the canonical exact-functor comparison.
Source: ILO XVI 2.3.1, 3.2.1 (blueprint: def-per-punctual-purity). -/
def punctualPurityClassMap (ℓ : ℕ) (hℓ : ℓ.Prime)
    {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] (c : ℕ)
    (hi : IsStalkRegularClosedImmersion i c)
    (hX : IsUnit ((ℓ ^ 1 : ℕ) : Γ(X, ⊤))) :
    (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj (regularClassTwist ℓ 1 Z 0) ⟶
      (@closedSupportPlus (regularClassCoefficients.{u} ℓ 1) inferInstance
        (punctualPurityCoefficientsFinite ℓ hℓ) Z X i inferInstance).obj
        (((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          (regularClassTwist ℓ 1 X ((c : ℤ) + 0)))⟦((2 * c : ℕ) : ℤ)⟧) :=
  ((@closedSupportPlusAdjunction (regularClassCoefficients.{u} ℓ 1) inferInstance
      (punctualPurityCoefficientsFinite ℓ hℓ) Z X i inferInstance).ofNatIsoLeft
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) i))).homEquiv _ _
    ((Functor.mapDerivedCategoryPlusSingleFunctor
        (lowerStar (ModuleCat.{u + 1} (regularClassCoefficients.{u} ℓ 1)) i) 0).hom.app
          (regularClassTwist ℓ 1 Z 0) ≫
      supportedExtPlusHom ℓ X _ _ (2 * c)
        (regularImmersionClasses ℓ hℓ 1 (by decide) i c hi hX 0))

/-- Punctual purity at w: the local closed-point class is invertible. The witnesses record
its actual finite Krull dimension and the evidence needed to evaluate the existing class
family. For a regular Noetherian scheme these witnesses always exist independently of purity.
Source: ILO XVI Definitions 3.2.1--3.2.2 (blueprint: def-per-punctual-purity). -/
def IsPunctuallyPureAt (ℓ : ℕ) (hℓ : ℓ.Prime) (W : Scheme.{u}) (w : W) : Prop :=
  ∃ (d : ℕ), ringKrullDim (W.presheaf.stalk w) = (d : WithBot ℕ∞) ∧
    ∃ (_hN : IsNoetherian (Spec (W.presheaf.stalk w)))
      (hi : IsStalkRegularClosedImmersion (Spec.map (W.residue w)) d)
      (hInv : IsUnit ((ℓ ^ 1 : ℕ) : Γ(Spec (W.presheaf.stalk w), ⊤))),
      IsIso (punctualPurityClassMap ℓ hℓ (Spec.map (W.residue w)) d hi hInv)

/-- Punctual purity holds at every point, including nonclosed points of the original scheme.
Regularity and Noetherianity are supplied by the theorems using this predicate.
Source: ILO XVI Definition 3.2.2 (blueprint: def-per-punctual-purity). -/
def IsPunctuallyPure (ℓ : ℕ) (hℓ : ℓ.Prime) (W : Scheme.{u}) : Prop :=
  ∀ w : W, IsPunctuallyPureAt ℓ hℓ W w

end AlgebraicGeometry.Etale
