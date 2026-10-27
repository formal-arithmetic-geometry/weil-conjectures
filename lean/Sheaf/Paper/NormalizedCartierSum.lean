/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.SupportedCupFunctoriality
public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary

/-! # Addition of three normalized Cartier Kummer representatives

Source: blueprint lem-pur-divisor-class, product-ideal addition clause
(blueprint: lem-pur-normalized-cartier-sum).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

/-- Three individually normalized representatives satisfy the Cartier sum formula.
The Cartier condition and support inclusions are inputs; this lemma only compares
cohomology classes, without constructing the global divisor family.

Source: blueprint lem-pur-divisor-class, clause (b); DAG
lem-pur-cartier-pair-tensor-addition and lem-pur-divisor-normalized-realization.
(blueprint: lem-pur-normalized-cartier-sum).

Proof: cartierPairTensor_geometry identifies the dual of the product ideal with
the tensor of the two dual ideals and their canonical sections. The specified
frames on the common complementary open tensor to the product frame. Apply
cartierPairTensor_extensions: their integral relative extensions satisfy the
Baer-sum identity after the two canonical maps on supported integers. The
SupportedKummerBoundary witnesses identify each extension with its canonical
relative extension, and each module representative with its unique normalized
scalar realization. divisorRealization_additive and divisorRealization_enlarge
carry the Baer-sum equation to the module and pro-etale classes. The support maps
are functorialCupChangeSupport: both preserve the restriction of constants, so
the normalized support-map uniqueness identifies them. Apply the same exact site
comparison to the equation. This proves the displayed equality globally; no
inference from equality on trivializing opens is used. Empty divisors give the
zero relative extension, and coincident or nonreduced divisors are allowed because
the hypothesis uses the product ideal and the tensor calculation includes multiplicity. -/
theorem normalizedCartier_sum (P : PurityFiniteSetting.{u})
    {D₁ D₂ Z T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (i₁ : D₁ ⟶ T) (i₂ : D₂ ⟶ T) (s : Z ⟶ T)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion s]
    (h₁ : i₁.ker.IsInvertible) (h₂ : i₂.ker.IsInvertible)
    (hs : s.ker = i₁.ker * i₂.ker) (hsum : s.ker.IsInvertible)
    (a₁ : D₁ ⟶ Z) (a₂ : D₂ ⟶ Z) (ha₁ : a₁ ≫ s = i₁) (ha₂ : a₂ ≫ s = i₂)
    (κ₁ : Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i₁).obj (P.constantEtale D₁))
      (P.frameTwistEtale T 1) 2)
    (κ₂ : Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i₂).obj (P.constantEtale D₂))
      (P.frameTwistEtale T 1) 2)
    (κsum : Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s).obj (P.constantEtale Z))
      (P.frameTwistEtale T 1) 2)
    (α₁ : P.FunctorialCupH false i₁ 2 1)
    (α₂ : P.FunctorialCupH false i₂ 2 1)
    (αsum : P.FunctorialCupH false s 2 1)
    (hα₁ : HEq κ₁.hom α₁) (hα₂ : HEq κ₂.hom α₂) (hαsum : HEq κsum.hom αsum)
    (hκ₁ : Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i₁ h₁ (P.diagonalExponent_isUnit a) κ₁)
    (hκ₂ : Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i₂ h₂ (P.diagonalExponent_isUnit a) κ₂)
    (hκsum : Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates s hsum (P.diagonalExponent_isUnit a) κsum) :
    P.functorialCupCompare s 2 1 αsum =
      P.functorialCupChangeSupport true s i₁ a₁ ha₁ 2 1
          (P.functorialCupCompare i₁ 2 1 α₁) +
        P.functorialCupChangeSupport true s i₂ a₂ ha₂ 2 1
          (P.functorialCupCompare i₂ 2 1 α₂) := by sorry

end WeilConjectures.PurityFiniteSetting
