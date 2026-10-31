/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedCupFunctoriality
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundarySupplement

/-! # Forgetting a normalized Cartier representative
Source: blueprint lem-pur-divisor-class, ordinary Chern paragraph
(blueprint: lem-pur-normalized-cartier-forget). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u vH vK
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The existential compatibility of an Ext representative and a Hom representative.
This ordinary logical predicate keeps its maps explicit before specialization.
Source: divisor-class Chern clause (blueprint: lem-pur-normalized-cartier-forget). -/
def divisorChernSpecification {E L : Type*} {H H' : Type vH} {K K' : Type vK}
    (hom : E → H) (ordinary : H → K) (chern : K')
    (supported : L) (compare : H' → L) : Prop :=
  ∃ (c : E) (β : H'), HEq (hom c) β ∧ HEq (ordinary (hom c)) chern ∧
    supported = compare β

/-- The ordinary Ext realization, with its structural instances elaborated once.
Source: Ext.hom and the divisor Chern clause
(blueprint: lem-pur-normalized-cartier-forget). -/
def divisorOrdinaryHom (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  fun c₁ : Abelian.Ext (P.constantEtale T) (P.frameTwistEtale T 1) 2 ↦ c₁.hom

/-- The same ordinary finite-coefficient realization with its parameters fixed.
Source: ordinaryFiniteClass (blueprint: lem-pur-normalized-cartier-forget). -/
def divisorOrdinaryRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  Etale.ordinaryFiniteClass P.Coefficient T (P.frameTwistEtale T 1) 2

/-- The ordinary etale Ext representative obtained by forgetting a normalized
Cartier support. This is only the underived/derived constant-unit identification
ordinary Chern calculation, and naturality of forgetting under site comparison.
Source: blueprint lem-pur-divisor-class, final paragraph; Stacks 03PL and 0A45
(blueprint: lem-pur-normalized-cartier-forget).

Proof: functorialCupForget on the etale site is precomposition with the single
of closedConstantSectionMap. The constant-sheaf adjunction identifies that
restriction with supportedConstantUnit. Set c1=(Ext.mk0 supportedConstantUnit)
composed with kappa. The Ext single-map formula and the realization witness
identify c1.hom with the stated forgetful Hom class. The exact derived single-unit
comparison identifies the same map with supportedDerivedUnit followed by
supportedExactDerivedMap. Apply ordinary_supported_kummer_chern to its normalized
boundary witness to obtain the second equality. These are global equations.
Apply the forget_support clause of supportedCupFunctoriality to the etale
forgetful Hom representative to give the same equation after site comparison.
The empty Cartier divisor has zero relative extension and hence zero ordinary
class; no passage from local equality in degree two is used. -/
theorem normalizedCartier_forget (P : PurityFiniteSetting.{u})
    {D T : Scheme.{u}} (a : T ⟶ Spec (.of P.field.k))
    (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2)
    (α : P.FunctorialCupH false i 2 1) (hα : HEq κ.hom α)
    (hκ : Etale.SupportedKummerBoundary P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a) κ) :
    divisorChernSpecification
      (P.divisorOrdinaryHom T)
      (P.divisorOrdinaryRealization T)
      (Etale.supportedKummerChern P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates i hI (P.diagonalExponent_isUnit a))
      (P.functorialCupForget true i 2 1 (P.functorialCupCompare i 2 1 α))
      (P.functorialCupOrdinaryCompare T 2 1) := by sorry

end WeilConjectures.PurityFiniteSetting
