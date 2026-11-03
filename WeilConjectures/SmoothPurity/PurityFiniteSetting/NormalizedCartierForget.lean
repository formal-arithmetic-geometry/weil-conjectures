/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement

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

end WeilConjectures.PurityFiniteSetting
