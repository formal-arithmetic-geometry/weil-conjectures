module

public import Sheaf.Paper.FramedScalarRealization
public import Sheaf.Paper.SupportedCupFunctoriality

/-! # Finite supported Ext in the canonical Hom model

Source: ordinary etale derived categories, Ext.hom
(blueprint: def-pur-framed-etale-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
/-- The finite module Ext class in the existing etale supported Hom model.
Source: ordinary derived categories and Ext.hom
(blueprint: def-pur-framed-etale-hom). -/
@[irreducible] def divisorEtaleHom (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (i : Z ⟶ T)
    (b : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constantEtale Z)) (P.frameTwistEtale T 1) 2) :
    P.FunctorialCupH false i 2 1 := b.hom


end WeilConjectures.PurityFiniteSetting
