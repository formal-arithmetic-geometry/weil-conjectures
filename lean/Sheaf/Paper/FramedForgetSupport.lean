module

public import Sheaf.Paper.FramedProPredicate

/-! # Forget support in the normalized framed realization

Source: Stacks 03PL and 0A45, positive Kummer and the support triangle
(blueprint: def-pur-framed-forget-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
/-- Forget support and realize the module class as ordinary abelian cohomology.
Source: Stacks 03PL and 0A45 (blueprint: def-pur-framed-forget-support). -/
@[irreducible] def divisorEtaleForget (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (b : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constantEtale Z)) (P.frameTwistEtale T 1) 2) :=
  Etale.ordinaryFiniteClass P.Coefficient T (P.frameTwistEtale T 1) 2
    (P.functorialCupForget false i 2 1 (P.divisorEtaleHom i b))

/-- The ordinary module derived Hom image after forgetting support.
Source: Stacks 0A45 (blueprint: def-pur-framed-forget-support). -/
@[irreducible] def divisorEtaleForgetHom (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (b : Ext.{u + 1} ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constantEtale Z)) (P.frameTwistEtale T 1) 2) :
    P.FunctorialCupOrdinaryH false T 2 1 :=
  P.functorialCupForget false i 2 1 (P.divisorEtaleHom i b)

/-- The ordinary pro-etale Hom image of an actual normalized supported class.
Source: Stacks 0A45 (blueprint: def-pur-framed-forget-support). -/
@[irreducible] def divisorProForget (P : PurityFiniteSetting.{u}) {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i]
    (χ : (proEtaleSupportHomPair P i).Identification) (c : P.DivisorProGroup i) :
    P.FunctorialCupOrdinaryH true T 2 1 :=
  P.functorialCupForget true i 2 1 (P.divisorProHom i χ c)

end WeilConjectures.PurityFiniteSetting
