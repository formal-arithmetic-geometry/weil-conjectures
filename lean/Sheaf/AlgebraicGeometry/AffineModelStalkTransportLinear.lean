module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Scalar compatibility of the explicit affine stalk transport

Source: Stacks Project, Tags 01BH and 01HV (7).
(blueprint: new-s2-affine-model-stalk-transport-linear)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The additive stalk transport, constructed from the chart, model, and open restriction. -/
noncomputable def affineModelStalkAddEquiv
    {Y : Scheme.{u}} (x : Y) (U : Y.affineOpens) (hx : x ∈ U.1)
    (F : Y.Modules) (M : ModuleCat.{u} Γ(Y, U.1))
    (e : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅
      (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj (tilde M)) :
    (tilde M).presheaf.stalk (U.2.primeIdealOf ⟨x, hx⟩) ≃+ F.presheaf.stalk x :=
  (((Scheme.Modules.restrictStalkNatIso U.2.isoSpec.hom ⟨x, hx⟩).app
      (tilde M)).symm ≪≫
    (Scheme.Modules.toPresheaf U.1.toScheme ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hx⟩ : U.1.toScheme)).mapIso e.symm ≪≫
    (Scheme.Modules.restrictStalkNatIso U.1.ι ⟨x, hx⟩).app F).addCommGroupIsoToAddEquiv

/-- The explicitly constructed additive transport respects the coordinate-ring action.
Source: Stacks Project, Tags 01BH and 01HV (7).
(blueprint: new-s2-affine-model-stalk-transport-linear)

Proof: For an open immersion f, restriction-stalk transport carries the germ of
r times m to the germ of the restricted scalar times the transported section.
Represent r and m on a common neighbourhood and apply germ_smul and
smul_restrictAppIso_hom; the germ formula for restrictStalkNatIso gives this
identity in the stalk. Its inverse satisfies the inverse identity by bijectivity.
Apply these identities to the chart isomorphism and to U -> Y, and use linearity
of e.inv on sections for the middle factor. The composite ring-stalk map carries
the canonical germ of a in Spec A to the germ of a on U: this is
isoSpec_hom_appTop followed by germ_stalkMap_apply. Consequently the three
scalar identities compose to the displayed equality. Germ representatives cover
all stalk elements. Zero modules require no exception, and hx rules out empty U. -/
theorem affineModelStalkAddEquiv_smul
    {Y : Scheme.{u}} (x : Y) (U : Y.affineOpens) (hx : x ∈ U.1)
    (F : Y.Modules) (M : ModuleCat.{u} Γ(Y, U.1))
    (e : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅
      (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj (tilde M))
    (a : Γ(Y, U.1)) (m : (tilde M).presheaf.stalk (U.2.primeIdealOf ⟨x, hx⟩)) :
    affineModelStalkAddEquiv x U hx F M e (a • m) =
      Y.presheaf.germ U.1 x hx a • affineModelStalkAddEquiv x U hx F M e m := by sorry

end AlgebraicGeometry
