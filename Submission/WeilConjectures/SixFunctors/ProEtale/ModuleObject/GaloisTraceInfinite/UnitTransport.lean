/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisActionModule
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.UpperStarLowerStarHom

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The unit transport of module objects on underlying sheaves

For weakly étale `g : Y ⟶ X`, `p₁ : Y' ⟶ X` and `s : Y' ⟶ Y` with `s ≫ g = p₁`, the unit
transport `g_* g^* ⟶ p₁_* p₁^*` of module objects along `s`
(`AlgebraicGeometry.ProEtale.CondensedRing.unitTransport`, built from the unit of `s^* ⊣ s_*` and
the composition isomorphisms) is, on underlying sheaves, the restriction along `s` in the
restriction model `AlgebraicGeometry.ProEtale.upperStarLowerStarHom`, through the identifications
`upperStarForgetIso` (`AlgebraicGeometry.ProEtale.CondensedRing.forget_map_unitTransport_app_eq`).
We also record the underlying sheaf maps of the unit and of the trace of a Galois covering.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- A morphism `s` over `X` between weakly étale `X`-schemes is weakly étale. -/
lemma weaklyEtale_of_comp_eq_of_weaklyEtale {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    {p₁ : Y' ⟶ X}
    (hp : s ≫ g = p₁) [WeaklyEtale g] [WeaklyEtale p₁] : WeaklyEtale s :=
  MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) s g ‹_›
    (hp ▸ ‹WeaklyEtale p₁›)

/-- The restriction along `baseChangeTransport` is `restrictionHom`. -/
lemma baseChangeTransportSheafHom_eq {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    [WeaklyEtale g] {p₁ : Y' ⟶ X} [WeaklyEtale p₁] (hp : s ≫ g = p₁)
    (H : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
    baseChangeTransportSheafHom s g hp H = (restrictionHom g p₁ s hp).app H :=
  Sheaf.hom_ext (restrictionHom_app_hom s hp H).symm

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The unit transport of module objects on underlying sheaves** is the restriction along `s`
in the restriction model, conjugated by the identifications `upperStarForgetIso`. -/
theorem forget_map_unitTransport_app_eq {X Y Y' : Scheme.{u}} (s : Y' ⟶ Y) (g : Y ⟶ X)
    [WeaklyEtale g] {p₁ : Y' ⟶ X} [WeaklyEtale p₁] (hp : s ≫ g = p₁)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget _).map ((unitTransport Λ s hp hp).app M) =
      (g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).inv.app M) ≫
        (upperStarLowerStarHom g p₁ s hp).app M.X ≫
        (p₁)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ p₁).hom.app M) := by
  have := weaklyEtale_of_comp_eq_of_weaklyEtale s g hp
  rw [forget_map_unitTransport_app_of_eq, unitTransport_eq_baseChangeTransportSheafHom s g hp,
    baseChangeTransportSheafHom_eq, upperStarLowerStarHom]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, assoc]

/-- The unit of `g^* ⊣ g_*` on module objects, on underlying sheaves. -/
lemma forget_map_unit_app {X Y : Scheme.{u}} (g : Y ⟶ X)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget _).map ((upperStarLowerStarAdjunction Λ g).unit.app M) =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g).unit.app M.X ≫
        (g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).hom.app M) :=
  upperStarLowerStarAdjunction_unit_app_hom Λ g M

section Transport

variable {X Y Y' Y'' : Scheme.{u}} {g : Y ⟶ X} {g' : Y' ⟶ X} {g'' : Y'' ⟶ X} [WeaklyEtale g]
  [WeaklyEtale g'] [WeaklyEtale g'']

/-- The Galois action of module objects on underlying sheaves, in terms of the restriction along
the automorphism. -/
lemma forget_map_galoisAction_app_eq [Surjective g] [QuasiCompact g] {Γ : Type u}
    {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g) (a : Γ)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (Mod.forget _).map ((galoisAction Λ g hρ a).app M) =
      (g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).inv.app M) ≫
        (upperStarLowerStarHom g g (ρ a) (hρ a)).app M.X ≫
        (g)_*[Ab.{u + 1}].map ((upperStarForgetIso Λ g).hom.app M) := by
  rw [forget_map_galoisAction_app, ← galoisActionNatTrans_app, galoisActionNatTrans_eq]

/-- The Galois action on module objects is an action: `ρ a ≫ ρ b = ρ (b * a)`. -/
@[reassoc]
lemma galoisAction_app_comp_galoisAction_app [Surjective g] [QuasiCompact g] {Γ : Type u}
    [Mul Γ] {ρ : Γ → (Y ⟶ Y)} (hρ : ∀ i, ρ i ≫ g = g) (hmul : ∀ a b, ρ a ≫ ρ b = ρ (a * b))
    (a b : Γ) (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (galoisAction Λ g hρ a).app M ≫ (galoisAction Λ g hρ b).app M =
      (galoisAction Λ g hρ (b * a)).app M := by
  apply (Mod.forget _).map_injective
  rw [Functor.map_comp, forget_map_galoisAction_app_eq, forget_map_galoisAction_app_eq,
    forget_map_galoisAction_app_eq]
  simp only [assoc]
  rw [← Functor.map_comp_assoc (g)_*[Ab.{u + 1}], Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, id_comp]
  rw [← NatTrans.comp_app_assoc,
    upperStarLowerStarHom_comp, upperStarLowerStarHom_congr _ (hmul b a)]

end Transport

end CondensedRing

end AlgebraicGeometry.ProEtale
