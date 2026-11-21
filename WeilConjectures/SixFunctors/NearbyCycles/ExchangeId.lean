/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BaseChangeCoherence

/-!

# The pullback exchange of the identity morphism of models

The pullback exchange `α : L(𝟙)^* Ψ_M ⟶ Ψ_M L(𝟙)^*` of the identity morphism of a model
(`AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel.Hom.id`) is the composite of the
identity isomorphisms `L(𝟙)^* ≅ 𝟭`
(`NearbyCyclesModel.Hom.id_pullbackExchange_app`). It follows from the unit laws of the
composition isomorphisms of the derived pullbacks (`leftDerivedUpperStarComp_id_left_app`,
`leftDerivedUpperStarComp_id_right_app`).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

/-- **The pullback exchange of a morphism of models with identity components** is the composite of
the identity isomorphisms `I : L(𝟙)^* ≅ 𝟭`: `α_φ(A) = I(Ψ A) ≫ Ψ(I⁻¹(A))`. -/
lemma Hom.pullbackExchange_app_of_eq_id (φ : M.Hom M (𝟙 X) (𝟙 X')) (ht : φ.total = 𝟙 _)
    (hg : φ.generic = 𝟙 _)
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (φ.pullbackExchange Λ).app A =
      (leftDerivedUpperStarId Λ X').hom.app ((M.nearbyCycles Λ).obj A) ≫
        (M.nearbyCycles Λ).map ((leftDerivedUpperStarId Λ X).inv.app A) := by
  obtain ⟨total, generic, _, _, _⟩ := φ
  dsimp only at ht hg
  subst ht hg
  have hj := mateEquiv_app_of_isoId (derivedUpperStarLowerStarAdjunction Λ M.j)
    (leftDerivedUpperStarId Λ M.total) (leftDerivedUpperStarId Λ M.generic)
    (pullbackSquareComparison Λ (⟨by simp⟩ : CommSq (𝟙 M.generic) M.j M.j (𝟙 M.total))).hom
    (fun B ↦ pullbackSquareComparison_hom_app_id_left Λ M.j _ B)
  simp only [Hom.pullbackExchange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, hj,
    pullbackSquareComparison_hom_app_id_right Λ M.i,
    pullbackSquareComparison_hom_app_id_right Λ M.ε]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  rfl

/-- **The pullback exchange of the identity morphism of models** is the composite of the identity
isomorphisms `I : L(𝟙)^* ≅ 𝟭`: `α_𝟙(A) = I(Ψ A) ≫ Ψ(I⁻¹(A))`. -/
lemma Hom.id_pullbackExchange_app
    (A : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    ((Hom.id M).pullbackExchange Λ).app A =
      (leftDerivedUpperStarId Λ X').hom.app ((M.nearbyCycles Λ).obj A) ≫
        (M.nearbyCycles Λ).map ((leftDerivedUpperStarId Λ X).inv.app A) :=
  Hom.pullbackExchange_app_of_eq_id Λ M _ (Hom.id_total M) (Hom.id_generic M) A

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
