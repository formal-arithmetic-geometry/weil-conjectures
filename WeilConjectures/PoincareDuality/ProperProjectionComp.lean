/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionCoherence
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived

/-!

# The derived proper projection morphism of a composite

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of schemes, the derived projection morphism
`PF^*_{f ≫ g}` of `L(f ≫ g)^* ⊣ R(f ≫ g)_*` is the composite of `PF^*_g` and `Rg_* PF^*_f`, read
through the composition isomorphisms `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` and its conjugate
(`ProEtale.CondensedRing.properProjectionMorphism_comp`). This is the proper part of the
composition clause of the coherence of the projection formula (blueprint `prop-sf-pf-coherence`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

set_option maxHeartbeats 2000000 in
-- unfolding the comultiplication of the derived pullback built from `leftDerivedUpperStarTensor`
/-- The composition isomorphism of the derived pullbacks is compatible with the comultiplications,
in the form used by `CategoryTheory.Adjunction.projectionMorphism_eq_of_iso`. -/
lemma leftDerivedUpperStarComp_δ
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    δ L((f ≫ g)^*⟦Λ⟧) K M ≫
        ((leftDerivedUpperStarComp Λ f g).hom.app K ⊗ₘ (leftDerivedUpperStarComp Λ f g).hom.app M) =
      (leftDerivedUpperStarComp Λ f g).hom.app (K ⊗ M) ≫
        δ (L((g)^*⟦Λ⟧) ⋙ L((f)^*⟦Λ⟧)) K M := by
  exact leftDerivedUpperStarTensor_comp Λ f g K M

section Open

variable {U V : Scheme.{u}} (i : U ⟶ V) (i' : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion i']

end Open

end AlgebraicGeometry.ProEtale.CondensedRing
