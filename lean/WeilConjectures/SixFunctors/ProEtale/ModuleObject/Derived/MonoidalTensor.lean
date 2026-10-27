/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalRightCounit

/-!
# The tensor comparison of the derived pullback of module objects

Part of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`, split off so that
each file compiles within the time limit: the comparison
`Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L` (`leftDerivedUpperStarTensor`) and its compatibility with
the counits.
-/


set_option Elab.async false

@[expose] public section

open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The counit of the bifunctor `Lf^* (- ⊗ᴸ -)`: `Lf^*` of the lax structure
`Qh A ⊗ᴸ Qh B ⟶ Qh (A ⊗ B)` of the localization, followed by the counit
`Lf^* (Qh (A ⊗ B)) ⟶ Qh (f^* (A ⊗ B))` of the derived pullback. -/
noncomputable def leftDerivedUpperStarTensorLeftCounit :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (leftDerivedUpperStarTensorLeft Λ f) ⟶
      upperStarTensorTarget Λ f where
  app A :=
    { app B := L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (A ⊗ B)
      naturality B B' ψ := by
        have h₁ := Functor.LaxMonoidal.μ_natural_right DerivedCategory.Qh A ψ
        have h₂ := (f)^*⟦Λ⟧.leftDerivedFunctorCounit.naturality (A ◁ ψ)
        dsimp only [Functor.comp_map] at h₂
        change L((f)^*⟦Λ⟧).map (DerivedCategory.Qh.obj A ◁ DerivedCategory.Qh.map ψ) ≫
            L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B') ≫ _ =
          (L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫ _) ≫
            DerivedCategory.Qh.map (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).map (A ◁ ψ))
        rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, Category.assoc, h₂] }
  naturality A A' φ := by
    ext B
    have h₁ := Functor.LaxMonoidal.μ_natural_left DerivedCategory.Qh φ B
    have h₂ := (f)^*⟦Λ⟧.leftDerivedFunctorCounit.naturality (φ ▷ B)
    dsimp only [Functor.comp_map] at h₂
    change L((f)^*⟦Λ⟧).map (DerivedCategory.Qh.map φ ▷ DerivedCategory.Qh.obj B) ≫
        L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A' B) ≫ _ =
      (L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫ _) ≫
        DerivedCategory.Qh.map (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).map (φ ▷ B))
    rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, Category.assoc, h₂]

/-- The comparison `m_{K,L} : Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L` of the derived pullback with the
derived tensor product, as a natural transformation of bifunctors on `D(Mod_{Λ_Y})`: the
morphism to the left derived bifunctor `Lf^* - ⊗ᴸ Lf^* -` induced by the counit
`leftDerivedUpperStarTensorLeftCounit` (`Functor.leftDerived₂Lift`). -/
noncomputable def leftDerivedUpperStarTensor :
    leftDerivedUpperStarTensorLeft Λ f ⟶ leftDerivedUpperStarTensorRight Λ f :=
  (leftDerivedUpperStarTensorRight Λ f).leftDerived₂Lift
    (leftDerivedUpperStarTensorRightCounit Λ f)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (leftDerivedUpperStarTensorLeft Λ f) (leftDerivedUpperStarTensorLeftCounit Λ f)

/-- The comparison `m` is compatible with the counits. -/
lemma leftDerivedUpperStarTensor_fac :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).map
        (leftDerivedUpperStarTensor Λ f) ≫ leftDerivedUpperStarTensorRightCounit Λ f =
      leftDerivedUpperStarTensorLeftCounit Λ f :=
  Functor.leftDerived₂_fac _ _ _ _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing
