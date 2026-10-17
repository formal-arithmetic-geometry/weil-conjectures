/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.Defs

/-!
# The composition isomorphisms of pro-étale pullbacks of sheaves of modules are monoidal

For a commutative ring `R`, the composition isomorphism `(h₁ ≫ h₂)^* ≅ h₂^* ⋙ h₁^*` and the
isomorphism `g^* ≅ g'^*` for `g = g'` of pullbacks of pro-étale sheaves of `R`-modules are
monoidal natural isomorphisms. This is the counterpart for `ModuleCat R` of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso`: the
composition isomorphism of pushforwards is monoidal for any coefficients, being the
composition isomorphism of pushforwards along continuous functors of sites, and that of
pullbacks is its conjugate.

It is used to compare the coefficient rings `j'^* g^* B` and `g_U^* j^* B` of a base change
square (`WeilConjectures.SixFunctors.ProEtale.RingSheaf.OpenBaseChange`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable {R : Type (u + 1)} [CommRing R]

section Comp

variable {S T V : Scheme.{u}} (h₁ : V ⟶ T) (h₂ : T ⟶ S)

/-- The composition isomorphism `h₁_* ⋙ h₂_* ≅ (h₁ ≫ h₂)_*` of pushforwards of sheaves of
`R`-modules is monoidal. -/
instance isMonoidal_lowerStarComp_hom_moduleCat :
    NatTrans.IsMonoidal (lowerStarComp (ModuleCat.{u + 1} R) h₁ h₂).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h₁ h₂).symm)
    (ModuleCat.{u + 1} R) (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)
    (Scheme.ProEt.topology V)).hom)

/-- The composition isomorphism `h₂^* ⋙ h₁^* ≅ (h₁ ≫ h₂)^*` of pullbacks of sheaves of
`R`-modules is monoidal: it is the conjugate of the monoidal composition isomorphism of
pushforwards. -/
instance isMonoidal_upperStarComp_inv_moduleCat :
    NatTrans.IsMonoidal (upperStarComp (ModuleCat.{u + 1} R) h₁ h₂).inv := by
  have h₁' : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (h₁ ≫ h₂))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  have h₂' : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) h₂).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) h₁))
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact Adjunction.isMonoidal_comp _ _
  exact isMonoidal_conjugateEquiv_symm _ _ (lowerStarComp (ModuleCat.{u + 1} R) h₁ h₂).inv

end Comp

section Congr

variable {Z Y : Scheme.{u}} {g g' : Z ⟶ Y} (h : g = g')

/-- The isomorphism `g^* ≅ g'^*` of pullbacks of sheaves of `R`-modules along equal morphisms
is monoidal. -/
instance isMonoidal_upperStarCongr_hom_moduleCat :
    NatTrans.IsMonoidal (upperStarCongr (ModuleCat.{u + 1} R) h).hom := by
  subst h
  exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))

end Congr

end AlgebraicGeometry.ProEtale
