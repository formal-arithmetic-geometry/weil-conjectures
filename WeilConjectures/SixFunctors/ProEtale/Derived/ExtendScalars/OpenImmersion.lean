/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek

/-!
# Derived scalar extension commutes with extension by zero

Let `S` be an algebra over a commutative ring `R` and `j : U ⟶ X` an open immersion. Derived
scalar extension `Ψ = - ⊗ᴸ_R S` commutes with the exact extension by zero `j_!`:
`Ψ (j_! K) ≅ j_! (Ψ K)` (blueprint `thm-trf-finite-coefficient-map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The restriction `j^*` along an open immersion on pro-étale sheaves is a left adjoint (of
`j_*`), hence preserves finite colimits. -/
instance preservesFiniteColimits_openImmersionRestriction (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] :
    PreservesFiniteColimits (openImmersionRestriction A j) :=
  have := (openImmersionAdjunctionTriple A j).adj₂.isLeftAdjoint
  inferInstance

/-- Restriction of scalars of pro-étale sheaves commutes with the restriction `j^*` along an
open immersion: both are computed sectionwise. -/
noncomputable def openImmersionRestrictionCompRestrictScalarsIso :
    openImmersionRestriction (ModuleCat.{u + 1} S) j ⋙
        sheafCompose (ProEt.topology U) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) ≅
      sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S)) ⋙
        openImmersionRestriction (ModuleCat.{u + 1} R) j :=
  Iso.refl _

/-- The isomorphism `j^* (U_X K) ≅ U_U (j^* K)` of functors `D(X_proét, S) ⥤ D(U_proét, R)`
between the right adjoints of the two sides of `openImmersionLowerShriekExtendScalarsIso`,
induced by `openImmersionRestrictionCompRestrictScalarsIso`. -/
noncomputable def mapDerivedCategoryOpenImmersionRestrictionCompRestrictScalarsIso :
    D(openImmersionRestriction (ModuleCat.{u + 1} S) j) ⋙
        D(sheafCompose (ProEt.topology U) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))) ≅
      D(sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))) ⋙
        D(openImmersionRestriction (ModuleCat.{u + 1} R) j) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openImmersionRestrictionCompRestrictScalarsIso R S j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Derived scalar extension commutes with the extension by zero along an open immersion `j`:
`Ψ (j_! K) ≅ j_! (Ψ K)`. -/
noncomputable def openImmersionLowerShriekExtendScalarsIso :
    D((j)_!open[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) X) ≅
      L(sheafExtendScalars (algebraMap R S) U) ⋙ D((j)_!open[ModuleCat.{u + 1} S]) :=
  (conjugateIsoEquiv
    ((leftDerivedSheafExtendScalarsAdjunction R S U).comp
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} S) j).mapDerivedCategoryAdjunction)
    ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).mapDerivedCategoryAdjunction.comp
      (leftDerivedSheafExtendScalarsAdjunction R S X))).symm
    (mapDerivedCategoryOpenImmersionRestrictionCompRestrictScalarsIso R S j)

/-- `openImmersionLowerShriekExtendScalarsIso` is characterised as the conjugate, with respect
to the adjunctions `Ψ ⊣ U` and `D(j_!) ⊣ D(j^*)`, of the isomorphism
`mapDerivedCategoryOpenImmersionRestrictionCompRestrictScalarsIso` of right adjoints. -/
lemma conjugateEquiv_openImmersionLowerShriekExtendScalarsIso_hom :
    conjugateEquiv
      ((leftDerivedSheafExtendScalarsAdjunction R S U).comp
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} S) j).mapDerivedCategoryAdjunction)
      (Adjunction.comp
        (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).mapDerivedCategoryAdjunction
        (leftDerivedSheafExtendScalarsAdjunction R S X))
      (openImmersionLowerShriekExtendScalarsIso R S j).hom =
    (mapDerivedCategoryOpenImmersionRestrictionCompRestrictScalarsIso R S j).hom :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply _)

end OpenImmersion
end AlgebraicGeometry.ProEtale
