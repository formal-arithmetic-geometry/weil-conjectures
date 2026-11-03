/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientSiteScalarArrow

/-! # The specified finite scalar/site comparison, on components

Source: blueprint thm-coef-finite-hom, final site-comparison sentence;
Stacks 00YV and 03CY (blueprint: def-sf-finite-coefficient-site-scalar-arrow).
The imported definitions construct the ordinary inverse image and normalized
restriction isomorphism directly. This module records the explicit component
formula for their derived scalar adjunction mate. No map is chosen by this theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem finiteHomSiteInverseMate_app
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : C ⥤ D} {S : D ⥤ C}
    (a : F ⊣ R) (b : G ⊣ S) {U : A ⥤ C} {V : B ⥤ D}
    (ρ : R ⋙ U ⟶ V ⋙ S) (T : A) :
    (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ ρ)).natTrans).app T =
      G.map (U.map (a.unit.app T)) ≫ G.map (ρ.app (F.obj T)) ≫
        b.counit.app (V.obj (F.obj T)) := by
  simp only [mateEquiv_symm_apply, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, G.map_id,
    Category.id_comp, Category.comp_id]

/-- The inverse mate is the prescribed unit--inverse-restriction--counit composite.
Source: blueprint thm-coef-finite-hom, final site-comparison sentence; Stacks 00YV
(blueprint: def-sf-finite-coefficient-site-scalar-arrow).
Proof: unfold finiteHomSiteBeta and Mathlib's mateEquiv inverse. Evaluate its
whiskered transformations at T. Functoriality sends the associator identities to
identities; cancel these and the two unitors. The remaining three factors are,
in order, pro-etale scalar extension applied to the inverse image of the etale
unit, pro-etale scalar extension applied to rho inverse at the extended object,
and the pro-etale counit. This works also for the identity quotient n=m. -/
theorem finiteHomSiteBeta_app {n m : ℕ} (h : m ≤ n) (T : finiteHomEtale l E X n) :
    (finiteHomSiteBeta l E X h).app T =
      (coefficientFiniteQuotientDerived l E X h).map
        ((finiteHomNu l E X n).map
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (finiteHomQuotient l E h))).unit.app T)) ≫
      (coefficientFiniteQuotientDerived l E X h).map
        ((finiteHomNuDerivedRestriction l E X h).inv.app
          ((finiteHomEtaleReduction l E X h).obj T)) ≫
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction
        h).counit.app ((finiteHomNu l E X m).obj
          ((finiteHomEtaleReduction l E X h).obj T)) := by
  exact finiteHomSiteInverseMate_app
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology (finiteHomQuotient l E h)))
    ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.adjunction h)
    (finiteHomNuDerivedRestriction l E X h).inv T

end WeilConjectures
