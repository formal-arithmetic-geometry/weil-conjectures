/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Finite-torsion unbounded compact supports after exact étale sum extension

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/
sec-the-exceptional-inverse-image-of-a-smooth-morphism-and-base-change/
sk-lem-geo-affine-local/lem-amb-etale-adjoint-locality.proof.md, paragraph 2,
third Hom bijection (blueprint: lem-amb-etale-compact-support-precomposition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The unique left-adjoint comparison for successive étale restrictions, descended termwise.
Source: `lem-amb-etale-adjoint-locality.proof.md`, paragraph 2, further localization;
node proof step 4 (blueprint: lem-amb-etale-compact-support-precomposition).

It is the mate of the inverse of `upperStarComp`, using the given sum/restriction adjunctions.
The exact-functor derived compositor transports this sheaf mate to the ordinary unbounded
categories. Its definition does not assume a later theorem identifying a sheetwise compositor. -/
noncomputable def etaleCompactSupportSumCompIso
    (A : Type (u + 1)) [CommRing A]
    {V U X : Scheme.{u}} (v : V ⟶ U) (u : U ⟶ X) [Etale v] [Etale u] :
    (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) (v ≫ u) inferInstance).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointCompIso
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) u inferInstance)
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (v ≫ u) inferInstance)
        (upperStarComp (ModuleCat.{u + 1} A) v u).symm)

/-- The exact identity sum extension is identified with the identity by uniqueness of
left adjoints to the canonical identity restriction. Source: the identity clause of
`lem-amb-etale-adjoint-locality.proof.md`, paragraph 2
(blueprint: lem-amb-etale-compact-support-precomposition). -/
noncomputable def etaleCompactSupportIdentityComparison
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance).mapDerivedCategory ≅
      𝟭 (DerivedCategoryModule A X) := by
  exact Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointIdIso
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X) inferInstance)
        (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
    Functor.mapDerivedCategoryIdIso _

end AlgebraicGeometry.Etale
