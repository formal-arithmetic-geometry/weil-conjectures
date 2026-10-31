/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

/-! # Precomposing the ordinary derived pullback interchange -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The ordinary derived pullback interchange commutes with precomposition,
including specified names for the two composite arrows.
Source: composition-coherence proof, Step 1, restriction along the diagonal
(blueprint: lem-pur-pullback-square-precomposition).

Proof: expand the interchange as the inverse right-hand pullback compositor
followed by the left-hand compositor. The first rearranged associativity law
moves the initial compositor past the inverse right-hand compositor. The direct
associativity law moves the remaining left-hand compositor past pullback.
The intermediate compositor and its inverse cancel, giving exactly the
interchange for the precomposed square. Equality proofs are irrelevant, so the
calculation applies to all specified names for the composites. -/
@[reassoc]
theorem pullback_square_precomposition
    (A : Type (u + 1)) [CommRing A]
    {W R Q D E : Scheme.{u}} (H : W ⟶ R)
    (J : R ⟶ D) (r : R ⟶ Q) (q : D ⟶ E) (G : Q ⟶ E)
    (sq : CommSq J r q G) (F : W ⟶ D) (a : W ⟶ Q)
    (hF : F = H ≫ J) (ha : a = H ≫ r)
    (sqF : CommSq F a q G) (K : DerivedCategoryModule A E) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) H r a ha).hom.app
        ((upperStar (ModuleCat.{u + 1} A) G).leftDerivedFunctor.obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) H).leftDerivedFunctor.map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K) ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) H J F hF).inv.app
        ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K) =
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sqF).hom.app K := by
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app_assoc
    (ModuleCat.{u + 1} A) H r G a (J ≫ q) (F ≫ q) ha sq.w sqF.w K]
  rw [leftDerivedUpperStarComp_assoc'_app_assoc
    (ModuleCat.{u + 1} A) H J q F (J ≫ q) (F ≫ q) hF rfl rfl K]
  simp only [Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry.Etale
