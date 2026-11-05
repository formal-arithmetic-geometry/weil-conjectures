/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityAmbientExchangeComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale

/-! # The ambient pullback square in levelwise coordinates -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The four exact-to-derived comparisons transport the actual pullback square. -/
lemma purityAmbientPullbackSquareComparison_coordinates (sq : CommSq g' f' f g) :
    (pullbackSquareComparison Λ sq).hom =
      Functor.whiskerLeft L((g)^*⟦Λ⟧)
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f').hom ≫
      Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g).hom
        D((f')^*⟦Λ⟧) ≫
      (Functor.mapDerivedCategorySquareIso (upperStarSquareComparison Λ sq)).hom ≫
      Functor.whiskerLeft D((f)^*⟦Λ⟧)
        (leftDerivedUpperStarIsoMapDerivedCategory Λ g').inv ≫
      Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv
        L((g')^*⟦Λ⟧) := by
  rw [pullbackSquareComparison_eq_leftDerivedFunctorSquareIso]
  ext K
  have h := Adjunction.leftDerivedFunctorSquareIso_hom_app
    (upperStarSquareComparison Λ sq) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← cancel_epi (D((f')^*⟦Λ⟧).map
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv.app K) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f').inv.app (L((g)^*⟦Λ⟧).obj K))]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  rw [h]
  congr 1
  exact (leftDerivedUpperStarIsoMapDerivedCategory Λ g').inv.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv.app K)

end AlgebraicGeometry.ProEtale.CondensedRing
