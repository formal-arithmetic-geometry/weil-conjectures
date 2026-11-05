/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityK4NativeFiniteFreeSite
public import WeilConjectures.WeilSheaf.SmoothPurityComparisonRestriction

/-! # Free-sheaf site comparison and geometric pullback -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory

private lemma k4Native_forward_square_of_two_inverses {C : Type*} [Category C]
    {A B C' D E : C} (a : A ≅ B) (b : B ≅ C') (d : D ≅ E)
    (u : C' ⟶ E) (v : A ⟶ D)
    (h : u ≫ d.inv = b.inv ≫ a.inv ≫ v) :
    a.hom ≫ b.hom ≫ u = v ≫ d.hom := by
  apply (cancel_mono d.inv).mp
  simp only [Category.assoc, h, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.K4Native

open Scheme CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  (n : ℕ) {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The free pro-étale sheaf on the inverse image of an étale abelian sheaf
commutes with geometric pullback. -/
noncomputable def purityComparisonFreePullbackIso :
    (ν^*(Y)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf ℓ E n Y) ⋙
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)] ≅
      Etale.upperStar Ab.{u + 1} g ⋙ (ν^*(X)[Ab.{u + 1}] ⋙ purityFiniteFreeSheaf ℓ E n X) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (purityFiniteFreeSheafPullbackIso ℓ E n g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (comparisonUpperStarUpperStarIso Ab.{u + 1} g) _ ≪≫
    Functor.associator _ _ _

lemma purityComparisonFreePullbackIso_conjugate :
    conjugateIsoEquiv
      ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction ℓ E n X)))
      (((comparisonAdjunction Ab.{u + 1} Y).comp (purityFiniteFreeSheafAdjunction ℓ E n Y)).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g))
      (purityComparisonFreePullbackIso ℓ E n g) = Iso.refl _ := by
  unfold purityComparisonFreePullbackIso
  rw [conjugateIsoEquiv_trans _ ((comparisonAdjunction Ab.{u + 1} Y).comp
      ((purityFiniteFreeSheafAdjunction ℓ E n Y).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g))),
    conjugateIsoEquiv_trans _ ((comparisonAdjunction Ab.{u + 1} Y).comp
      ((upperStarLowerStarAdjunction Ab.{u + 1} g).comp
        (purityFiniteFreeSheafAdjunction ℓ E n X))),
    conjugateIsoEquiv_trans _ (((comparisonAdjunction Ab.{u + 1} Y).comp
      (upperStarLowerStarAdjunction Ab.{u + 1} g)).comp
        (purityFiniteFreeSheafAdjunction ℓ E n X)),
    conjugateIsoEquiv_trans _ (((Etale.upperStarLowerStarAdjunction Ab.{u + 1} g).comp
      (comparisonAdjunction Ab.{u + 1} X)).comp (purityFiniteFreeSheafAdjunction ℓ E n X)),
    conjugateIsoEquiv_associator, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator]
  simp only [purityFiniteFreeSheafPullbackIso, comparisonUpperStarUpperStarIso,
    lowerStarComparisonLowerStarIso, Equiv.apply_symm_apply]
  ext N
  simp
  rfl

/-- The site comparison respects the free-sheaf geometric datum. -/
lemma purity_comparisonFreeSheaf_pullback
    (M : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          ((Etale.upperStarExtendScalarsIso (integersModPowCoeff.{u} ℓ E n) g).hom.app M) ≫
        (purityComparisonFreeSheafIso ℓ E n X).inv.app ((Etale.upperStar Ab.{u + 1} g).obj M) =
      (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).inv.app
          ((Etale.extendScalars (integersModPowCoeff.{u} ℓ E n) Y).obj M) ≫
        (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          ((purityComparisonFreeSheafIso ℓ E n Y).inv.app M) ≫
        (purityComparisonFreePullbackIso ℓ E n g).hom.app M := by
  apply purity_free_pullback_cube
    (Etale.upperStarLowerStarAdjunction Ab.{u + 1} g)
    (Etale.extendScalarsAdjunction (integersModPowCoeff.{u} ℓ E n) Y)
    (Etale.extendScalarsAdjunction (integersModPowCoeff.{u} ℓ E n) X)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g)
    (comparisonAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Y)
    (comparisonAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) X)
    ((comparisonAdjunction Ab.{u + 1} Y).comp (purityFiniteFreeSheafAdjunction ℓ E n Y))
    ((comparisonAdjunction Ab.{u + 1} X).comp (purityFiniteFreeSheafAdjunction ℓ E n X))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g)
    (Etale.upperStarExtendScalarsIso (integersModPowCoeff.{u} ℓ E n) g)
    (purityComparisonFreePullbackIso ℓ E n g)
    (purityComparisonFreeSheafIso ℓ E n Y).symm
    (purityComparisonFreeSheafIso ℓ E n X).symm
    (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).symm
  intro N
  rw [purityComparisonFreePullbackIso_conjugate]
  simp only [purityComparisonFreeSheafIso, comparisonUpperStarUpperStarIso,
    Etale.upperStarExtendScalarsIso, purity_leftAdjointUniq_ofNatIsoRight,
    Adjunction.symm_conjugateIsoEquiv_symm_apply, Equiv.apply_symm_apply,
    lowerStarComparisonLowerStarIso, Iso.refl_symm, Iso.refl_hom, NatTrans.id_app,
    NatIso.ofComponents_hom_app, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Forward form of the free-sheaf site comparison square. -/
lemma purity_comparisonFreeSheaf_pullback_forward
    (M : Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    (g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          ((purityComparisonFreeSheafIso ℓ E n Y).hom.app M) ≫
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).hom.app
          ((Etale.extendScalars (integersModPowCoeff.{u} ℓ E n) Y).obj M) ≫
        ν^*(X)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].map
          ((Etale.upperStarExtendScalarsIso (integersModPowCoeff.{u} ℓ E n) g).hom.app M) =
      (purityComparisonFreePullbackIso ℓ E n g).hom.app M ≫
        (purityComparisonFreeSheafIso ℓ E n X).hom.app ((Etale.upperStar Ab.{u + 1} g).obj M) := by
  exact k4Native_forward_square_of_two_inverses
    ((g)^*[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)].mapIso
      ((purityComparisonFreeSheafIso ℓ E n Y).app M))
    ((comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g).app
      ((Etale.extendScalars (integersModPowCoeff.{u} ℓ E n) Y).obj M))
    ((purityComparisonFreeSheafIso ℓ E n X).app ((Etale.upperStar Ab.{u + 1} g).obj M))
    _ _ (purity_comparisonFreeSheaf_pullback ℓ E n g M)

end AlgebraicGeometry.ProEtale.K4Native
