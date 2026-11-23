/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.RightDerivedFunctorCountableProducts

/-!
# Right derived functors and countable derived limits

Source: Stacks Project, Injectives, Lemma Tag 08U1.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- If an additive functor on sheaves of modules commutes with countable products,
its unbounded right derived functor sends every specified Roos triangle to a Roos
triangle. The comparison of product vertices respects each projection.
Stacks Project, Injectives, Lemma Tag 08U1. -/
theorem rightDerivedFunctor_isDerivedLimitTriangle (X : Scheme.{u})
    (F : X.Modules ⥤ AddCommGrpCat.{u}) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    [Abelian.HasKInjectiveResolutions X.Modules]
    [Abelian.HasKInjectiveResolutions AddCommGrpCat.{u}]
    [HasDerivedCategory X.Modules] [HasDerivedCategory AddCommGrpCat.{u}]
    {K : ℕ → DerivedCategory X.Modules}
    (f : ∀ n, K (n + 1) ⟶ K n) (L : DerivedCategory X.Modules)
    (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (h : CategoryTheory.IsDerivedLimitTriangle f L p δ) :
    ∃ e : F.rightDerivedFunctor.obj (∏ᶜ K) ≅
        ∏ᶜ (fun n => F.rightDerivedFunctor.obj (K n)),
      (∀ n, e.hom ≫ Pi.π _ n = F.rightDerivedFunctor.map (Pi.π K n)) ∧
      CategoryTheory.IsDerivedLimitTriangle (fun n => F.rightDerivedFunctor.map (f n))
        (F.rightDerivedFunctor.obj L) (F.rightDerivedFunctor.map p ≫ e.hom)
        (e.inv ≫ F.rightDerivedFunctor.map δ ≫
          (F.rightDerivedFunctor.commShiftIso (1 : ℤ)).hom.app L) := by
  let Φ := F.rightDerivedFunctor
  have := rightDerivedFunctor_preservesCountableProducts X F
  let e := PreservesProduct.iso Φ K
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = Φ.map (Pi.π K n) := by
    simp [e]
  refine ⟨e, he, ?_⟩
  have ht : Φ.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ Φ.map (f n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_comp_π, Functor.map_sub]
    rw [← Category.assoc, he, ← Functor.map_comp]
    rw [← Functor.map_comp, Pi.lift_comp_π, Category.id_comp, Functor.map_comp]
  exact Pretriangulated.isomorphic_distinguished _ (Φ.map_distinguished _ h) _
    (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm
      (by change (Φ.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ Φ.map p; simp)
      (by
        change towerTransitionEndomorphism (fun n ↦ Φ.map (f n)) ≫ e.inv =
          e.inv ≫ Φ.map (towerTransitionEndomorphism f)
        apply (cancel_mono e.hom).1
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc] using congrArg (fun t ↦ e.inv ≫ t) ht.symm)
      (by
        change (e.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L) ≫
          (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
            e.inv ≫ (Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app L)
        simp))

end AlgebraicGeometry.Scheme
