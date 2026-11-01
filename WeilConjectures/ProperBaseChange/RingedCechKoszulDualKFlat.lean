/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
-- Reuse the private product-projection and internal-Hom zero lemmas.
import all WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! K-flatness of the finite dual Koszul tower terms.
Source: Stacks Project, More on Algebra, Tag 0913.
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-kflat).
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-kflat)
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

-- Only the two supported rows contribute to a total-complex term.
set_option synthInstance.maxSize 2048 in
private noncomputable def totalTwoXIso
    {A : Type*} [Category A] [Preadditive A] [HasZeroObject A]
    [HasBinaryBiproducts A]
    (K : HomologicalComplex₂ A (.up ℤ) (.up ℤ)) [K.HasTotal (.up ℤ)]
    (hz : ∀ p q : ℤ, p ≠ 0 → p ≠ 1 → IsZero ((K.X p).X q)) (n : ℤ) :
    (K.total (.up ℤ)).X n ≅ (K.X 0).X n ⊞ (K.X 1).X (n - 1) := by
  classical
  let f (p q : ℤ) (h : p + q = n) :
      (K.X p).X q ⟶ (K.X 0).X n ⊞ (K.X 1).X (n - 1) :=
    if hp : p = 0 then
      (K.XXIsoOfEq _ _ _ hp (by omega)).hom ≫ biprod.inl
    else if hp : p = 1 then
      (K.XXIsoOfEq _ _ _ hp (by omega)).hom ≫ biprod.inr
    else 0
  let a := K.totalDesc (c₁₂ := .up ℤ) f
  let v := biprod.desc (K.ιTotal (.up ℤ) 0 n n (by simp))
    (K.ιTotal (.up ℤ) 1 (n - 1) n (by change 1 + (n - 1) = n; omega))
  refine ⟨a, v, ?_, ?_⟩
  · apply HomologicalComplex₂.total.hom_ext
    intro p q h
    change p + q = n at h
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
    by_cases hp : p = 0
    · subst p
      have hq : q = n := by omega
      subst q
      simp [f, v]
    · by_cases hp' : p = 1
      · subst p
        have hq : q = n - 1 := by omega
        subst q
        simp [f, v]
      · exact (hz p q hp hp').eq_of_src _ _
  · apply biprod.hom_ext'
    · simp [v, a, f, HomologicalComplex₂.ι_totalDesc]
    · simp [v, a, f, HomologicalComplex₂.ι_totalDesc]

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

-- The two nonzero terms of a Koszul factor are both the tensor unit.
set_option synthInstance.maxSize 2048 in
open MonoidalCategory in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxSize 2048 in
end CategoryTheory
