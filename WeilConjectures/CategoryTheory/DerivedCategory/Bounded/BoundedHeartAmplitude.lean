/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.TruncationTriangle

/-!
# Finite cohomological amplitude from bounds on cohomology objects

## References

* Stacks Project, Tags 08J5 and 0G2A.
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace DerivedCategory

/-- An exact triangulated functor bounded on a class of heart objects has the corresponding
finite cohomological amplitude on bounded objects with cohomology in that class.
Stacks Project, Tags 08J5 and 0G2A. -/
theorem bounded_heart_amplitude
    (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ] [T.IsTriangulated]
    (S : A → Prop)
    (_hSiso : ∀ (M N : A), (M ≅ N) → S M → S N)
    (_hSzero : S (0 : A))
    (c d : ℤ) (_hcd : c ≤ d)
    (_hHeart : ∀ (M : A), S M → ∀ (i : ℤ), i < c ∨ d < i →
      IsZero ((homologyFunctor B i).obj (T.obj ((singleFunctor A 0).obj M))))
    (a b : ℤ) (_hab : a ≤ b) (K : DerivedCategory A)
    (_hK : ∀ (r : ℤ), r < a ∨ b < r → IsZero ((homologyFunctor A r).obj K))
    (_hKS : ∀ (r : ℤ), S ((homologyFunctor A r).obj K)) :
    ∀ (i : ℤ), i < a + c ∨ b + d < i → IsZero ((homologyFunctor B i).obj (T.obj K)) := by
  let C : CochainComplex A ℤ := Q.objPreimage K
  let e : Q.obj C ≅ K := Q.objObjPreimageIso K
  have hC (r : ℤ) (hr : r < a ∨ b < r) : IsZero (C.homology r) :=
    (_hK r hr).of_iso
      ((homologyFunctorFactors A r).symm.app C ≪≫ (homologyFunctor A r).mapIso e)
  have hCS (r : ℤ) : S (C.homology r) :=
    _hSiso _ _ ((homologyFunctor A r).mapIso e.symm ≪≫
      (homologyFunctorFactors A r).app C) (_hKS r)
  have hCGE : C.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro r hr
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hC r (Or.inl hr))
  have hCLE : C.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro r hr
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (hC r (Or.inr hr))
  have hsingle (q i : ℤ) (hq : a ≤ q ∧ q ≤ b)
      (hi : i < a + c ∨ b + d < i) :
      IsZero ((homologyFunctor B i).obj
        (T.obj ((singleFunctor A q).obj (C.homology q)))) := by
    apply (_hHeart _ (hCS q) (i - q) (by rcases hi with hi | hi <;> omega)).of_iso
    exact (homologyFunctor B i).mapIso (T.mapIso
        (((singleFunctors A).shiftIso (-q) q 0 (by simp)).app (C.homology q)).symm ≪≫
      (T.commShiftIso (-q)).app _) ≪≫
      ((homologyFunctor B 0).shiftIso (-q) i (i - q) (by omega)).app _
  have htrunc : ∀ n : ℕ, a - 1 + n ≤ b → ∀ i : ℤ,
      i < a + c ∨ b + d < i →
      IsZero ((homologyFunctor B i).obj (T.obj (Q.obj (C.truncLE (a - 1 + n))))) := by
    intro n
    induction n with
    | zero =>
      intro hn i hi
      have : (C.truncLE (a - 1)).IsGE a :=
        (((truncation_triangle A (a - 1)).2.2 C a).2 hCGE).2.1
      have hz : IsZero (Q.obj (C.truncLE (a - 1))) :=
        TStructure.t.isZero _ (a - 1) a (by omega)
      simpa using (homologyFunctor B i).map_isZero (T.map_isZero hz)
    | succ n ih =>
      intro hn i hi
      let q : ℤ := a - 1 + (n + 1 : ℕ)
      obtain ⟨f, g, _, _, k, hk, _⟩ := (truncation_triangle A q).1 C
      have hdist := T.map_distinguished _ hk
      have h₁ : IsZero ((homologyFunctor B i).obj (T.obj (Q.obj (C.truncLE (q - 1))))) := by
        have heq : q - 1 = a - 1 + n := by dsimp [q]; omega
        rw [heq]
        exact ih (by omega) i hi
      have h₃ := hsingle q i (by dsimp [q]; constructor <;> omega) hi
      exact (HomologySequence.exact₂ _ hdist i).isZero_of_both_zeros
        (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  have hlast (i : ℤ) (hi : i < a + c ∨ b + d < i) :
      IsZero ((homologyFunctor B i).obj (T.obj (Q.obj (C.truncLE b)))) := by
    have heq : a - 1 + ((b - a + 1).toNat : ℤ) = b := by omega
    simpa only [heq] using htrunc (b - a + 1).toNat (by omega) i hi
  intro i hi
  exact (hlast i hi).of_iso
    ((homologyFunctor B i).mapIso
      (T.mapIso ((asIso (Q.map (C.ιTruncLE b))) ≪≫ e)).symm)

end DerivedCategory
