/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationCycles
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Evaluation for finite-free complexes with zero differentials

## References

* Stacks Project, Tag 0BQY, the finite-free Hom calculation; Tag 0A8X
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

private theorem finiteFree_hom_preservesHomology
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u}) (r : ℕ)
    (M : SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hM : M ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    [((SheafOfModules.homFunctor R).obj (op M)).PreservesZeroMorphisms] :
    ((SheafOfModules.homFunctor R).obj (op M)).PreservesHomology := by
  let H := (SheafOfModules.homFunctor R).obj (op M)
  let : H.Additive := ⟨by
    intro A B f g
    apply SheafOfModules.hom_ext
    ext U φ
    rfl⟩
  exact (Functor.exact_tfae H).out 1 3 |>.mp (by
    intro T hT
    obtain ⟨hz, hs, _⟩ := SheafOfModules.finiteFreeInternalHomExact (R := R) r M hM T hT
    exact hs)

/-- Evaluation for a bounded finite-free zero-differential complex is an isomorphism,
with its action on cycles expressed by two factorization identities.
-/
theorem finiteFreeZero_homologyEvaluation
    {C : Type u} [SmallCategory C] {S : GrothendieckTopology C}
    (R : Sheaf S CommRingCat.{u})
    (E K : CochainComplex (SheafOfModules.{u}
      ((sheafCompose S (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℤ) (hK : ∀ k : ℤ, k ≠ 0 → IsZero (K.homology k))
    (hzero : ∀ a b : ℤ, E.d a b = 0)
    (hsupp : ∃ a b : ℤ, ∀ k : ℤ, k < a ∨ b < k → IsZero (E.X k))
    (hfree : ∀ k : ℤ, ∃ r : ℕ, Nonempty (E.X k ≅
      SheafOfModules.free (ULift.{u} (Fin r)))) :
    let P := homComplex (R := R) E K
    let π := (Classical.choose (homComplex_projections_exists (R := R)))
      E K n (-n) 0 (by omega)
    ∃ f : P.homology n ⟶ SheafOfModules.homObj (R := R)
        (E.homology (-n)) (K.homology 0),
      IsIso f ∧ ∃ c : P.cycles n ⟶
        SheafOfModules.homObj (R := R) (E.cycles (-n)) (K.cycles 0),
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.iCycles 0) =
        P.iCycles n ≫ π ≫ SheafOfModules.homObjMap (R := R) (E.iCycles (-n)) (𝟙 _) ∧
      c ≫ SheafOfModules.homObjMap (R := R) (𝟙 _) (K.homologyπ 0) =
        P.homologyπ n ≫ f ≫ SheafOfModules.homObjMap (R := R) (E.homologyπ (-n)) (𝟙 _) := by
  dsimp
  obtain ⟨f, c, hc₁, hc₂⟩ := finiteFreeZero_homologyEvaluation_cycles R E K n hzero
  have hf := finiteFreeZero_homologyEvaluation_iso R E K n hK hzero hsupp hfree
    f c hc₁ hc₂
  exact ⟨f, hf, c, hc₁, hc₂⟩

end CategoryTheory
