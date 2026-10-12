/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Rlim
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.CompletedBaseChange.TowerLimit
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# The derived category of towers is a sequential derived limit formalism

Let `A` be a Grothendieck abelian category. This file shows that the derived evaluations
`evₙ : D(ℕᵒᵖ ⥤ A) ⥤ D(A)` are jointly conservative
(`DerivedCategory.isIso_of_forall_isIso_towerEval`): homology of complexes of towers is computed
levelwise, and the derived evaluations commute with homology, evaluation being exact.

Together with the Roos triangle `DerivedCategory.isHomotopyLimit_rlimCone`, this makes the
derived category of towers, with `R lim`, a `CategoryTheory.TowerLimitFormalism`
(`DerivedCategory.towerLimitFormalism`). As consequences:

* a levelwise isomorphism of derived towers is an isomorphism, and so is its image under `R lim`
  (`DerivedCategory.isIso_rlim_map_of_forall_isIso`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-- The derived evaluation `evₙ` commutes with the homology functors. -/
noncomputable def towerEvalHomologyIso (n : ℕᵒᵖ) (q : ℤ) :
    homologyFunctor (ℕᵒᵖ ⥤ A) q ⋙ (evaluation ℕᵒᵖ A).obj n ≅
      (towerEval A).obj n ⋙ homologyFunctor A q :=
  ((evaluation ℕᵒᵖ A).obj n).rightDerivedFunctorHomologyFunctorIso q

/-- **Blueprint `lem-weil-pbc-levelwise-isomorphism-cones`** (first assertion, part 1). The
derived evaluations `evₙ : D(ℕᵒᵖ ⥤ A) ⥤ D(A)` are jointly conservative: a morphism of the
derived category of towers whose evaluation at every level is an isomorphism is an
isomorphism. -/
theorem isIso_of_forall_isIso_towerEval {M N : DerivedCategory (ℕᵒᵖ ⥤ A)} (f : M ⟶ N)
    (hf : ∀ n : ℕ, IsIso (((towerEval A).obj (op n)).map f)) : IsIso f := by
  rw [isIso_iff]
  intro q
  have (n : ℕᵒᵖ) : IsIso (((homologyFunctor (ℕᵒᵖ ⥤ A) q).map f).app n) := by
    obtain ⟨n⟩ := n
    have := hf n
    change IsIso ((homologyFunctor (ℕᵒᵖ ⥤ A) q ⋙ (evaluation ℕᵒᵖ A).obj (op n)).map f)
    rw [← NatIso.naturality_2 (towerEvalHomologyIso (op n) q) f]
    dsimp only [Functor.comp_map]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **Blueprint `lemma-weil-pbc-r-lim-levelwise-isomorphism`** (derived-tower form). A morphism
of derived towers whose evaluations are all isomorphisms induces an isomorphism on `R lim`. -/
theorem isIso_rlim_map_of_forall_isIso {M N : DerivedCategory (ℕᵒᵖ ⥤ A)} (f : M ⟶ N)
    (hf : ∀ n : ℕ, IsIso (((towerEval A).obj (op n)).map f)) : IsIso ((rlim A).map f) := by
  have := isIso_of_forall_isIso_towerEval f hf
  infer_instance

variable (A) in
/-- The natural transformation `R lim M ⟶ (evₙ M)ₙ` of the cones `DerivedCategory.rlimCone`. -/
@[simps]
noncomputable def rlimConeπ : rlim A ⋙ Functor.const ℕᵒᵖ ⟶ towerFunctor A where
  app M := (rlimCone A M).π
  naturality _ _ f := by
    ext n
    exact ((rlimπ A n).naturality f)

variable (A) in
/-- **Blueprint `def-weil-pbc-derived-inverse-limit`** (as a formalism). The derived category of
towers `D(ℕᵒᵖ ⥤ A)` over `D(A)`, with the derived evaluations `evₙ`
(`DerivedCategory.towerFunctor`), the derived limit `R lim` and its projections, is a sequential
derived limit formalism: the projections exhibit `R lim M` as the derived limit of `(evₙ M)ₙ`
(Roos triangle, `DerivedCategory.isHomotopyLimit_rlimCone`) and the evaluations are jointly
conservative (`DerivedCategory.isIso_of_forall_isIso_towerEval`). -/
noncomputable def towerLimitFormalism :
    TowerLimitFormalism (DerivedCategory (ℕᵒᵖ ⥤ A)) (DerivedCategory A) where
  tower := towerFunctor A
  rlim := rlim A
  π := rlimConeπ A
  isHomotopyLimit M := isHomotopyLimit_rlimCone M
  isIso_of_forall_isIso f hf := isIso_of_forall_isIso_towerEval f hf

@[simp] lemma towerLimitFormalism_tower : (towerLimitFormalism A).tower = towerFunctor A := rfl

@[simp] lemma towerLimitFormalism_rlim : (towerLimitFormalism A).rlim = rlim A := rfl

@[simp] lemma towerLimitFormalism_π : (towerLimitFormalism A).π = rlimConeπ A := rfl

end DerivedCategory
