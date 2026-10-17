/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.SplitEtaleHypercoverFreeComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!
# The augmented free complex of a split étale hypercover

Blueprint `lem-weil-pbc-hypercover-free-resolution`: the sheafified augmented free complex
`⋯ → ℤ[U_1] → ℤ[U_0] → ℤ[X] → 0` of a split étale hypercover is exact, and for an injective
sheaf `I` the complex of sections `I(U_•)` is a resolution of `I(X)`; the same holds for free
modules over a ring. These are specializations of
`AlgebraicGeometry.SplitEtaleHypercover.quasiIso_augmentation` and
`AlgebraicGeometry.SplitEtaleHypercover.injective_section_cohomology`.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SplitEtaleHypercover

lemma freeAbelianGroup_exists_finite {S : Type w} (x : FreeAbelianGroup S) :
    ∃ F : Set S, F.Finite ∧ x ∈ Set.range (FreeAbelianGroup.map (Subtype.val : F → S)) := by
  induction x using FreeAbelianGroup.induction_on with
  | zero => exact ⟨∅, Set.finite_empty, 0, map_zero _⟩
  | of s =>
    exact ⟨{s}, Set.finite_singleton s, FreeAbelianGroup.of ⟨s, rfl⟩,
      FreeAbelianGroup.map_of_apply _⟩
  | neg s h =>
    obtain ⟨F, hF, y, hy⟩ := h
    exact ⟨F, hF, -y, by rw [map_neg, hy]⟩
  | add x y hx hy =>
    obtain ⟨F, hF, a, rfl⟩ := hx
    obtain ⟨G, hG, b, rfl⟩ := hy
    refine ⟨F ∪ G, hF.union hG,
      FreeAbelianGroup.map (Set.inclusion Set.subset_union_left) a +
        FreeAbelianGroup.map (Set.inclusion Set.subset_union_right) b, ?_⟩
    rw [map_add, ← FreeAbelianGroup.map_comp_apply, ← FreeAbelianGroup.map_comp_apply]
    rfl

lemma finsupp_exists_finite {S : Type w} {R : Type*} [Semiring R] (x : S →₀ R) :
    ∃ F : Set S, F.Finite ∧ x ∈ Set.range (Finsupp.mapDomain (M := R) (Subtype.val : F → S)) := by
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨∅, Set.finite_empty, 0, Finsupp.mapDomain_zero⟩
  | single s r =>
    exact ⟨{s}, Set.finite_singleton s, Finsupp.single ⟨s, rfl⟩ r, Finsupp.mapDomain_single⟩
  | add x y hx hy =>
    obtain ⟨F, hF, a, rfl⟩ := hx
    obtain ⟨G, hG, b, rfl⟩ := hy
    refine ⟨F ∪ G, hF.union hG,
      Finsupp.mapDomain (Set.inclusion Set.subset_union_left) a +
        Finsupp.mapDomain (Set.inclusion Set.subset_union_right) b, ?_⟩
    rw [Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    rfl

/-- Blueprint `lem-weil-pbc-hypercover-free-resolution`: the sheafified augmented free abelian
complex of a split étale hypercover is exact. -/
theorem freeAbelian_augmentation_quasiIso
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) AddCommGrpCat.{w + 1}).obj
            AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{w + 1})).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))) :=
  U.quasiIso_augmentation AddCommGrpCat.free (fun _ _ _ ↦ rfl)
    (fun _ x ↦ freeAbelianGroup_exists_finite x)

/-- Blueprint `lem-weil-pbc-hypercover-free-resolution`: for an injective abelian sheaf `I`,
the complex of sections `I(U_•)` of a split étale hypercover resolves `I(X)`. -/
theorem injective_abelian_section_cohomology
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X)
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) [Injective I] :
    Function.Injective
        (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op) ∧
      (∀ s : I.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk 0)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
            s ∈ Set.range (I.obj.map (terminal.from
              (U.simplicial.obj (op (SimplexCategory.mk 0)))).op)) ∧
      ∀ p : ℕ, 0 < p → IsZero
        (((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{w + 1}).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) :=
  U.injective_section_cohomology AddCommGrpCat.free (fun _ _ _ ↦ rfl)
    (fun _ x ↦ freeAbelianGroup_exists_finite x) AddCommGrpCat.adj
    (fun S h ↦ (ShortComplex.ab_exact_iff S).2 h) I

/-- Blueprint `lem-weil-pbc-hypercover-free-resolution`: the sheafified augmented complex of
free modules of a split étale hypercover is exact. -/
theorem freeModule_augmentation_quasiIso
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [Ring R] :
    QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.whiskeringObj X.Etale _
        (uliftYoneda.{w + 1} ⋙
          (Functor.whiskeringRight X.Etaleᵒᵖ (Type (w + 1)) (ModuleCat.{w + 1} R)).obj
            (ModuleCat.free R) ⋙
          presheafToSheaf X.smallEtaleTopology (ModuleCat.{w + 1} R))).obj
        (U.simplicial.augmentOfIsTerminal (terminalIsTerminal (C := X.Etale))))) :=
  U.quasiIso_augmentation (ModuleCat.free R) (fun _ _ _ ↦ rfl)
    (fun _ x ↦ finsupp_exists_finite x)

/-- Blueprint `lem-weil-pbc-hypercover-free-resolution`: for an injective sheaf of modules
`I`, the complex of sections `I(U_•)` of a split étale hypercover resolves `I(X)`. -/
theorem injective_module_section_cohomology
    {X : Scheme.{w}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : SplitEtaleHypercover X) (R : Type (w + 1)) [Ring R]
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{w + 1} R)) [Injective I] :
    Function.Injective
        (I.obj.map (terminal.from
          (U.simplicial.obj (op (SimplexCategory.mk 0)))).op) ∧
      (∀ s : I.obj.obj (op (U.simplicial.obj (op (SimplexCategory.mk 0)))),
        ((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{w + 1} R)).obj
          (U.simplicial.rightOp ⋙ I.obj)).d 0 1 s = 0 ↔
            s ∈ Set.range (I.obj.map (terminal.from
              (U.simplicial.obj (op (SimplexCategory.mk 0)))).op)) ∧
      ∀ p : ℕ, 0 < p → IsZero
        (((AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{w + 1} R)).obj
          (U.simplicial.rightOp ⋙ I.obj)).homology p) :=
  U.injective_section_cohomology (ModuleCat.free R) (fun _ _ _ ↦ rfl)
    (fun _ x ↦ finsupp_exists_finite x) (ModuleCat.adj R)
    (fun S h ↦ (ShortComplex.moduleCat_exact_iff S).2 h) I

end AlgebraicGeometry.SplitEtaleHypercover
