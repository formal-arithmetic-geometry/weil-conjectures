/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverCohomologyColimit
public import WeilConjectures.Algebra.Homology.ConcreteCohomologyClass

/-!
# A criterion for the colimit property of hypercover cohomology

If compatible maps `H^q(C(U, F)) ⟶ H(F)` are jointly surjective, if a class mapping to zero
dies on a refinement, and if any two finite split hypercovers have a common refinement, then
`H(F)` is the colimit of the `H^q(C(U, F))` over refinements, provided morphisms of `A` can be
built from functions which are locally (on pairs of elements) given by morphisms.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  {A : Type w} [Category.{v} A] [Abelian A]

lemma cohomologyRefinement_comp {U V W : FiniteSplitEtaleHypercover X} (h : W.Refinement U)
    (f : U.Refinement V) (q : ℕ) :
    cohomologyRefinement A (h ≫ f) q = cohomologyRefinement A f q ≫ cohomologyRefinement A h q := by
  ext F
  simp only [cohomologyRefinement, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, ← Functor.map_comp]
  rw [NatTrans.rightOp_comp, Functor.map_comp, NatTrans.comp_app]

variable {FA : A → A → Type*} {CA : A → Type v}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{v} A FA]
  [∀ X, AddCommGroup (CA X)] [∀ X Y, AddMonoidHomClass (FA X Y) (CA X) (CA Y)]

/-- Morphisms of `A` can be constructed from functions which on any two elements are given by
a morphism. -/
def HasLocalMk (A : Type w) [Category.{v} A] {FA : A → A → Type*} {CA : A → Type v}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{v} A FA] : Prop :=
  ∀ {Y B : A} (φ : ToType Y → ToType B),
    (∀ y₁ y₂ : ToType Y, ∃ (Z : A) (a : Z ⟶ Y) (b : Z ⟶ B) (z₁ z₂ : ToType Z),
      a z₁ = y₁ ∧ a z₂ = y₂ ∧ ∀ z, φ (a z) = b z) →
    ∃ e : Y ⟶ B, ∀ y, e y = φ y

theorem isCohomologyColimit_of (hmk : HasLocalMk A) (q : ℕ)
    (H : Sheaf X.smallEtaleTopology A ⥤ A)
    (hhom : ∀ (U V : FiniteSplitEtaleHypercover X) (f g : U.Refinement V),
      isRefinementHomotopic f g → cohomologyRefinement A f q = cohomologyRefinement A g q)
    (c : ∀ U : FiniteSplitEtaleHypercover X, cohomologyFunctor A U q ⟶ H)
    (hc : ∀ (U V : FiniteSplitEtaleHypercover X) (f : U.Refinement V),
      cohomologyRefinement A f q ≫ c U = c V)
    (hS : ∀ (F : Sheaf X.smallEtaleTopology A) (y : ToType (H.obj F)),
      ∃ (U : FiniteSplitEtaleHypercover X) (x : ToType ((cohomologyFunctor A U q).obj F)),
        (c U).app F x = y)
    (hI : ∀ (U : FiniteSplitEtaleHypercover X) (F : Sheaf X.smallEtaleTopology A)
      (x : ToType ((cohomologyFunctor A U q).obj F)), (c U).app F x = 0 →
        ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
          (cohomologyRefinement A f q).app F x = 0)
    (hcommon : ∀ U V : FiniteSplitEtaleHypercover X,
      ∃ W : FiniteSplitEtaleHypercover X, Nonempty (W.Refinement U) ∧
        Nonempty (W.Refinement V)) :
    IsCohomologyColimit A q H := by
  refine ⟨hhom, c, hc, fun F B d hd ↦ ?_⟩
  have hcF : ∀ (U V : FiniteSplitEtaleHypercover X) (f : U.Refinement V) x,
      (c U).app F ((cohomologyRefinement A f q).app F x) = (c V).app F x := fun U V f x ↦ by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, hc]
  have hdF : ∀ (U V : FiniteSplitEtaleHypercover X) (f : U.Refinement V) x,
      d U ((cohomologyRefinement A f q).app F x) = d V x := fun U V f x ↦ by
    rw [← ConcreteCategory.comp_apply, hd]
  -- well-definedness
  have hwd : ∀ (U V : FiniteSplitEtaleHypercover X) x x',
      (c U).app F x = (c V).app F x' → d U x = d V x' := by
    intro U V x x' hxx'
    obtain ⟨W, ⟨f⟩, ⟨g⟩⟩ := hcommon U V
    have h0 : (c W).app F ((cohomologyRefinement A f q).app F x -
        (cohomologyRefinement A g q).app F x') = 0 := by
      rw [map_sub, hcF, hcF, hxx', sub_self]
    obtain ⟨W', h, hh⟩ := hI W F _ h0
    rw [map_sub, sub_eq_zero, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← NatTrans.comp_app, ← NatTrans.comp_app, ← cohomologyRefinement_comp,
      ← cohomologyRefinement_comp] at hh
    rw [← hdF W' U (h ≫ f) x, hh, hdF]
  choose U₀ x₀ hx₀ using hS F
  let φ : ToType (H.obj F) → ToType B := fun y ↦ d (U₀ y) (x₀ y)
  have hφ : ∀ U x, φ ((c U).app F x) = d U x := fun U x ↦ hwd _ _ _ _ (hx₀ _)
  obtain ⟨e, he⟩ := hmk φ (by
    intro y₁ y₂
    obtain ⟨W, ⟨f⟩, ⟨g⟩⟩ := hcommon (U₀ y₁) (U₀ y₂)
    refine ⟨(cohomologyFunctor A W q).obj F, (c W).app F, d W,
      (cohomologyRefinement A f q).app F (x₀ y₁), (cohomologyRefinement A g q).app F (x₀ y₂),
      by rw [hcF, hx₀], by rw [hcF, hx₀], fun z ↦ hφ W z⟩)
  refine ⟨e, fun U ↦ ConcreteCategory.hom_ext _ _ fun x ↦ ?_, fun e' he' ↦ ?_⟩
  · rw [ConcreteCategory.comp_apply, he, hφ]
  · refine ConcreteCategory.hom_ext _ _ fun y ↦ ?_
    rw [he, ← hx₀ y, ← ConcreteCategory.comp_apply, he' (U₀ y), hφ]

end AlgebraicGeometry.FiniteSplitEtaleHypercover
