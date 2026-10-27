/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.Paper.CompactSupportLimitEquationData
import Sheaf.Paper.CompleteIntegralConstantRestriction
import Sheaf.Paper.CompactSupportPathReductionSquare

/-! # Whole-tower realization of compact-support equations

Source: blueprint prop-pur-weil-equivariance-compatibilities, constituent-compatibility
paragraph; Stacks 0941, 099N, 07A7, 0F7B--0F7F
(blueprint: lem-pur-compact-support-limit-equation-realization).

The constant towers are the exact scalar restrictions of the published strict system
interpretation. The normalized scalar comparisons identify their letters with constant-ring
pullback, proper image and open extension. No finite evaluation defines a morphism here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportLimit
open IntegralSystemRealization


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (o : Operations l E) (r : Realizations l E D o)
  {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
  {T : Over (Spec (CommRingCat.of D.k))} (hl : l ≠ D.p)

private theorem integralDomain_output {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {W : Over B} (e : Expression B I X W) (K : ∀ i, Integral l E (X i).left)
    (h : IntegralDomain l E e K) :
    finiteTorConstructibleIntegral l E W.left
      ((e.evaluate (integralInterpretation l E)).obj K) := by
  cases e <;> exact h.1

private theorem limit_square {C N : Type*} [Category C] [Category N]
    (R : C ⥤ N) (L : N ⥤ C) (η : 𝟭 C ⟶ R ⋙ L)
    {A B : C} {M P : N} (qA : R.obj A ⟶ M) (qB : R.obj B ⟶ P)
    (a : A ⟶ B) (s : M ⟶ P) (h : R.map a ≫ qB = qA ≫ s) :
    a ≫ (η.app B ≫ L.map qB) = (η.app A ≫ L.map qA) ≫ L.map s := by
  have hn := η.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← L.map_comp, h, L.map_comp, Category.assoc]

/-- Normalized corners realize equations of actual whole strict towers.
Source: blueprint prop-pur-weil-equivariance-compatibilities, constituent paragraph;
Stacks 0941, 099N, 07A7 and 0F7B--0F7F
(blueprint: lem-pur-compact-support-limit-equation-realization).

Proof: restrict scalars using the complete coefficient equivalence, with its unit and
finite-reduction normalization. Construct q on letters by the inverse reduced completion
unit for pullback, the counit-tensor projection for proper image, and the normalized open
reduction mate for extension by zero. Recursively compose q and set a=L(q)eta, exactly
as corner above. Proper/open strict realization identifies the completed exchange with
the whole-tower proper mate followed by proper image of beta. Tensor reassociation on
K-flat representatives identifies pullback compositors. The coefficient square carries
the open unit and clopen projector to themselves, hence carries the refinement gamma
to strict gamma before inversion. Proper pushforward and its compositor commute with
strict limit on common K-injectives. Invert gamma on the supplied origin domain, then
whisker with the outer proper factors. Naturality proves right whiskering; normalized
system substitution proves left pullback whiskering without a general pullback/limit
commutation. Induction on the finite path cancels its middle corners. Finally cancel
the invertible target corner and use faithfulness of scalar restriction on complete
objects. This proves equality of completed parallel paths and the refinement exchange
and cocycle equations from equality of whole strict paths. Finite evaluations are used
only to detect invertibility on the origin domain, never to infer equality of maps.
-/
theorem compactSupportLimitEquationRealization :
    EquationLaws l E D o r hl (X := X) (T := T) := by
  intro e t ge gt we wt se st K ht ie it
  have he := completeIntegralConstantRestriction l E T.left _
    (integralDomain_output l E e K.obj ie)
  have ht' := completeIntegralConstantRestriction l E T.left _
    (integralDomain_output l E t K.obj it)
  have ce : IsIso (corner l E D o r e ge K) := by
    have := he.1
    dsimp only [corner]
    infer_instance
  have ct : IsIso (corner l E D o r t gt ⟨K.obj, ht⟩) := by
    have := ht'.1
    dsimp only [corner]
    infer_instance
  have square : ∀ s a, Path l E D o r hl K.obj e t s a →
      (GeneratorReduction.H l E T.left).map a ≫ corner l E D o r t gt ⟨K.obj, ht⟩ =
        corner l E D o r e ge K ≫
          (GeneratorReduction.constantLimit l E T.left).map (towerMap l E D o K.obj s) := by
    intro s a h
    have hq := compactSupportPathReductionSquare l E D o r hl e t ge gt we wt se st
      K ht ie it s a h
    exact limit_square (GeneratorReduction.constantReduction l E T.left)
      (GeneratorReduction.constantLimit l E T.left)
      ((sfCbcSite T.left).unit _ (sfCbcModelIdeal (GeneratorReduction.constantDatum l E)))
      (reductionComparison l E D o r e ge K).hom
      (reductionComparison l E D o r t gt ⟨K.obj, ht⟩).hom
      ((GeneratorReduction.H l E T.left).map a) (towerMap l E D o K.obj s) hq
  refine ⟨ce, ct, square, ?_⟩
  intro s s' a a' h h' hs
  apply he.2 _ (integralDomain_output l E t K.obj it)
  apply (cancel_mono (corner l E D o r t gt ⟨K.obj, ht⟩)).1
  rw [square s a h, square s' a' h', hs]

end WeilConjectures.CompactSupportLimit
