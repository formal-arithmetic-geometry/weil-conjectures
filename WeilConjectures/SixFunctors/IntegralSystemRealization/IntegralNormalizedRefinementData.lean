/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.CompletedShriekCompositionLaws
public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionData

/-! # Words and outside contexts for normalized integral refinement

These are the original constructions from IntegralNormalizedRefinementPasting,
separated so that the realization comparison can be proved independently.
(blueprint: def-sf-normalized-refinement-context-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The one-input compactification word B_c=S_p J_j, with its actual scheme indices.
Source: blueprint extracted normalized coefficient argument, step 10
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def normalizedRefinementWord {B : Scheme.{u}} {X Y : Over B} (f : X ⟶ Y)
    (c : Compactification f.left) : Expression B (ULift.{u} Unit) (fun _ ↦ X) Y :=
  .compactSupport f c (.var ⟨()⟩)

/-- The finite-type geometric proof for the actual one-input compactification word.
Source: blueprint step 10, finite-type domain
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
abbrev normalizedRefinementGeometric {B : Scheme.{u}} {X Y : Over B}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) : (normalizedRefinementWord f c).geometric :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, True.intro⟩

/-- The inverse of the existing reverse system refinement, wherever it is invertible.
The total inverse-or-zero convention is the recorded GeneratorReduction convention;
the theorem below asserts invertibility, so its zero branch is never used there.
Source: blueprint step 10, inversion of intrinsic system pasting
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def normalizedRefinementSystemMap {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) (M : System l E X) :
    (completedShriekF l E o c).obj M ⟶ (completedShriekF l E o d).obj M :=
  GeneratorReduction.inverseOrZero ((completedShriekRefinement l E R r).app M)

/-- Finite outer proper/open factors in a refinement diagram, retaining their order.
This is notation for the whiskering clause, not additional geometric data.
Source: blueprint step 10; Stacks 0F7C, 0F7D
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
inductive NormalizedRefinementContext (B : Scheme.{u}) (V : Over B) : Over B →
    Type (u + 1) where
  | hole : NormalizedRefinementContext B V V
  | push {U W : Over B} (f : U ⟶ W) (hf : IsProper f.left)
      (q : NormalizedRefinementContext B V U) : NormalizedRefinementContext B V W
  | shriek {U W : Over B} (j : U ⟶ W) (hj : IsOpenImmersion j.left)
      (hq : QuasiCompact j.left) (q : NormalizedRefinementContext B V U) :
      NormalizedRefinementContext B V W

/-- Substitute the compactification expression into the same outer proper/open word.
Source: blueprint step 10, permitted whiskering
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def NormalizedRefinementContext.plug {B : Scheme.{u}} {V W : Over B}
    (q : NormalizedRefinementContext B V W) {I : Type u} {X : I → Over B}
    (e : Expression B I X V) : Expression B I X W :=
  match q with
  | .hole => e
  | .push f hf q => .push f hf (q.plug e)
  | .shriek j hj hq q => .shriek j hj hq (q.plug e)

/-- Interpret the outside factors as the actual composite functor in either calculus.
Source: blueprint step 10, whiskering before evaluation
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def NormalizedRefinementContext.evaluate {B : Scheme.{u}} {V W : Over B}
    (q : NormalizedRefinementContext B V W)
    {C : Scheme.{u} → Type v} [∀ T, Category.{w} (C T)]
    (d : Interpretation C) : C V.left ⥤ C W.left :=
  match q with
  | .hole => 𝟭 _
  | .push f _ q => q.evaluate d ⋙ d.push f.left
  | .shriek j hj _ q =>
    letI := hj
    q.evaluate d ⋙ d.shriek j.left

/-- Canonical associators identify substitution with application of the outer functor.
Source: blueprint step 10, identical outside factors
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def NormalizedRefinementContext.evaluationIso {B : Scheme.{u}} {V W : Over B}
    (q : NormalizedRefinementContext B V W)
    {C : Scheme.{u} → Type v} [∀ T, Category.{w} (C T)] (d : Interpretation C)
    {I : Type u} {X : I → Over B} (e : Expression B I X V) :
    (q.plug e).evaluate d ≅ e.evaluate d ⋙ q.evaluate d :=
  match q with
  | .hole => (Functor.rightUnitor (e.evaluate d)).symm
  | .push f _ q =>
    Functor.isoWhiskerRight (q.evaluationIso d e) (d.push f.left) ≪≫
      Functor.associator _ _ _
  | .shriek j hj _ q =>
    letI := hj
    Functor.isoWhiskerRight (q.evaluationIso d e) (d.shriek j.left) ≪≫
      Functor.associator _ _ _

/-- The prescribed realization in outside-factor coordinates, using only associators.
Source: blueprint step 10, whiskered realization
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
def NormalizedRefinementContext.realization {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {V W : Over (Spec (CommRingCat.of D.k))}
    (q : NormalizedRefinementContext _ V W) (e : Expression _ I X V)
    (g : (q.plug e).geometric) (K : ∀ i, Integral l E (X i).left)
    (h : (q.plug e).domain l E o K) :
    (coefficientSequenceLimit l E W.left).obj
        ((q.evaluate (systemInterpretation l E o)).obj
          (e.systemObj l E o ((inputReduction l E X).obj K))) ≅
      (q.evaluate (integralInterpretation l E)).obj
        ((e.evaluate (integralInterpretation l E)).obj K) :=
  ((coefficientSequenceLimit l E W.left).mapIso
    ((q.evaluationIso (systemInterpretation l E o) e).app
      ((inputReduction l E X).obj K))).symm ≪≫
    (R.comparison (q.plug e) g).app ⟨K, h⟩ ≪≫
    (q.evaluationIso (integralInterpretation l E) e).app K

/-- Transport the bundled finite-type structure to the same typeclass structure map.
Source: blueprint finite-type convention
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
instance normalizedRefinementFiniteType {B : Scheme.{u}} (X : Over B)
    [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (X.left ↘ B) :=
  inferInstanceAs (LocallyOfFiniteType X.hom)

/-- Transport quasi-compactness to the same bundled structure morphism.
Source: blueprint finite-type convention
(blueprint: lem-sf-integral-normalized-refinement-pasting). -/
instance normalizedRefinementQuasiCompact {B : Scheme.{u}} (X : Over B)
    [QuasiCompact X.hom] : QuasiCompact (X.left ↘ B) :=
  inferInstanceAs (QuasiCompact X.hom)

end WeilConjectures.IntegralSystemRealization
