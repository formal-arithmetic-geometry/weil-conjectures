/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalPurityScalarModels
public import WeilConjectures.AlgebraicGeometry.PbcDescentFunctors
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-! # Definitions of the rational PBC purity presentation

The original coherence obligation and presentation definitions, publicly re-exported
by RationalPurityPresentation. Their statements and data bodies are unchanged.
(blueprint: def-pur-rational-purity-presentation-data).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option linter.all false
set_option linter.unusedVariables false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures AlgebraicGeometry.Scheme
open scoped TensorProduct

attribute [local instance high] Algebra.toModule ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom
  AlgebraicGeometry.Scheme.pbcRationalScalarHom
  AlgebraicGeometry.Scheme.pbcPurityTwisted AlgebraicGeometry.Scheme.pbcPurityCompact
  AlgebraicGeometry.Scheme.pbcPurityTwistedAmbient
  AlgebraicGeometry.Scheme.pbcPurityCompactAmbient
  AlgebraicGeometry.Scheme.pbcPurityStageA AlgebraicGeometry.Scheme.pbcPurityStageC
  AlgebraicGeometry.Scheme.pbcPurityStageTwisted
  AlgebraicGeometry.Scheme.pbcPurityStageCompact
  AlgebraicGeometry.Scheme.pbcPurityScalarNormalization
  AlgebraicGeometry.Scheme.pbcPurityTwistedScalar
  AlgebraicGeometry.Scheme.pbcPurityCompactScalar
  AlgebraicGeometry.Scheme.pbcPurityTateModel
  AlgebraicGeometry.Scheme.pbcPurityDerivedScalarModel
  purCoefficientModel integralSheafTwist completedDerivedScalarExtension pbcTateAmbient
  purScalarModel integralTwistOrdinaryBeta pbcPurityTateScalarModel
  pbcPurityTateScalarComponent pbcActualCompletedPull

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- The actual pullback/tensor comparisons obey the tensor associator equation.
Source: original parent proof Step 4
(blueprint: def-pur-rational-purity-presentation-data).
Proof: on flat-term K-flat representatives the two composites multiply the same
two scalar factors and send the root line by the same twistScalarMaps. Tensor
associativity, root-line transitivity and canonical shift interchange identify
them. Universal counits descend that equality, then scalar localization preserves
it. Conjugation by the fixed unit normalizations gives the displayed equation. -/
theorem pbcPurityStageA_coherence {E F L : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (k : F ≤ L) (K : pbcStageCategory l Ω Y E) :
    ((pbcScalarSystem l Ω X dX.out iX.out).T k).map
        ((pbcPurityStageA l Ω f c d h).hom.app K) ≫
      (pbcPurityStageA l Ω f c d k).hom.app
        (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K) ≫
      (pbcPurityStageTwisted l Ω f c d L).map
        (((pbcScalarSystem l Ω Y dY.out iY.out).assoc h k).hom.app K) =
    ((pbcScalarSystem l Ω X dX.out iX.out).assoc h k).hom.app
        ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
      (pbcPurityStageA l Ω f c d (h.trans k)).hom.app K := by
  sorry


/-- The actual twisted inverse-image family with its specified comparison maps.
Source: proof Steps 3--5 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def pbcPurityTwistedSystem :
    StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out) where
  Φ := pbcPurityStageTwisted l Ω f c d
  β := pbcPurityStageA l Ω f c d
  coh := pbcPurityStageA_coherence l Ω f c d



/-- Exceptional inverse image is right adjoint to the actual proper/open compact
support. Its b comparison is the adjoint transpose of inverse c followed by the
old counit. The counit equation fixes every component uniquely, so a sign change
of b cannot satisfy this normalization.
Source: proof Step 3 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcPurityExceptionalSpec
    (G : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out)) : Prop :=
  ∃ adj : ∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcPurityStageCompact l Ω f c d E ⊣ G.Φ E,
    ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
      (K : pbcStageCategory l Ω Y E),
      (pbcPurityStageCompact l Ω f c d F).map ((G.β h).hom.app K) ≫
          (adj F).counit.app (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K) =
        (pbcPurityStageC l Ω f c d h).inv.app ((G.Φ E).obj K) ≫
          ((pbcScalarSystem l Ω Y dY.out iY.out).T h).map ((adj E).counit.app K)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- Step 4's pasted-square equation, retaining the actual tensor associators at both
ends. The middle expression is successive extension; the first and last use direct
extension. This is an equality of maps, not merely existence of compositors.
Source: proof Step 4 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcPurityTransitivity
    (G : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out))
    (γ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcPurityStageTwisted l Ω f c d E ≅ G.Φ E) : Prop :=
  ∀ {E F L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (k : F ≤ L)
    (K : pbcStageCategory l Ω Y E),
    (((pbcScalarSystem l Ω X dX.out iX.out).assoc h k).hom.app
          ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
        ((pbcScalarSystem l Ω X dX.out iX.out).T (h.trans k)).map ((γ E).hom.app K) ≫
        (G.β (h.trans k)).hom.app K =
      ((pbcScalarSystem l Ω X dX.out iX.out).T k).map
          (((pbcScalarSystem l Ω X dX.out iX.out).T h).map ((γ E).hom.app K)) ≫
        ((pbcScalarSystem l Ω X dX.out iX.out).T k).map ((G.β h).hom.app K) ≫
        (G.β k).hom.app (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K) ≫
        (G.Φ L).map (((pbcScalarSystem l Ω Y dY.out iY.out).assoc h k).hom.app K)) ∧
    (((pbcScalarSystem l Ω X dX.out iX.out).assoc h k).hom.app
          ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
        ((pbcScalarSystem l Ω X dX.out iX.out).T (h.trans k)).map ((γ E).hom.app K) ≫
        (G.β (h.trans k)).hom.app K =
      ((pbcScalarSystem l Ω X dX.out iX.out).assoc h k).hom.app
          ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
        (pbcPurityStageA l Ω f c d (h.trans k)).hom.app K ≫
        (γ L).hom.app (((pbcScalarSystem l Ω Y dY.out iY.out).T (h.trans k)).obj K))

/-- Descent on the actual PBC Qbar categories, including the common-stage naturality
square and both component formulas. Morphism classes and enlargement independence
are those of the recorded StageSystem descent functors themselves.
Source: proof Step 5 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcPurityDescent
    (G : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out))
    (γ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcPurityStageTwisted l Ω f c d E ≅ G.Φ E)
    (γQ : (pbcPurityTwistedSystem l Ω f c d).functor ≅ G.functor) : Prop :=
  StageSystem.Morphism.DescentSpec (pbcPurityTwistedSystem l Ω f c d) ∧
  StageSystem.Morphism.DescentSpec G ∧
  (∀ K : pbcQbarCategory l Ω Y,
    γQ.hom.app K = (Functor.whiskerRight (γ K.stage).hom
      ((pbcScalarSystem l Ω X dX.out iX.out).ι K.stage)).app K.obj ∧
    γQ.inv.app K = (Functor.whiskerRight (γ K.stage).inv
      ((pbcScalarSystem l Ω X dX.out iX.out).ι K.stage)).app K.obj) ∧
  ∀ {E F M : Padic.FiniteCoefficientFields l Ω} (hE : E ≤ M) (hF : F ≤ M)
    (K : pbcStageCategory l Ω Y E) (L : pbcStageCategory l Ω Y F)
    (u : ((pbcScalarSystem l Ω Y dY.out iY.out).T hE).obj K ⟶
      ((pbcScalarSystem l Ω Y dY.out iY.out).T hF).obj L),
    ((G.β hE).hom.app K ≫ (G.Φ M).map u ≫ (G.β hF).inv.app L) ≫
        ((pbcScalarSystem l Ω X dX.out iX.out).T hF).map ((γ F).inv.app L) =
      ((pbcScalarSystem l Ω X dX.out iX.out).T hE).map ((γ E).inv.app K) ≫
        ((pbcPurityStageA l Ω f c d hE).hom.app K ≫
          (pbcPurityStageTwisted l Ω f c d M).map u ≫
          (pbcPurityStageA l Ω f c d hF).inv.app L)

attribute [local irreducible] PbcPurityTransitivity PbcPurityDescent

/-- The complete coefficient-square, associator, descent and retract assertion.
All categories, scalar transitions and a comparisons are specified constructions.
The exceptional family is pinned to actual compact support by its adjunction and
counit-mate normalization. No arbitrary pair of functors can instantiate this.
Source: proof Steps 1--7 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcPurityCoefficientConclusion : Prop :=
  ∃ G : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out),
    PbcPurityExceptionalSpec l Ω f c d G ∧
    ∃ γ : ∀ E : Padic.FiniteCoefficientFields l Ω,
        pbcPurityStageTwisted l Ω f c d E ≅ G.Φ E,
      (∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
        (K : pbcStageCategory l Ω Y E),
        ((pbcScalarSystem l Ω X dX.out iX.out).T h).map ((γ E).hom.app K) ≫
            (G.β h).hom.app K =
          (pbcPurityStageA l Ω f c d h).hom.app K ≫
            (γ F).hom.app (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K)) ∧
      PbcPurityTransitivity l Ω f c d G γ ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : pbcStageCategory l Ω Y E) (e : K ⟶ K) (he : e ≫ e = e),
        IsIso (((Idempotents.functorExtension₂
          (pbcStageCategory l Ω Y E) (pbcStageCategory l Ω X E)).map (γ E).hom).app
            ⟨K, e, he⟩)) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω) {J K : pbcStageCategory l Ω Y E}
        (i : J ⟶ K) (r : K ⟶ J) (_hi : i ≫ r = 𝟙 J),
        (pbcPurityStageTwisted l Ω f c d E).map i ≫ (γ E).hom.app K ≫
            (G.Φ E).map r = (γ E).hom.app J ∧
        (G.Φ E).map i ≫ (γ E).inv.app K ≫
            (pbcPurityStageTwisted l Ω f c d E).map r = (γ E).inv.app J) ∧
      ∃ γQ : (pbcPurityTwistedSystem l Ω f c d).functor ≅ G.functor,
        PbcPurityDescent l Ω f c d G γ γQ ∧
        (∀ (K : pbcQbarCategory l Ω Y) (e : K ⟶ K) (he : e ≫ e = e),
          IsIso (((Idempotents.functorExtension₂
            (pbcQbarCategory l Ω Y) (pbcQbarCategory l Ω X)).map γQ.hom).app ⟨K, e, he⟩)) ∧
        ∀ {J K : pbcQbarCategory l Ω Y} (i : J ⟶ K) (r : K ⟶ J)
          (_hi : i ≫ r = 𝟙 J),
          (pbcPurityTwistedSystem l Ω f c d).functor.map i ≫ γQ.hom.app K ≫
              G.functor.map r = γQ.hom.app J ∧
          G.functor.map i ≫ γQ.inv.app K ≫
              (pbcPurityTwistedSystem l Ω f c d).functor.map r = γQ.inv.app J

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
    [Xsep : IsSeparated (X ↘ Spec (.of D.k))]
    [Ysep : IsSeparated (Y ↘ Spec (.of D.k))]
    [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
    [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
    [fsep : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
    (d : ℕ) [fsm : SmoothOfRelativeDimension d f]

/-- Supply the source-implied PBC category bounds without extra geometric assumptions.
Source: proof Step 1 (blueprint: prop-pur-rational-purity-transitivity-summands). -/
def PbcRationalPurityConclusion : Prop := by
  letI := (pbcPurityGeometricBounds l D hl X).1
  letI := (pbcPurityGeometricBounds l D hl Y).1
  letI : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞)) :=
    ⟨(pbcPurityGeometricBounds l D hl X).2.1⟩
  letI : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞)) :=
    ⟨(pbcPurityGeometricBounds l D hl Y).2.1⟩
  letI : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)) :=
    ⟨(pbcPurityGeometricBounds l D hl X).2.2⟩
  letI : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :=
    ⟨(pbcPurityGeometricBounds l D hl Y).2.2⟩
  exact ∀ c : Compactification f, PbcPurityCoefficientConclusion l Ω f c d


end AlgebraicGeometry.Scheme
