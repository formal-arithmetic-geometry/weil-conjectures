/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility
public import Sheaf.SixFunctors.CompletedShriekCompositionLaws
public import Sheaf.SixFunctors.AmbientProperOpenPasting
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
public import Sheaf.SixFunctors.GeneratorReductionStatement
import Sheaf.SixFunctors.SemilinearProperOpenMatePasting

/-! # Pasting of the prescribed normalized integral refinement maps

Source: blueprint exceptional inverse image, extracted normalized coefficient argument,
old step 10; Stacks Tags 0F7B, 0F7C and 0F7D
(blueprint: lem-sf-integral-normalized-refinement-pasting).

All comparisons below are arrows in the ordinary derived categories themselves.
Positive coefficient level n is the exponent n+1 in the imported system calculus.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

section Pasting
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (o : Operations l E) (R : Realizations l E D o)
  {X Y : Over (Spec (CommRingCat.of D.k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
  (F : ∀ _c : Compactification f.left,
    finiteTorConstructibleIntegralCategory l E X.left ⥤
      finiteTorConstructibleIntegralCategory l E Y.left)
  (r : ∀ c : Compactification f.left,
    F c ⋙ (finiteTorConstructibleIntegral l E Y.left).ι ≅
      (finiteTorConstructibleIntegral l E X.left).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E) c)
  (ρ : ∀ {c d : Compactification f.left}, c.Refinement d → (F c ≅ F d))
  (e : ∀ {_c d : Compactification f.left} (v : _c.Refinement d),
    (finiteTorConstructibleIntegral l E X.left).ι ⋙ ringedOpen l E d.i ≅
      (finiteTorConstructibleIntegral l E X.left).ι ⋙
        ringedOpen l E _c.i ⋙ ringedPush l E v.hom)

/-- Actual integral identity, composition, total-limit realization and outer-factor laws.
Source: blueprint exceptional inverse image, extracted normalized coefficient argument,
old step 10; Stacks 0F7B, 0F7C, 0F7D
(blueprint: lem-sf-integral-normalized-refinement-pasting).

Proof:
1. For a refinement u use the square (j_c,j_d,1_X,u). The intrinsic proper/open
mate transpose gives lambda P(g_u)=1. Semilinear mate pasting and ambient proper/open
pasting give g_vu=c_vu (S_v g_u) g_v and g_1=1 before evaluation.
2. The integral compactification system realization and generator reduction coherence
identify the realized g_u with the supplied e_u: both have the specified open-unit
transpose after the canonical restriction/clopen identification. Injectivity of the
open-adjunction Hom equivalence gives equality of actual arrows. Proper compositors
are identified by the same realization. All intermediate systems satisfy the assumed
normalized, witnessed common cohomology and Tor bounds.
3. The actual reconstruction counits on normalized systems are invertible by
lem-pur-normalized-actual-reconstruction-maps. Naturality expresses g_u as the
conjugate of reduction of its invertible realized map; hence g_u is invertible.
The forward system refinement is proper image of its inverse, after the inverse
proper compositor, precisely the inverse of completedShriekRefinement.
4. Invert step 1's equation. Naturality and associativity of the proper compositors
give t_v t_u=t_vu and t_1=1, with every intermediate compositor evaluated on J inputs.
5. The supplied normalization of rho gives I(rho_u)=a_d L(t_u) a_c inverse, where
a_c is c_Bc followed by r_c inverse. The recursive realization identifies the same
square after proper/open whiskering. Applying total limit to step 4 and cancelling
adjacent realization isomorphisms gives the asserted laws after inclusion. Its
faithfulness gives the actual integral identity and composition laws. Zero inputs
and empty opens give unique zero-object arrows; identity refinements use unitors.
No equality is detected by finite evaluation.
-/
theorem integralNormalizedRefinementPasting
    (_compatible : ∀ c : Compactification f.left,
      ∃ η : F c ⋙ PurCompactSupport.finiteTorIntegralInclusion l E Y.left ≅
          PurCompactSupport.finiteTorIntegralInclusion l E X.left ⋙
            sfCompactSupportFiniteIntegralFunctor l D.k
              (PurCompactSupport.coefficientPrimeUnit l D hl) c E,
        ∀ K : finiteTorConstructibleIntegralCategory l E X.left,
          (r c).hom.app K = (sfIntegralConstructible l E Y.left).ι.map (η.hom.app K) ≫
            (sfQcqsCompactSupportRealization l E D.k
              (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
                ((PurCompactSupport.finiteTorIntegralInclusion l E X.left).obj K))
    (_transpose : ∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left),
      (ringedOpenAdj l E d.i).homEquiv _ _ ((e v).hom.app K) ≫
          PurCompactSupport.refinementRestriction (PurCompactSupport.completed l E) v
            (PurCompactSupport.completedPull_comp l E c.i v.hom) K.obj =
        (ringedOpenAdj l E c.i).unit.app K.obj)
    (_normalization : ∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left),
      (finiteTorConstructibleIntegral l E Y.left).ι.map ((ρ v).hom.app K) ≫
          (r d).hom.app K =
        (r c).hom.app K ≫
          ((ringedPushComp l E v.hom d.g ≪≫
            eqToIso (congrArg (ringedPush l E) v.hom_g)).inv.app
              ((ringedOpen l E c.i).obj K.obj)) ≫
          (ringedPush l E d.g).map ((e v).inv.app K))
    (hDiagram : ∀ (c : Fin 3 → Compactification f.left)
      (v : (c 0).Refinement (c 1)) (w : (c 1).Refinement (c 2))
      (K : finiteTorConstructibleIntegralCategory l E X.left) (q : Fin 18),
      (refinementDiagramWords f c v w (fun i ↦ inferInstance) q).2.domain l E o
        (fun _ ↦ K.obj)) :
    (∀ c : Compactification f.left, ρ (.id c) = Iso.refl (F c)) ∧
    (∀ (c d b : Compactification f.left) (v : c.Refinement d) (w : d.Refinement b),
      ρ (v.comp w) = ρ v ≪≫ ρ w) ∧
    (∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left),
      IsIso ((completedShriekRefinement l E R v).app
        ((calculus l E X.left).reduction.obj K.obj)) ∧
      (finiteTorConstructibleIntegral l E Y.left).ι.map ((ρ v).hom.app K) ≫
          (r d).hom.app K =
        (r c).hom.app K ≫
          (R.comparison (normalizedRefinementWord f c)
            (normalizedRefinementGeometric f c)).inv.app
              ⟨(fun _ ↦ K.obj), hDiagram (fun _ ↦ c) (.id c) (.id c) K 15⟩ ≫
          (coefficientSequenceLimit l E Y.left).map
            (normalizedRefinementSystemMap l E R v
              ((calculus l E X.left).reduction.obj K.obj)) ≫
          (R.comparison (normalizedRefinementWord f d)
            (normalizedRefinementGeometric f d)).hom.app
              ⟨(fun _ ↦ K.obj), hDiagram (fun _ ↦ d) (.id d) (.id d) K 15⟩) ∧
    (∀ (c d : Compactification f.left) (v : c.Refinement d)
      (K : finiteTorConstructibleIntegralCategory l E X.left)
      {W : Over (Spec (CommRingCat.of D.k))}
      (q : NormalizedRefinementContext _ Y W)
      (gc : (q.plug (normalizedRefinementWord f c)).geometric)
      (gd : (q.plug (normalizedRefinementWord f d)).geometric)
      (hc : (q.plug (normalizedRefinementWord f c)).domain l E o (fun _ ↦ K.obj))
      (hd : (q.plug (normalizedRefinementWord f d)).domain l E o (fun _ ↦ K.obj)),
      (q.evaluate (integralInterpretation l E)).map
          ((r c).inv.app K ≫
            (finiteTorConstructibleIntegral l E Y.left).ι.map ((ρ v).hom.app K) ≫
            (r d).hom.app K) =
        (q.realization l E R (normalizedRefinementWord f c) gc (fun _ ↦ K.obj) hc).inv ≫
          (coefficientSequenceLimit l E W.left).map
            ((q.evaluate (systemInterpretation l E o)).map
              (normalizedRefinementSystemMap l E R v
                ((calculus l E X.left).reduction.obj K.obj))) ≫
          (q.realization l E R (normalizedRefinementWord f d) gd (fun _ ↦ K.obj) hd).hom) := by
  sorry

end Pasting
end WeilConjectures.IntegralSystemRealization
