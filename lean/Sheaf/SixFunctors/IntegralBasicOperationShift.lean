/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.SixFunctors.GeneratorReductionStatement
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.SixFunctors.BasicRealizationShiftSquare
import Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus

/-!
# Shift squares for the specified single-operation integral comparisons

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-compatibility/fix-prop-coherence.proof.md,
maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift).

The tensor constructors distinguish the selected slot. Their other operand is an
integral input and its actual reduction is the other system operand. The comparison
is exactly GeneratorReduction.pullD, identity for the defining proper tower,
GeneratorReduction.openD, or GeneratorReduction.tensorD.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A basic operation with one selected input slot; the two tensor slots are distinct.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
inductive BasicShiftOperation (B : Scheme.{u}) : Over B → Over B → Type (u + 3) where
  | pull {U V : Over B} (f : U ⟶ V) (hs : IsSeparated f.left)
      (ht : LocallyOfFiniteType f.left) (hq : QuasiCompact f.left) : BasicShiftOperation B V U
  | push {U V : Over B} (f : U ⟶ V) (hp : IsProper f.left) : BasicShiftOperation B U V
  | open {U V : Over B} (j : U ⟶ V) (hj : IsOpenImmersion j.left)
      (hq : QuasiCompact j.left) : BasicShiftOperation B U V
  | tensorLeft (W : Over B) (N : Integral l E W.left) : BasicShiftOperation B W W
  | tensorRight (W : Over B) (M : Integral l E W.left) : BasicShiftOperation B W W

variable {B : Scheme.{u}} {U V : Over B}

/-- The actual strict-system operation in the selected slot.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.system (o : GeneratorReduction.Operations l E) :
    BasicShiftOperation l E B U V → (System l E U.left ⥤ System l E V.left)
  | .pull f _ _ _ => IntegralSystemRealization.pull l E f.left
  | .push f _ => Operations.push l E o.system f.left
  | .open j hj _ => letI := hj; Operations.shriek l E o.system j.left
  | .tensorLeft W N =>
      (Functor.curry.obj (calculus l E W.left).systemClosed.tensor).flip.obj
        ((calculus l E W.left).reduction.obj N)
  | .tensorRight W M =>
      (Functor.curry.obj (calculus l E W.left).systemClosed.tensor).obj
        ((calculus l E W.left).reduction.obj M)

/-- The corresponding completed integral operation, with the generator's proper tower.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.integral (o : GeneratorReduction.Operations l E) :
    BasicShiftOperation l E B U V → (Integral l E U.left ⥤ Integral l E V.left)
  | .pull f _ _ _ => integralDerivedPullback l E f.left
  | .push f _ => GeneratorReduction.integralPush l E o f.left
  | .open j hj _ => letI := hj; ringedOpen l E j.left
  | .tensorLeft W N => (Functor.curry.obj (integralCompletedTensor l E W.left)).flip.obj N
  | .tensorRight W M => (Functor.curry.obj (integralCompletedTensor l E W.left)).obj M

/-- The source L A R of the specified single-operation comparison.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.source (o : GeneratorReduction.Operations l E)
    (A : BasicShiftOperation l E B U V) :=
  (calculus l E U.left).reduction ⋙ A.system l E o ⋙ coefficientSequenceLimit l E V.left

/-- The fixed termwise, adjunction-mate, or signed tensor system shift.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.systemShift (o : GeneratorReduction.Operations l E) :
    (A : BasicShiftOperation l E B U V) → (r : ℤ) → (M : System l E U.left) →
      (A.system l E o).obj (M⟦r⟧) ≅ ((A.system l E o).obj M)⟦r⟧
  | .pull f _ _ _, r, M =>
      (Functor.commShiftIso _ (self := systemPullShift l E f.left) r).app M
  | .push f _, r, M =>
      (Functor.commShiftIso _ (self := systemPushShift l E o.system f.left) r).app M
  | .open j hj _, r, M => letI := hj
      (Functor.commShiftIso _ (self := systemOpenShift l E o.system j.left) r).app M
  | .tensorLeft W N, r, M =>
      ((tensorShifts l E).systemLeft W.left r).app
        (M, (calculus l E W.left).reduction.obj N)
  | .tensorRight W M, r, N =>
      ((tensorShifts l E).systemRight W.left r).app
        ((calculus l E W.left).reduction.obj M, N)

/-- Proper image uses the composite shift of its defining L S R tower.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
@[instance_reducible]
def basicIntegralPushShift (o : GeneratorReduction.Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (GeneratorReduction.integralPush l E o f).CommShift ℤ := by
  letI := reductionShift l E X
  letI := systemPushShift l E o.system f
  letI := limitShift l E Y
  change ((calculus l E X).reduction ⋙ Operations.push l E o.system f ⋙
    coefficientSequenceLimit l E Y).CommShift ℤ
  infer_instance

/-- The fixed integral comparison, with coefficient 1 on left tensor summands and
(-1)^(ri) on right tensor summands, followed by the specified Roos cone shift.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.integralShift (o : GeneratorReduction.Operations l E) :
    (A : BasicShiftOperation l E B U V) → (r : ℤ) → (K : Integral l E U.left) →
      (A.integral l E o).obj (K⟦r⟧) ≅ ((A.integral l E o).obj K)⟦r⟧
  | .pull f _ _ _, r, K =>
      (Functor.commShiftIso _ (self := (integralShifts l E).pull f.left) r).app K
  | .push f _, r, K =>
      (Functor.commShiftIso _ (self := basicIntegralPushShift l E o f.left) r).app K
  | .open j hj _, r, K => letI := hj
      (Functor.commShiftIso _ (self := (integralShifts l E).shriek j.left) r).app K
  | .tensorLeft W N, r, K => ((tensorShifts l E).integralLeft W.left r).app (K, N)
  | .tensorRight W M, r, K => ((tensorShifts l E).integralRight W.left r).app (M, K)

/-- The source shift uses reduction, the selected operation slot, then actual total limit.
The latter is the product/cone comparison of limitShift_roos, not a chosen endpoint iso.
For proper image this is evaluated as the canonical composite CommShift component,
using the same three constituent shifts as basicIntegralPushShift. This avoids
normalizing the derived-limit model when comparing its two presentations.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.sourceShift (o : GeneratorReduction.Operations l E) :
    (A : BasicShiftOperation l E B U V) → (r : ℤ) → (K : Integral l E U.left) →
    (A.source l E o).obj (K⟦r⟧) ≅ ((A.source l E o).obj K)⟦r⟧
  | .push f _, r, K =>
      (Functor.commShiftIso _ (self := basicIntegralPushShift l E o f.left) r).app K
  | A, r, K =>
      (coefficientSequenceLimit l E V.left).mapIso
        ((A.system l E o).mapIso
          ((Functor.commShiftIso _ (self := reductionShift l E U.left) r).app K) ≪≫
          A.systemShift l E o r ((calculus l E U.left).reduction.obj K)) ≪≫
        (Functor.commShiftIso _ (self := limitShift l E V.left) r).app
          ((A.system l E o).obj ((calculus l E U.left).reduction.obj K))

/-- Exactly d_A from the recorded generator statement. The open map is L(r_j inverse)
followed by the inverse reconstruction unit; the proper map is identity on its tower.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.comparison (o : GeneratorReduction.Operations l E) :
    (A : BasicShiftOperation l E B U V) → (K : Integral l E U.left) →
      (A.source l E o).obj K ⟶ (A.integral l E o).obj K
  | .pull f _ _ _, K => (GeneratorReduction.pullD l E f.left).hom.app K
  | .push _ _, _ => 𝟙 _
  | .open j hj _, K => letI := hj; GeneratorReduction.openD l E o j.left K
  | .tensorLeft W N, K => (GeneratorReduction.tensorD l E W.left).hom.app (K, N)
  | .tensorRight W M, K => (GeneratorReduction.tensorD l E W.left).hom.app (M, K)

/-- Common bounds on all inputs and intermediate systems. The other tensor input
has its own completeness, compatible origin, constructibility and finite-Tor witnesses.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftOperation.admissible (o : GeneratorReduction.Operations l E)
    (A : BasicShiftOperation l E B U V) (K : Integral l E U.left)
    (lo hi torLo torHi : ℤ) : Prop :=
  GeneratorReduction.Admissible l E (calculus l E U.left) K lo hi torLo torHi ∧
  GeneratorReduction.SystemAdmissible l E V.left
    ((A.system l E o).obj ((calculus l E U.left).reduction.obj K)) lo hi torLo torHi ∧
  match A with
  | .tensorLeft W N | .tensorRight W N =>
      GeneratorReduction.Admissible l E (calculus l E W.left) N lo hi torLo torHi
  | .pull _ _ _ _ | .push _ _ | .open _ _ _ => True

/-- Express naturality, zero-shift normalization, and addition coherence using Mathlib's
existing CommShift structure, with every component pinned to the specified comparisons.
Source: maps-used sentence (blueprint: lem-pur-integral-basic-operation-shift). -/
def BasicShiftCoherent {C : Type v} [Category.{w} C] [HasShift C ℤ]
    {D : Type v'} [Category.{w'} D] [HasShift D ℤ] (F : C ⥤ D)
    (σ : ∀ (r : ℤ) (X : C), F.obj (X⟦r⟧) ≅ (F.obj X)⟦r⟧) : Prop :=
  ∃ s : F.CommShift ℤ, ∀ (r : ℤ) (X : C),
    (Functor.commShiftIso F (self := s) r).app X = σ r X

attribute [local irreducible] limitShift reductionShift systemPushShift
  coefficientSequenceLimit BasicShiftCoherent

private theorem coherentTriple
    {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
    [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₃ ℤ] [HasShift C₄ ℤ]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₃ ⥤ C₄)
    (sF : F.CommShift ℤ) (sG : G.CommShift ℤ) (sH : H.CommShift ℤ)
    (σ : ∀ (r : ℤ) (X : C₂), G.obj (X⟦r⟧) ≅ (G.obj X)⟦r⟧)
    (hσ : ∀ (r : ℤ) (X : C₂), (Functor.commShiftIso G (self := sG) r).app X = σ r X) :
    BasicShiftCoherent (F ⋙ G ⋙ H) (fun r X ↦
      H.mapIso (G.mapIso ((Functor.commShiftIso F (self := sF) r).app X) ≪≫
        σ r (F.obj X)) ≪≫
      (Functor.commShiftIso H (self := sH) r).app (G.obj (F.obj X))) := by
  unfold BasicShiftCoherent
  let := sF
  let := sG
  let := sH
  refine ⟨inferInstance, ?_⟩
  intro r X
  apply Iso.ext
  simp only [Iso.app_hom, Functor.commShiftIso_comp_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Functor.comp_map, Category.assoc]
  rw [show (Functor.commShiftIso G r).hom.app (F.obj X) = (σ r (F.obj X)).hom from
    congrArg Iso.hom (hσ r (F.obj X))]

private theorem basicSourceCoherent (o : GeneratorReduction.Operations l E)
    (A : BasicShiftOperation l E B U V)
    (h : BasicShiftCoherent (A.system l E o) (A.systemShift l E o)) :
    BasicShiftCoherent (A.source l E o) (A.sourceShift l E o) := by
  cases A with
  | push f hp =>
    unfold BasicShiftCoherent
    exact ⟨basicIntegralPushShift l E o f.left, fun _ _ ↦ rfl⟩
  | pull f hs ht hq | «open» f hs ht | tensorLeft _ f | tensorRight _ f =>
    unfold BasicShiftCoherent at h
    obtain ⟨s, hs⟩ := h
    exact coherentTriple (calculus l E _).reduction _
      (coefficientSequenceLimit l E _) (reductionShift l E _) s
      (limitShift l E _) _ hs

/-- Shift compatibility for each specified single-operation reduction-tower realization.
Source: main-20261015, fix-prop-coherence.proof.md, maps-used sentence
(blueprint: lem-pur-integral-basic-operation-shift).

Proof:
1. For unary operations take the prescribed CommShift structures. For each tensor
slot apply basicSystemShiftResolutionCalculus to its fixed other operand.
2. Compose reduction, the selected system shift, and total limit. Mathlib's
composite component formula, functoriality, and associativity identify its component
with sourceShift. Proper image uses this composite directly.
3. Apply the pull, open, and tensor fields of basicRealizationShiftSquare to the
admissibility projections. Proper image has identity comparison on its defining tower.
4. Apply the naturality fields of the same square structure; for tensor use the
identity map in the fixed slot. Proper-image naturality is the identity law. -/
theorem integralBasicOperationShift (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : GeneratorReduction.Operations l E)
    {U V : Over (Spec (.of D.k))}
    (_hUt : LocallyOfFiniteType U.hom) (_hUq : QuasiCompact U.hom)
    (_hVt : LocallyOfFiniteType V.hom) (_hVq : QuasiCompact V.hom)
    (A : BasicShiftOperation l E _ U V) :
    BasicShiftCoherent (A.system l E o) (A.systemShift l E o) ∧
    BasicShiftCoherent (A.integral l E o) (A.integralShift l E o) ∧
    BasicShiftCoherent (A.source l E o) (A.sourceShift l E o) ∧
    (∀ (K : Integral l E U.left) (lo hi torLo torHi : ℤ),
      A.admissible l E o K lo hi torLo torHi → ∀ r : ℤ,
        A.comparison l E o (K⟦r⟧) ≫ (A.integralShift l E o r K).hom =
          (A.sourceShift l E o r K).hom ≫ (A.comparison l E o K)⟦r⟧') ∧
    (∀ (K L : Integral l E U.left) (f : K ⟶ L) (lo hi torLo torHi : ℤ),
      A.admissible l E o K lo hi torLo torHi →
      A.admissible l E o L lo hi torLo torHi →
      (A.source l E o).map f ≫ A.comparison l E o L =
        A.comparison l E o K ≫ (A.integral l E o).map f) := by
  let := _hUt
  let := _hUq
  let := _hVt
  let := _hVq
  have models := basicSystemShiftResolutionCalculus l E D _hl o.system
  have hsystem : BasicShiftCoherent (A.system l E o) (A.systemShift l E o) := by
    unfold BasicShiftCoherent
    cases A with
    | pull f hs ht hq => exact ⟨systemPullShift l E f.left, fun _ _ ↦ rfl⟩
    | push f hp => exact ⟨systemPushShift l E o.system f.left, fun _ _ ↦ rfl⟩
    | «open» j hj hq =>
      let := hj
      exact ⟨systemOpenShift l E o.system j.left, fun _ _ ↦ rfl⟩
    | tensorLeft _ N =>
      obtain ⟨s₁, s₂, h₁, h₂⟩ := models.system_tensor_laws U
      exact ⟨s₁ ((calculus l E U.left).reduction.obj N),
        fun r M ↦ h₁ M ((calculus l E U.left).reduction.obj N) r⟩
    | tensorRight _ M =>
      obtain ⟨s₁, s₂, h₁, h₂⟩ := models.system_tensor_laws U
      exact ⟨s₂ ((calculus l E U.left).reduction.obj M),
        fun r N ↦ h₂ ((calculus l E U.left).reduction.obj M) N r⟩
  have hintegral : BasicShiftCoherent (A.integral l E o) (A.integralShift l E o) := by
    unfold BasicShiftCoherent
    cases A with
    | pull f hs ht hq => exact ⟨(integralShifts l E).pull f.left, fun _ _ ↦ rfl⟩
    | push f hp => exact ⟨basicIntegralPushShift l E o f.left, fun _ _ ↦ rfl⟩
    | «open» j hj hq =>
      let := hj
      exact ⟨(integralShifts l E).shriek j.left, fun _ _ ↦ rfl⟩
    | tensorLeft _ N =>
      obtain ⟨s₁, s₂, h₁, h₂⟩ := models.integral_tensor_laws U
      exact ⟨s₁ N, fun r M ↦ h₁ M N r⟩
    | tensorRight _ M =>
      obtain ⟨s₁, s₂, h₁, h₂⟩ := models.integral_tensor_laws U
      exact ⟨s₂ M, fun r N ↦ h₂ M N r⟩
  obtain ⟨sq⟩ := (basicRealizationShiftSquare l E D _hl o).2.2.2.2.2
  refine ⟨hsystem, hintegral, basicSourceCoherent l E o A hsystem, ?_, ?_⟩
  · cases A with
    | pull f hs ht hq =>
      let := hs
      let := ht
      let := hq
      intro K lo hi torLo torHi h r
      exact sq.pull f K lo hi torLo torHi h.1 h.2.1 r
    | push f hp =>
      intro K lo hi torLo torHi h r
      change 𝟙 _ ≫ (BasicShiftOperation.sourceShift l E o (.push f hp) r K).hom =
        (BasicShiftOperation.sourceShift l E o (.push f hp) r K).hom ≫
          (shiftFunctor (Integral l E V.left) r).map (𝟙 _)
      rw [Category.id_comp, (shiftFunctor (Integral l E V.left) r).map_id,
        Category.comp_id]
    | «open» j hj hq =>
      let := hj
      let := hq
      intro K lo hi torLo torHi h r
      exact sq.shriek j K lo hi torLo torHi h.1 h.2.1 r
    | tensorLeft _ N =>
      intro K lo hi torLo torHi h r
      exact (sq.tensor U K N lo hi torLo torHi h.1 h.2.2 h.2.1 r).1
    | tensorRight _ M =>
      intro K lo hi torLo torHi h r
      exact (sq.tensor U M K lo hi torLo torHi h.2.2 h.1 h.2.1 r).2
  · cases A with
    | pull f hs ht hq =>
      intro K L f' lo hi torLo torHi hK hL
      exact sq.pull_natural f K L f'
    | push f hp =>
      intro K L f' lo hi torLo torHi hK hL
      simp only [BasicShiftOperation.comparison, BasicShiftOperation.integral,
        BasicShiftOperation.source, GeneratorReduction.integralPush,
        integralSystemDerivedDirectImage, BasicShiftOperation.system,
        Functor.comp_map, Category.comp_id, Category.id_comp]
    | «open» j hj hq =>
      let := hj
      let := hq
      intro K L f' lo hi torLo torHi hK hL
      exact sq.open_natural j K L f' lo hi torLo torHi hK.1 hL.1
    | tensorLeft _ N =>
      intro K L f lo hi torLo torHi hK hL
      change (coefficientSequenceLimit l E U.left).map
        ((calculus l E U.left).systemClosed.tensor.map
          (Prod.mkHom ((calculus l E U.left).reduction.map f) (𝟙 _))) ≫
        (GeneratorReduction.tensorD l E U.left).hom.app (L, N) =
        (GeneratorReduction.tensorD l E U.left).hom.app (K, N) ≫
          (integralCompletedTensor l E U.left).map (Prod.mkHom f (𝟙 N))
      have h := sq.tensor_natural U K L N N f (𝟙 N)
      rw [(calculus l E U.left).reduction.map_id] at h
      exact h
    | tensorRight _ M =>
      intro K L f lo hi torLo torHi hK hL
      change (coefficientSequenceLimit l E U.left).map
        ((calculus l E U.left).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((calculus l E U.left).reduction.map f))) ≫
        (GeneratorReduction.tensorD l E U.left).hom.app (M, L) =
        (GeneratorReduction.tensorD l E U.left).hom.app (M, K) ≫
          (integralCompletedTensor l E U.left).map (Prod.mkHom (𝟙 M) f)
      have h := sq.tensor_natural U M M K L (𝟙 M) f
      rw [(calculus l E U.left).reduction.map_id] at h
      exact h

end WeilConjectures.IntegralSystemRealization
