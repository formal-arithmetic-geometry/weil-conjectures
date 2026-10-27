/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U6
-/
module

public import Sheaf.Paper.EtaleSystemCofinalData
import Sheaf.Paper.EtaleSystemProjectionExistence
import Sheaf.Paper.EtaleCofinalRepeatSupportExistence
import Sheaf.Paper.EtaleCofinalFactorEvaluation

/-! # Repetition and scalar factorization of a selected extension

Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- Evaluation diagrams for block repetition and scalar factorization. These specify
coherence before inverting a coefficient projection or forming a support comparison.
Source: Zheng 4.1, paragraph before 4.10
(blueprint: lem-pur-etale-cofinal-block-factorization). -/
structure CofinalBlockEvaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (T : Theory c l) (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
    (Lx : CofinalExtension X B r) (Ly : CofinalExtension Y B r)
    (R : CofinalRepeatSupport T B r)
    (Fx : CofinalFactor X B r Lx R.x (T.scalarX (cofinalCoefficient B r)))
    (Fy : CofinalFactor Y B r Ly R.y (T.scalarY (cofinalCoefficient B r))) where
  x : ∀ m : ℕ,
    R.x.R.mapDerivedCategory ⋙ (T.evaluationX (cofinalRepeated B r) m).E ≅
      (T.evaluationX (cofinalCoefficients B r) (SheafOfModules.systemNextSelected r m)).E
  y : ∀ m : ℕ,
    R.y.R.mapDerivedCategory ⋙ (T.evaluationY (cofinalRepeated B r) m).E ≅
      (T.evaluationY (cofinalCoefficients B r) (SheafOfModules.systemNextSelected r m)).E
  factorX : ∀ (m : ℕ) (N : Derived X (cofinalCoefficients B r).rings),
    (T.evaluationX B m).E.map (Fx.derived.hom.app N) ≫
      (T.scalarEvaluationX (cofinalCoefficient B r) m).iso.hom.app
        (R.x.R.mapDerivedCategory.obj N) ≫
      (scalarExtension ((cofinalCoefficient B r).app (op m)).hom X).map
        ((x m).hom.app N) =
      (Lx.level m (T.evaluationX B m)
        (T.evaluationX (cofinalCoefficients B r)
          (SheafOfModules.systemNextSelected r m))).hom.app N
  factorY : ∀ (m : ℕ) (N : Derived Y (cofinalCoefficients B r).rings),
    (T.evaluationY B m).E.map (Fy.derived.hom.app N) ≫
      (T.scalarEvaluationY (cofinalCoefficient B r) m).iso.hom.app
        (R.y.R.mapDerivedCategory.obj N) ≫
      (scalarExtension ((cofinalCoefficient B r).app (op m)).hom Y).map
        ((y m).hom.app N) =
      (Ly.level m (T.evaluationY B m)
        (T.evaluationY (cofinalCoefficients B r)
          (SheafOfModules.systemNextSelected r m))).hom.app N
  support : ∀ (m : ℕ) (N : Derived X (cofinalCoefficients B r).rings),
    (T.evaluationY (cofinalRepeated B r) m).E.map (R.kappa.hom.app N) ≫
      (y m).hom.app ((T.support (cofinalCoefficients B r)).F.obj N) ≫
      (T.supportEvaluation (cofinalCoefficients B r)
        (SheafOfModules.systemNextSelected r m)).iso.hom.app N =
    (T.supportEvaluation (cofinalRepeated B r) m).iso.hom.app
        (R.x.R.mapDerivedCategory.obj N) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} ((cofinalRepeated B r).rings.obj (op m))) c).map
          ((x m).hom.app N)

/-- Repetition supplies the geometric square and factors the two local selected extensions.
The presentation is chosen together with its repetition evaluation diagrams, before any
selected-extension/support comparison is formed.
Source: Zheng, Construction 4.1 and paragraph preceding Lemma 4.10, printed pp. 21--23
(blueprint: lem-pur-etale-cofinal-block-factorization).

Proof: construct the ordinary geometric projection theory using the actual sequence-site
pushforward and a simultaneous sectionwise extension by zero for all coefficient towers.
Choose its evaluation and restriction comparisons by the canonical adjunction mates,
as in etaleSystemProjectionTheory_nonempty. This fixes T jointly with its block data;
one does not assert literal identity-on-sections comparisons for arbitrary open adjoints.
For any local normalized selected extensions, t(m), the least i with m ≤ r(i), is
monotone and onto since t(r(i))=i.
Its fibers are nonempty finite intervals, bounded above by r(i). Apply systemBlockRepetition
on the three small étale sites, with these blocks. Its actual repetition functors have
exactly the sections, maps and restrictions required in CofinalRepeat. Apply the geometric
block square to proper direct image and the section-normalized open-extension square to
extension by zero. The exact endpoint left adjoint makes repetition on the compactification
preserve K-injective complexes. This constructs CofinalRepeatSupport without using a right
adjoint of compact support. The repeated tower is D_m=B_(r(t(m))), with its actual quotient
map cofinalCoefficient B r to B. Repetition followed by ordinary coefficient extension has
at m the same tensor and transitions as the selected ordinary extension. Both are left
adjoints of actual cofinal restriction, with units x↦1⊗x at selected sections. Ordinary
adjoint uniqueness with that unit gives ordinary and ordinary_unit in each CofinalFactor.
On simultaneous flat-term K-flat representatives the two functors compute the same strict
complex, including its transitions and maps. The universal normalized left derived
comparison gives derived and its displayed normalization. Acyclic K-flat cones extend the
normalization to all complexes via the universal counit. Apply this construction on X and
Y. Evaluate repetition to obtain x and y. The ordinary tensor-unit equality, localized
with the normalized universal cochain comparison, gives factorX and factorY. On ordinary
open complexes the repetition square is identity on sections; on K-injective proper
representatives its derived square is the identical complex at t(m). Universal derived
uniqueness gives support, the repetition/support evaluation diagram, on all derived
objects. No selected-extension/support comparison or its evaluation is asserted. -/
theorem etaleCofinalBlockFactorization
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) :
    ∃ T : Theory c l,
      ∀ (B : Coefficients.{u} l) (r : ℕ ↪o ℕ)
        (Lx : CofinalExtension X B r) (Ly : CofinalExtension Y B r),
        ∃ (R : CofinalRepeatSupport T B r)
          (Fx : CofinalFactor X B r Lx R.x (T.scalarX (cofinalCoefficient B r)))
          (Fy : CofinalFactor Y B r Ly R.y (T.scalarY (cofinalCoefficient B r))),
          Nonempty (CofinalBlockEvaluation T B r Lx Ly R Fx Fy) := by
  obtain ⟨T⟩ := etaleSystemProjectionTheory_nonempty c l
  refine ⟨T, ?_⟩
  intro B r Lx Ly
  obtain ⟨R⟩ := etaleCofinalRepeatSupport_nonempty T B r
  obtain ⟨Fx, Fy, x, y, hfactorX, hfactorY, hsupport⟩ :=
    etaleCofinalFactorEvaluation_nonempty T B r Lx Ly R
  exact ⟨R, Fx, Fy, ⟨x, y, hfactorX, hfactorY, hsupport⟩⟩

end AlgebraicGeometry.Etale.SystemProjection
