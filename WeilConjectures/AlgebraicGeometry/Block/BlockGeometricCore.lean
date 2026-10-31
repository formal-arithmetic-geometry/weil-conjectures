/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.System.SystemBlockConstructions
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryDirectSystem

/-! # Reindexed ordinary geometric cores

Source: Zheng Construction 4.1 and the paragraph preceding Lemma 4.10.
This is the local construction before assembling the system adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (t : SystemBlockMap)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  (A : Data.{c, v, r} J B τ)
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)
  (RX : SystemBlockRepetition J' G.coefficients G.coefficientTransition t)
  (RY : SystemBlockRepetition J B τ t)

/-- Reassemble the repeated component functors, their local transition mate, and
canonical repetition squares. This does not assert a system Hom bijection,
a system adjunction, either global adjunction equation, or a derived comparison.

Source: Zheng Construction 4.1, printed p. 21, and the levelwise geometric
morphism paragraph before Lemma 4.10, printed p. 23; finite-block generalization.
(blueprint: lem-pur-block-geometric-core)

Proof: use the specified algebraic inverse image at index t(m). For a horizontal
map n ≤ m use G.restrictionPullback at t(n) ≤ t(m). The coefficient maps agree
with the repeated coefficient maps by functoriality of the original ring sequence.
Conjugating inverse image of the old transition by this restriction comparison
makes a semilinear map. Its underlying set-sheaf map is uInv of the original
transition, conjugated by the moduleUnderlying identifications; consequently
identity, composition, and naturality follow from the corresponding laws of uInv.
Reassemble on the sequence site, whose covers are vertical. Preserve finite
limits and colimits componentwise using the exact functors G.inverseImage.
For the direct core, use G.levelPush at t(m), and conjugate uPush of the
horizontal maps by G.levelPushUnderlying. The normalized module unit identifies
the transported scalar actions with those on G.levelPush. Applying the original
set-sheaf adjunction to a square of two component maps proves precisely the
local transition-mate equivalence of OrdinaryDirectSystemCore, in both directions.
This is a local two-component calculation, not an assertion of a global Hom
bijection. The constructions keep the component section carriers.
For the original direct image, transpose naturality of its system unit and use
ordinary_unit_evaluation. This identifies its horizontal transitions with the
same local mates. Faithful component evaluations detect these equalities.
For the original inverse image the corresponding identity is ordinaryPullTransition.
Thus on a repeated original system both constructions agree with the original
geometric constructions at t(m), on horizontal arrows as well as objects.
Their component identifications
therefore assemble into natural isomorphisms δ and s, identity on sections.
The two displayed evaluation equations are their definitions: evaluate at m,
then use the repeated-core and repetition component identifications. They are
compatible with every horizontal map by the construction above and with vertical
maps by naturality, hence are equations of the actual system functors. -/
theorem blockGeometricCore :
    ∃ (P : OrdinaryInverseSystem.{c, v, r}
      J (blockCoefficients B t) (blockTransitions J B τ t) J' uInv
      (blockCoefficients G.coefficients t)
      (blockTransitions J' G.coefficients G.coefficientTransition t)
      (fun m ↦ G.inverseImage (t.index m)))
      (K : OrdinaryDirectSystemCore.{c, v, r}
        J (blockCoefficients B t) (blockTransitions J B τ t) J' uInv
        (blockCoefficients G.coefficients t)
        (blockTransitions J' G.coefficients G.coefficientTransition t)
        (fun m ↦ G.inverseImage (t.index m)) P
        (fun m ↦ G.levelPush (t.index m)) (fun m ↦ G.levelAdjunction (t.index m)))
      (δ : G.pull ⋙ RX.repetition ≅ RY.repetition ⋙ P.pull)
      (s : RX.repetition ⋙ K.push ≅ G.push ⋙ RY.repetition),
      (∀ (M : Systems J B τ) (U : (ℕ × C')ᵒᵖ)
        (x : ((G.pull ⋙ RX.repetition).obj M).val.obj U),
        HEq (((δ.hom.app M).val.app U) x) x) ∧
      (∀ (N : Systems J' G.coefficients G.coefficientTransition) (U : (ℕ × C)ᵒᵖ)
        (x : ((RX.repetition ⋙ K.push).obj N).val.obj U),
        HEq (((s.hom.app N).val.app U) x) x) ∧
      (∀ (M : Systems J B τ) (m : ℕ),
        (evaluation J' (blockCoefficients G.coefficients t)
            (blockTransitions J' G.coefficients G.coefficientTransition t) m).map
              (δ.hom.app M) ≫
          (P.component m).hom.app (RY.repetition.obj M) ≫
          (G.inverseImage (t.index m)).modules.map ((RY.evaluation m).hom.app M) =
        (RX.evaluation m).hom.app (G.pull.obj M) ≫
          (G.ordinaryPullEvaluation (t.index m)).hom.app M) ∧
      (∀ (N : Systems J' G.coefficients G.coefficientTransition) (m : ℕ),
        (evaluation J (blockCoefficients B t) (blockTransitions J B τ t) m).map
            (s.hom.app N) ≫
          (RY.evaluation m).hom.app (G.push.obj N) ≫
          (G.ordinaryPushEvaluation (t.index m)).hom.app N =
        (K.component m).hom.app (RX.repetition.obj N) ≫
          (G.levelPush (t.index m)).map ((RX.evaluation m).hom.app N)) := by sorry

end WeilConjectures.SemilinearSections
