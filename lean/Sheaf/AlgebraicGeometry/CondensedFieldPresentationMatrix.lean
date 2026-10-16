/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrices of continuous functions for condensed field presentations

Source: Hemo--Richarz--Scholbach, Example 3.1; the rank/descent argument of
(blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
-/

@[expose] public section


universe u

open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The continuous-function matrix of a finite free morphism and a coefficient realization.
Source: Hemo--Richarz--Scholbach, Example 3.1, and the presentation-matrix step of
(blueprint: def-weil-pbc-condensed-field-presentation-matrix).
Each entry is the image of the unit under the corresponding regular-module endomorphism,
conjugated by the supplied ring-object isomorphism. -/
noncomputable def continuousFieldPresentationMatrix
    (E : Type u) [NormedField E] (V : Scheme.{u})
    {R : Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}} [MonObj R]
    (e : R ⟶ (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E)) [IsIso e]
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    Matrix (Fin n) (Fin m) C(V, E) := fun i j ↦
  let a := biproduct.ι (fun _ : Fin m ↦ Mod.regular R) j ≫ f ≫
    biproduct.π (fun _ : Fin n ↦ Mod.regular R) i
  (((inv e ≫ a.hom ≫ e).hom.app
    (op (Scheme.ProEt.mk (𝟙 V)))) (ULift.up 1)).down

/-- The realization of coefficients pulled back along an arbitrary scheme map.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-field-presentation-matrix).
Compose the monoidal coefficient pullback comparison with the canonical realization. -/
noncomputable def condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) ⟶
    (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E) :=
  condensedPullbackHom (Profinite.continuousCoefficientRingObj E) g ≫
    (condensedFieldContinuousMapIso E V).hom.hom

instance isIso_condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) : IsIso (condensedFieldPullbackRealization E g) := by
  unfold condensedFieldPullbackRealization
  infer_instance

instance isMonHom_condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) : IsMonHom (condensedFieldPullbackRealization E g) := by
  unfold condensedFieldPullbackRealization
  infer_instance

end AlgebraicGeometry.ProEtale
