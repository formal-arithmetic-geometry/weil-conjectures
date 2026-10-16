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

/-- The explicit composite uniquely determines the pullback realization.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-field-presentation-matrix).
Proof: the displayed composite is a witness, and the defining equality proves uniqueness. -/
theorem existsUnique_condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) :
    ∃! α : (upperStar AddCommGrpCat.{u + 1} g).obj
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) ⟶
    (sheafCompose (Scheme.ProEt.topology V)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf V E),
      α = condensedPullbackHom (Profinite.continuousCoefficientRingObj E) g ≫
        (condensedFieldContinuousMapIso E V).hom.hom := by
  exact ⟨_, rfl, fun _ h ↦ h⟩

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
  (existsUnique_condensedFieldPullbackRealization E g).exists.choose

/-- The pullback realization equals its explicit defining composite.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: def-weil-pbc-condensed-field-presentation-matrix).
Proof: the chosen morphism satisfies its uniquely determining equality. This equation
allows controlled rewriting without reducing the inverse-image construction at evaluation. -/
theorem condensedFieldPullbackRealization_eq
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) :
    condensedFieldPullbackRealization E g =
      condensedPullbackHom (Profinite.continuousCoefficientRingObj E) g ≫
        (condensedFieldContinuousMapIso E V).hom.hom :=
  (existsUnique_condensedFieldPullbackRealization E g).exists.choose_spec

instance isIso_condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) : IsIso (condensedFieldPullbackRealization E g) := by
  rw [condensedFieldPullbackRealization_eq]
  infer_instance

instance isMonHom_condensedFieldPullbackRealization
    (E : Type u) [NormedField E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (g : V ⟶ X) : IsMonHom (condensedFieldPullbackRealization E g) := by
  rw [condensedFieldPullbackRealization_eq]
  infer_instance

end AlgebraicGeometry.ProEtale
