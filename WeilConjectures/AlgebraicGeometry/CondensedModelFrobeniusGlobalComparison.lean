/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase

/-! Strict subgoal of the global condensed model Frobenius comparison. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The model/global comparison, the second strict subgoal of the global theorem.
Source: latest blueprint, `lem-fd-realness-pushforward.proof.md`, Step 1;
original operator comparison proof steps 4--9.
(blueprint: lem-fd-condensed-model-frobenius-global-comparison).

Proof: choose the dense compactification and transpose the proper model comparison
under pullback/direct-image adjunction. Compare the open mates using the normalized
open unit, identify the proper/open interchange by its restriction and triangle
identity, then combine with the semilinear compact exchange. Transport along the
published compactification-identification isomorphism. This proves equality of
actual derived module morphisms before evaluation or traces. -/
theorem condensed_model_frobenius_global_comparison
    [IsSeparated X₀.hom] (ell : ℕ) [Fact ell.Prime] [Fact (ell ≠ D₀.p)]
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj ell)
      (StrictWeil.modelFrobenius D₀ X₀)) (c₀ : Compactification X₀.hom)
    (w : Factorization D₀ X₀)
    (hB : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ell) (D₀.geometricFiber X₀).left)
      K.carrier.obj)
    (hf : ∀ m : ℕ, IsFinite (frobeniusIterate (modelEnd D₀ X₀) m).left)
    (hu : ∀ m : ℕ, IsUniversalHomeomorphism (frobeniusIterate (modelEnd D₀ X₀) m).left)
    (wj : ∀ m : ℕ,
      ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m) ≫
          (geometricCompactification D₀ X₀ c₀).i =
        (geometricCompactification D₀ X₀ c₀).i ≫
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m))
    (wp : ∀ m : ℕ,
      ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m) ≫
          (geometricCompactification D₀ X₀ c₀).g =
        (geometricCompactification D₀ X₀ c₀).g ≫
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m)) :
(∀ m : ℕ, 1 ≤ m →
        (compactIdentification ell (geometricCompactification D₀ X₀ c₀)
          ⟨K.carrier.obj, hB⟩).inv ≫
          modelGlobal ell (frobeniusIterate (modelEnd D₀ X₀) m) (hf m) (hu m)
            (modelObject ell (frobeniusIterate (modelEnd D₀ X₀) m) ⟨K.carrier.obj, hB⟩
              (modelStructure D₀ X₀ ell K w m)) ≫
          (compactIdentification ell (geometricCompactification D₀ X₀ c₀)
            ⟨K.carrier.obj, hB⟩).hom =
        compactReturn (Profinite.padicAlgClRingObj ell)
          (geometricCompactification D₀ X₀ c₀).i (geometricCompactification D₀ X₀ c₀).g
          ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m)
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m)
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) (wj m) (wp m)
          (iterateStructure (Profinite.padicAlgClRingObj ell)
            (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) m).hom) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
