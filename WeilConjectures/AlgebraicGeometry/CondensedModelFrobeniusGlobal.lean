/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusOperatorsBase
import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusGlobalPower
import WeilConjectures.AlgebraicGeometry.CondensedModelFrobeniusGlobalComparison

/-! Canonical condensed model Frobenius comparison, a step of the operator theorem. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D₀.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The semilinear compact-support returns obey the power law and equal the model operator.
Source: latest blueprint, lem-fd-realness-pushforward.proof.md, Step 1;
original operator comparison proof steps 4--11.
(blueprint: lem-fd-condensed-model-frobenius-global).

Proof: the profinite-site point equivalence identifies the point reparametrization with
the inverse of the point component of kappa; check this on every profinite test set, where
relative Frobenius fixes that set's coordinate. In the base-changed compactification,
transpose the proper model comparison under pullback/direct-image adjunction. Naturality
of kappa makes the two transposes equal, hence R p_*(kappa) rho = E_g r inverse. Under the
open extension/restriction adjunction the two transposes of its comparison are both the
pullback of the open unit followed by kappa. This gives b_g kappa = j_!(kappa) b_model.
The mate of b_model restricts to identity on the open. The normalized proper/open pasting
identity identifies this mate with the actual lower-shriek compositor. The triangle
identity then expresses the model compact-support comparison as R p_*(b_model) rho.
Combine these three equations and compose the image of theta^[m]; conjugating by the
published compactification-independence isomorphism gives the second equality.
For the first equality, expand the proper exchange as unit/comparison/counit. Pasting
cancels the middle counit/unit. The analogous open calculation cancels its middle
unit/counit after transposition. Thus the compact exchange satisfies the additive
cocycle. Point reparametrization has the same cocycle, and naturality moves the iterated
theta through it. Therefore F_(r+m) = F_r F_m. Induction starting at degree one gives
F_m = F_1^m. This works for any supplied compactification; the common-refinement
comparison retains the specified normalized compositor, without replacing the
non-Cartesian model square by Cartesian exchange. -/
theorem condensed_model_frobenius_global
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
        compactReturn (Profinite.padicAlgClRingObj ell)
          (geometricCompactification D₀ X₀ c₀).i (geometricCompactification D₀ X₀ c₀).g
          ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ m)
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ m)
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ m) (wj m) (wp m)
          (iterateStructure (Profinite.padicAlgClRingObj ell)
            (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) m).hom =
        (compactReturn (Profinite.padicAlgClRingObj ell)
          (geometricCompactification D₀ X₀ c₀).i (geometricCompactification D₀ X₀ c₀).g
          ((End.of (StrictWeil.modelFrobenius D₀ X₀).hom) ^ 1)
          ((End.of (StrictWeil.modelFrobenius D₀ (Over.mk c₀.g)).hom) ^ 1)
          ((End.of (StrictWeil.pointFrobenius D₀).hom) ^ 1) (wj 1) (wp 1)
          (iterateStructure (Profinite.padicAlgClRingObj ell)
            (End.of (StrictWeil.modelFrobenius D₀ X₀).hom) (ambientStructure _ K) 1).hom) ^ m) ∧
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
  refine ⟨?_, ?_⟩
  · exact condensed_model_frobenius_global_power D₀ X₀ ell K c₀ w hB hf hu wj wp
  · exact condensed_model_frobenius_global_comparison D₀ X₀ ell K c₀ w hB hf hu wj wp

end AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison
