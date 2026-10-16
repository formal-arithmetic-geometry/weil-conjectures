/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
import Sheaf.Paper.ContinuousIntegralCoefficients

/-! # Projection normalization of integral residue comparisons

Source: Bhatt--Scholze, Lemma 6.5.9(3), and Remark 6.8.15.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Coherent pull comparisons identify the restricted push mate with the projection map.

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15, and associativity of derived tensor.
(blueprint: new-integral-residue-projection-normalization)

Proof. The inverse image on sheaves preserves the coequalizers of balanced tensor pairs.
Its strong monoidal comparison therefore induces the relative tensor comparison on
module objects, and the coefficient-pullback isomorphism identifies their base rings.
The unit and associativity diagrams follow after precomposing with the epimorphisms
from the balanced tensor presentations. Pullback preserves flat modules and colimits;
apply the functorial flat resolutions to obtain resolutions with K-flat pullback.
The derived tensor comparison of these resolutions is invertible, and its unit and
associativity diagrams follow by uniqueness of derived comparisons. This gives m.

Resolve the input of scalar extension by K-flat modules. Associativity of relative tensor
and the coefficient-pullback isomorphism give the pull comparison. The associativity
pentagon and the coefficient-map composition equations give its composition law with
leftDerivedUpperStarComp, so the comparisons form c. The supplied tensor universal property
identifies reduction after restriction with tensor by the residue regular module, and
symmetry puts this coefficient in the right tensor factor. This gives s. Derived scalar
extension is left adjoint to exact scalar restriction. Thus the two composite functors
in c.pull are left adjoints, and conjugating c.pull gives an isomorphism of their right
adjoints, Rf_* followed by restriction and restriction followed by Rf_*. Evaluate it at
reduction of K. Combine it with the tensor identification on X and the coefficient
pullback isomorphism f^* A_Y ≅ A_X to obtain e on X. The target identification is the
composite of c.restrictPushIso at reduction of K with Rf_* applied to e. To identify the
morphism, transpose under the integral pull-push adjunction. The counit identity for
c.push, tensor associativity, and the coefficient-pullback isomorphism reduce both
sides to the oplax tensor comparison followed by the counit tensored with the identity.
This is the defining transpose of rightAdjointProjectionMap. No dualizability or
invertibility of the projection map is used. Empty schemes and zero complexes are
included: all comparisons remain the canonical ones. -/
theorem integralResidue_projection_normalization
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ c : IntegralResiduePullComparisons.{u} ℓ E,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        ∃ m : (residueExchangeUpperStar (integralCoeff ℓ E) f).Monoidal,
          letI := m
          ∀ K : residueExchangeDerived (integralCoeff ℓ E) X,
            ∃ (s :
                (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory.obj
                    ((residueExchangeReduction ℓ E Y).obj
                      ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K)) ≅
                  (residueExchangeLowerStar (integralCoeff ℓ E) f).obj K ⊗
                    residueExchangeCoefficient ℓ E Y)
              (e :
                (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategory.obj
                    ((residueExchangeReduction ℓ E X).obj K) ≅
                  K ⊗ (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
                    (residueExchangeCoefficient ℓ E Y)),
              (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory.map
                  ((c.push f).app K) ≫
                (c.restrictPushIso f).hom.app ((residueExchangeReduction ℓ E X).obj K) ≫
                (residueExchangeLowerStar (integralCoeff ℓ E) f).map e.hom =
                s.hom ≫
                  (((residueExchangeAdjunction (integralCoeff ℓ E) f).rightAdjointProjectionMap
                    (Functor.OplaxMonoidal.δNatTrans
                      (residueExchangeUpperStar (integralCoeff ℓ E) f))).app K).app
                    (residueExchangeCoefficient ℓ E Y) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
