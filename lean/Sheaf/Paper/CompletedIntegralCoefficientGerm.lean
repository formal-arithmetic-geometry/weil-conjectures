/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Constant scalars in the completed coefficient stalk

Source: Weil blueprint, completed integral coefficients, order 1455;
Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients).
The constant-to-completed map is the limit lift of the actual quotient maps.
No isomorphism or arbitrary scalar action is chosen.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{u})

/-- The quotient map from constant integral coefficients to the n+1 finite level.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def integralConstantQuotientRingMap (n : ℕ) :
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)))) ⟶
      integralCoefficientSheaf l E Y n :=
  (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
          ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
            (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom))))

/-- Compatibility of the constant quotient maps with the coefficient tower.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients).
Proof: the transition is the factor map induced by inclusion of consecutive ideal
powers. Its composite with the quotient at exponent n+2 is the quotient at n+1,
as is checked on a representative in O_E. Apply constant sheafification and forget
commutativity; both preserve this composition identity. -/
theorem integralConstantQuotientRingMap_compatibility (n : ℕ) :
    integralConstantQuotientRingMap l E Y (n + 1) ≫
      integralCoefficientSheafTransition l E Y n = integralConstantQuotientRingMap l E Y n := by
  sorry

/-- The cone of constant integral scalars over all finite levels.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def integralConstantCoefficientCone : Cone (integralCoefficientSheafSystem l E Y) :=
  { pt := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))
    π := NatTrans.ofOpSequence (integralConstantQuotientRingMap l E Y)
      (fun n ↦ by
        change 𝟙 _ ≫ _ = _
        rw [Category.id_comp]
        simpa only [integralCoefficientSheafSystem,
          Functor.ofOpSequence_map_homOfLE_succ] using
            (integralConstantQuotientRingMap_compatibility l E Y n).symm) }


/-- The canonical constant-to-completed map, with all quotient projections prescribed.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def integralConstantToCompletion :
    (integralConstantCoefficientCone l E Y).pt ⟶
      completedIntegralCoefficientSheafUnrestricted l E Y :=
  limit.lift (integralCoefficientSheafSystem l E Y) (integralConstantCoefficientCone l E Y)

variable {Y} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- Send an integral scalar to its constant germ in the completed coefficient stalk.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def integralConstantStalkGerm (y : Spec (.of Ω) ⟶ Y) :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      proEtaleGeometricStalkRing y (completedIntegralCommRingSheafUnrestricted l E Y) :=
  (colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget y).op
    (integralConstantToCompletion l E Y).hom)).hom.comp
      (proEtaleConstantRingGerm y (Padic.coefficientExtensionIntegers l E))

/-- The integral module stalk, with its canonical O_E action; no completeness assertion
about the stalk is required for its construction.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def integralCoefficientModuleStalkFunctor (y : Spec (.of Ω) ⟶ Y) :=
  geometricRingModuleStalkFunctor y (completedIntegralCommRingSheafUnrestricted l E Y) ⋙
    ModuleCat.restrictScalars (integralConstantStalkGerm l E y)

/-- Additivity inherited from the module colimit and restriction of scalars.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable instance integralCoefficientModuleStalkFunctorAdditive
    (y : Spec (.of Ω) ⟶ Y) : (integralCoefficientModuleStalkFunctor l E y).Additive :=
  inferInstanceAs ((geometricRingModuleStalkFunctor y
    (completedIntegralCommRingSheafUnrestricted l E Y) ⋙
      ModuleCat.restrictScalars (integralConstantStalkGerm l E y)).Additive)

end WeilConjectures
