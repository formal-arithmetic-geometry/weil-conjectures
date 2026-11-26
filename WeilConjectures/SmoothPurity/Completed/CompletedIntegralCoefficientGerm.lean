/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Field.ULift

/-!
# Constant scalars in the completed coefficient stalk

The map from the constant sheaf `O_E` to the completed integral coefficient sheaf, defined as
the limit lift of the quotient maps `O_E → O_E / 𝔪^(n+1)`, and the resulting constant germs and
scalar actions on sections over a geometric point.

## Implementation details

No isomorphism or arbitrary scalar action is chosen: the scalar actions on final-object
sections are restrictions of scalars along the actual constant-section maps.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Section 6.5
* [Stacks Project, Tag 03CW](https://stacks.math.columbia.edu/tag/03CW)
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

/-- The quotient map from the constant sheaf `O_E` to the finite coefficient sheaf
`O_E / 𝔪^(n+1)`. -/
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

/-- The constant quotient maps are compatible with the transition maps of the coefficient
tower. -/
theorem integralConstantQuotientRingMap_compatibility (n : ℕ) :
    integralConstantQuotientRingMap l E Y (n + 1) ≫
      integralCoefficientSheafTransition l E Y n = integralConstantQuotientRingMap l E Y n := by
  unfold integralConstantQuotientRingMap integralCoefficientSheafTransition
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 2

/-- The cone of constant integral scalars over all finite levels. -/
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

/-- The canonical constant-to-completed map, the limit lift of the constant quotient maps. -/
noncomputable def integralConstantToCompletion :
    (integralConstantCoefficientCone l E Y).pt ⟶
      completedIntegralCoefficientSheafUnrestricted l E Y :=
  limit.lift (integralCoefficientSheafSystem l E Y) (integralConstantCoefficientCone l E Y)

variable {Y} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- Send an integral scalar to its constant germ in the completed coefficient stalk. -/
noncomputable def integralConstantStalkGerm (y : Spec (.of Ω) ⟶ Y) :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      proEtaleGeometricStalkRing y (completedIntegralCommRingSheafUnrestricted l E Y) :=
  (colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget y).op
    (integralConstantToCompletion l E Y).hom)).hom.comp
      (proEtaleConstantRingGerm y (Padic.coefficientExtensionIntegers l E))

end WeilConjectures

/-! Canonical scalar actions on final-object sections. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- The constant-section coefficient map at the final object, given by the unit of
sheafification. -/
noncomputable def pointConstantSectionMap (k A : Type u) [Field k] [CommRing A] :
    ULift.{u + 1, u} A →+*
      (((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).obj.obj
            (op (ProEt.mk (𝟙 (Spec (.of k)))))) :=
  ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((CategoryTheory.toSheafify (ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op (ProEt.mk (𝟙 (Spec (.of k))))))).hom

/-- Final-object evaluation with scalars restricted along the constant-section map. -/
noncomputable def pointFiniteSections (k A : Type u) [Field k] [CommRing A] :=
  pointModuleSections k
      ((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A))) ⋙
    ModuleCat.restrictScalars (R := ULift.{u + 1, u} A) (pointConstantSectionMap k A)

/-- Final-object evaluation with restricted scalars is additive. -/
noncomputable instance pointFiniteSectionsAdditive (k A : Type u) [Field k] [CommRing A] :
    (pointFiniteSections k A).Additive :=
  inferInstanceAs ((pointModuleSections k _ ⋙
    ModuleCat.restrictScalars (R := ULift.{u + 1, u} A) (pointConstantSectionMap k A)).Additive)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]

/-- The canonical map `O_E → Γ(s, Ô_E)` to the completed coefficient sections over the final
object, the limit lift of the constant reductions. -/
noncomputable def pointIntegralSectionMap :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      (((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k)))).obj.obj
          (op (ProEt.mk (𝟙 (Spec (.of k)))))) :=
  (((integralConstantToCompletion l E (Spec (.of k))).hom.app
    (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom).comp
      (pointConstantSectionMap k (Padic.coefficientExtensionIntegers l E))

/-- Completed-coefficient sections over the final object, as `O_E`-modules via the canonical
integral coefficient action. -/
noncomputable def pointIntegralSections :=
  pointModuleSections k (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) ⋙
    ModuleCat.restrictScalars (pointIntegralSectionMap l E k)

/-- Completed-coefficient sections with restricted scalars form an additive functor. -/
noncomputable instance pointIntegralSectionsAdditive :
    (pointIntegralSections l E k).Additive :=
  inferInstanceAs ((pointModuleSections k _ ⋙
    ModuleCat.restrictScalars (pointIntegralSectionMap l E k)).Additive)

/-- The inclusion `O_E ↪ E`, transported through `ULift`. -/
noncomputable def pointIntegralToField :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+* ULift.{u + 1, u} E :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Padic.coefficientExtensionIntegers l E).subtype.comp ULift.ringEquiv.toRingHom)

/-- Extension of scalars along `O_E ↪ E` is additive. -/
noncomputable instance pointIntegralToFieldAdditive :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).left_adjoint_additive

end WeilConjectures
