/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.NormalizedScalar.FieldModel.NormalizedCoefficientExact
public import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedScalarActions
public import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedScalarLocalization
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleShift
import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedSemilinearDerived
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Shift.Linear
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # The scalar functor on ordinary bounded constructible complexes

Derived extension of scalars from the integral coefficient ring `O_E` to the field coefficient
ring `E` on the pro-étale site restricts to a triangulated functor between bounded
constructible complexes, sends each integral scalar `a` to the field scalar `a`, and hence
induces a forward functor on the Verdier rationalization at powers of `l`.

## Main results

* `boundedExtension`: the restricted derived extension of scalars.
* `boundedExtension_scalar`: compatibility with scalars.
* `bounded_forward_exists`: the forward functor on the rationalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.NormalizedScalar
variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- The integral coefficient ring on the pro-étale site of `T`, pulled back from the condensed
ring of continuous functions to the unit ball `O_E`. -/
abbrev integralRing := condensedRingObj
  (Profinite.continuousCoefficientRingObj (integers l E)) T

/-- The field coefficient ring on the pro-étale site of `T`, pulled back from the condensed
ring of continuous functions to `E`. -/
abbrev fieldRing (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] (T : Scheme.{u}) :=
  condensedRingObj (Profinite.continuousCoefficientRingObj E) T

/-- The coefficient map `integralRing → fieldRing` induced by the inclusion `O_E → E`. -/
abbrev inclusion := coefficientMap (scalarMap (l := l) (E := E)) T

/-- Extension of scalars along `inclusion` preserves finite limits. -/
instance inclusion_exact : PreservesFiniteLimits (Mod.extendScalars (inclusion l E T)) :=
  scalar_exact T

/-- The exactness proposition packaged at the canonical module universes. -/
def ScalarExactData : Prop :=
  PreservesFiniteLimits (Mod.extendScalars (inclusion l E T))

theorem scalar_exact_data : ScalarExactData l E T := by
  exact inclusion_exact l E T

/-- Bounded constructible complexes of `integralRing`-modules. -/
abbrev Integral := BoundedConstructible (integralRing l E T)

/-- Bounded constructible complexes of `fieldRing`-modules. -/
abbrev Rational := BoundedConstructible (fieldRing l E T)

/-- The total left derived extension of scalars along `inclusion`, restricted to bounded
constructible complexes. -/
def boundedExtension : Integral l E T ⥤ Rational l E T :=
  (boundedConstructible (fieldRing l E T)).lift
    ((boundedConstructible (integralRing l E T)).ι ⋙
      (Mod.extendScalars (inclusion l E T)).leftDerivedFunctor)
    (fun K ↦ boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K.obj K.property)

/-- `boundedExtension` followed by the inclusion agrees with the ambient derived extension of
scalars. -/
def boundedExtensionCompatibility :
    boundedExtension l E T ⋙ (boundedConstructible (fieldRing l E T)).ι ≅
      (boundedConstructible (integralRing l E T)).ι ⋙
        (Mod.extendScalars (inclusion l E T)).leftDerivedFunctor :=
  ObjectProperty.liftCompιIso _ _ _

attribute [local instance] modulesLinear

/-- Extension of scalars sends multiplication by `a ∈ O_E` to multiplication by `a ∈ E`. -/
theorem extension_scalar (a : integers l E)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (integralRing l E T)) :
    (Mod.extendScalars (inclusion l E T)).map (a • 𝟙 M) =
      (a : E) • 𝟙 ((Mod.extendScalars (inclusion l E T)).obj M) := by
  let : Linear (integers l E)
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (fieldRing l E T)) :=
    Mod.linearOfRingHom ((constants E T).comp (integers l E).subtype)
  have : (Mod.comap (inclusion l E T)).Linear (integers l E) := comap_linear T
  have : (Mod.extendScalars (inclusion l E T)).Linear (integers l E) :=
    (Mod.extendRestrictAdjunction (inclusion l E T)).left_adjoint_linear
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

attribute [local instance] CategoryTheory.ObjectProperty.linear_shiftFunctor_fullSubcategory

variable [ObjectProperty.IsTriangulated (boundedConstructible (integralRing l E T))]
  [ObjectProperty.IsTriangulated (boundedConstructible (fieldRing l E T))]

instance integralPretriangulated : Pretriangulated (Integral l E T) := by
  change Pretriangulated (boundedConstructible (integralRing l E T)).FullSubcategory
  exact CategoryTheory.ObjectProperty.instPretriangulatedFullSubcategory _
instance rationalPretriangulated : Pretriangulated (Rational l E T) := by
  change Pretriangulated (boundedConstructible (fieldRing l E T)).FullSubcategory
  exact CategoryTheory.ObjectProperty.instPretriangulatedFullSubcategory _

instance integralCategoryTriangulated : IsTriangulated (Integral l E T) := by
  change IsTriangulated (boundedConstructible (integralRing l E T)).FullSubcategory
  infer_instance
instance rationalCategoryTriangulated : IsTriangulated (Rational l E T) := by
  change IsTriangulated (boundedConstructible (fieldRing l E T)).FullSubcategory
  infer_instance

/-- Linearity of the inherited integral shifts. -/
instance integralShiftLinear (n : ℤ) :
    (shiftFunctor (Integral l E T) n).Linear (integers l E) := by
  change (shiftFunctor (boundedConstructible (integralRing l E T)).FullSubcategory n).Linear
    (integers l E)
  exact CategoryTheory.ObjectProperty.linear_shiftFunctor_fullSubcategory _ n

/-- The derived extension of scalars commutes with integer shifts. -/
@[instance_reducible] instance derivedExtensionShift :
    (Mod.extendScalars (inclusion l E T)).leftDerivedFunctor.CommShift ℤ :=
  CategoryTheory.Functor.CommShift.ofIso
    (Mod.extendScalars (inclusion l E T)).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ

/-- The derived extension of scalars is triangulated. -/
instance derivedExtensionTriangulated :
    (Mod.extendScalars (inclusion l E T)).leftDerivedFunctor.IsTriangulated := by
  have := CategoryTheory.Functor.CommShift.ofIso_compatibility
    (Mod.extendScalars (inclusion l E T)).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ
  exact CategoryTheory.Functor.isTriangulated_of_iso
    (Mod.extendScalars (inclusion l E T)).leftDerivedFunctorIsoMapDerivedCategory.symm

/-- `boundedExtension` commutes with integer shifts. -/
instance boundedExtensionShift : (boundedExtension l E T).CommShift ℤ := by
  unfold boundedExtension
  infer_instance

/-- `boundedExtension` is triangulated. -/
instance boundedExtensionTriangulated : (boundedExtension l E T).IsTriangulated := by
  unfold boundedExtension
  infer_instance

/-- Transport a scalar-identity equation without unfolding the concrete functors. -/
private lemma map_scalar_identity_of_iso
    {S : Type*} [Semiring S] {C D : Type*} [Category* C] [Category* D]
    [Preadditive D] [Linear S D] {F G : C ⥤ D} (e : F ≅ G)
    {X : C} (f : X ⟶ X) (s : S) (h : G.map f = s • 𝟙 (G.obj X)) :
    F.map f = s • 𝟙 (F.obj X) := by
  apply (cancel_mono (e.hom.app X)).1
  rw [e.hom.naturality, h]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Category.comp_id]

/-- `boundedExtension` sends multiplication by `a ∈ O_E` to multiplication by `a ∈ E`. -/
theorem boundedExtension_scalar (a : integers l E) (K : Integral l E T) :
    (boundedExtension l E T).map (a • 𝟙 K) =
      (a : E) • 𝟙 ((boundedExtension l E T).obj K) := by
  let F := Mod.extendScalars (inclusion l E T)
  have h := mapDerivedCategory_scalar (integers l E).subtype F
    (fun r M ↦ extension_scalar l E T r M) a K.obj
  have he : F.leftDerivedFunctor.map (a • 𝟙 K.obj) =
      (a : E) • 𝟙 (F.leftDerivedFunctor.obj K.obj) :=
    map_scalar_identity_of_iso F.leftDerivedFunctorIsoMapDerivedCategory
      (a • 𝟙 K.obj) (a : E) h
  apply ObjectProperty.hom_ext (P := boundedConstructible (fieldRing l E T))
  change F.leftDerivedFunctor.map (a • 𝟙 K.obj) =
    (a : E) • 𝟙 (F.leftDerivedFunctor.obj K.obj)
  exact he

/-- `boundedExtension` admits a linear triangulated forward lift to the Verdier
rationalization at powers of `l`, with a shift-compatible comparison. -/
def ForwardData : Prop :=
  ForwardFunctorData (Submonoid.powers (l : integers l E)) E (boundedExtension l E T)

/-- `boundedExtension` induces a forward functor on the Verdier rationalization at powers of
`l`, with a shift-compatible comparison and the fraction equation. -/
theorem bounded_forward_exists : ForwardData l E T := by
  let H := boundedExtension l E T
  have hH : ∀ (r : integers l E) (X : Integral l E T),
      H.map (r • 𝟙 X) = (r : E) • 𝟙 (H.obj X) :=
    fun r X ↦ boundedExtension_scalar l E T r X
  let h := forward_exists
    (Submonoid.powers (l : integers l E)) E H hH
  exact h

end WeilConjectures.NormalizedScalar
