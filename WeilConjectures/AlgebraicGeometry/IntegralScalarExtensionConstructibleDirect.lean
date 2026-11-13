/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.TraceFormula.PointFiberFunctorIntegral

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-!
# Direct integral scalar extension
-/

/-- The direct derived extension of scalars `T(K) = S ⊗^L_R K` along the coefficient change
`a_Y: p_Y^* 𝒪̲_E → p_Y^* 𝒪̲_L` induced by the inclusion `𝒪_E ⊆ 𝒪_L`: the left derived functor
of `Mod.extendScalars`, as in `det-def-sfb-derived-extension-of-scalars`. -/
noncomputable abbrev integralScalarExtension
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (Y : Scheme.{u}) :
    DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)) ⥤
      DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Y)) :=
  (Mod.extendScalars
    (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) Y)).leftDerivedFunctor

/-- Direct derived extension of scalars along `𝒪_E → 𝒪_L` sends `D_cons(Y_proét, R)` into
`D_cons(Y_proét, S)`; no derived completeness condition is involved.

Proof: `cartesianCoefficients_finiteFree`,
which assembles the integral basis and the finite-free
coordinates of `Res_{a_Y} S`, gives at `Y` that `Ext_{a_Y}` preserves finite limits. Then
`boundedConstructible_leftDerivedExtendScalars_obj` with `X = Y` and `φ = a_Y` applies:
its constructibility is exactly `boundedConstructible` and
its derived functor is `T`; no Noetherian hypothesis.
The statement includes empty schemes, zero complexes, identity extensions, shifts, torsion
cohomology, and ramified finite extensions, and imposes no derived completeness condition.
-/
theorem integralScalarExtension_constructible
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (Y : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y) K) :
    boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Y)
      ((integralScalarExtension ℓ h Y).obj K) := by
  let hflat := (cartesianCoefficients_finiteFree ℓ h).2.2 Y |>.1
  let : PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) Y)) := hflat
  exact boundedConstructible_leftDerivedExtendScalars_obj _ _ _ K hK

/-- Restriction of the direct derived tensor to the bounded constructible full
subcategories. Its object map is well-defined by
`integralScalarExtension_constructible`, and its morphism map is the ambient
full-subcategory map.
-/
noncomputable def integralScalarExtensionFunctor
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (Y : Scheme.{u}) :
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)).FullSubcategory ⥤
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) Y)).FullSubcategory :=
  ObjectProperty.lift _
    ((boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) Y)).ι ⋙
      integralScalarExtension ℓ h Y)
    (fun K ↦ integralScalarExtension_constructible ℓ h Y K.obj K.property)


end AlgebraicGeometry.ProEtale
