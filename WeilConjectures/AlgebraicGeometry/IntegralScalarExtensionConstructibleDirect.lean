/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CartesianCoefficientsFiniteFree
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
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

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/sk-prop-scalar-six-ctf.md, preservation clause
(blueprint: lem-weil-integral-scalar-extension-constructible).
-/

/-- The direct derived extension of scalars `T(K) = S ⊗^L_R K` along the coefficient change
`a_Y : p_Y^* 𝒪̲_E → p_Y^* 𝒪̲_L` induced by the inclusion `𝒪_E ⊆ 𝒪_L`: the left derived functor
of `Mod.extendScalars`, as in `det-def-sfb-derived-extension-of-scalars`.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
sk-prop-scalar-six-ctf.md, preservation for listed coefficient maps, the functor `T`
(blueprint: lem-weil-integral-scalar-extension-constructible). -/
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
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
sk-prop-scalar-six-ctf.md, det-sfb-coefficient-comparisons-ctf: preservation for listed
coefficient maps, specialized to the finite integral extension in sk-prop-scalar-six (2)
(blueprint: lem-weil-integral-scalar-extension-constructible).

Proof: `cartesianCoefficients_finiteFree` (`det-prop-sfb-cartesian-coefficients-finite-free`),
which assembles the integral basis (`lem-sfb-local-field-integral-basis`) and the finite-free
coordinates of `Res_{a_Y} S`, gives at `Y` that `Ext_{a_Y}` preserves finite limits. Then
`boundedConstructible_leftDerivedExtendScalars_obj`
(`lem-weil-pbc-bounded-constructible-exact-scalar-extension`) with `X = Y` and `φ = a_Y` applies:
its constructibility is exactly `boundedConstructible` (`det-def-sfb-bounded-constructible`) and
its derived functor is `T` (`det-def-sfb-derived-extension-of-scalars`); no Noetherian hypothesis.
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
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
sk-prop-scalar-six-ctf.md, restriction of `T` to the preserved full subcategories
(blueprint: lem-weil-integral-scalar-extension-constructible).
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


/-- The restricted functor is linear for `O_E`. The source action is induced by the
constant-section map `O_E → Γ(R)`. The target action is induced by the composite
`O_E → O_L → Γ(S)`, so it is exactly the coefficient action required by the
statement.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-qlbar-two-colimit/
det-def-sf-operations.md, clause (i), direct derived tensor restricted to the preserved full
subcategories (blueprint: lem-weil-integral-scalar-extension-constructible).

Proof (node step 3): the coefficient point map sends the constant section `r` to the constant
section of its image in `O_L` (sectionwise postcomposition on continuous functions), and
naturality of global sections under `upperStarFromPoint Y` gives `Γ(a_Y) ∘ φE = φF`. Hence
restriction `Mod.comap a_Y` is `O_E`-linear (`Mod.linear_comap`), so is its left adjoint
`Mod.extendScalars a_Y` (`sk-def-sfb-change-of-scalars`); the exact functor induces an
`O_E`-linear functor on derived categories, transported to `T` by
`leftDerivedFunctorIsoMapDerivedCategory` (`det-def-sfb-derived-extension-of-scalars`). The
full-subcategory maps on Hom groups are the ambient ones, so `T(c f) = c T(f)` there.
-/
theorem integralScalarExtensionFunctor_linear
    (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (Y : Scheme.{u}) :
    let φE := (MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp
      (CondensedRing.padicIntegersConstRingHom ℓ E)
    let φF := (MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp
      ((CondensedRing.padicIntegersConstRingHom ℓ F).comp
        (finiteCoefficientIntegersMap ℓ h))
    letI := CategoryTheory.Mod.linearOfRingHom φE
    letI := CategoryTheory.Mod.linearOfRingHom φF
    (integralScalarExtensionFunctor ℓ h Y).Linear (PadicAlgCl.integers ℓ E.1) := by
  dsimp only
  let φE := (MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp
    (CondensedRing.padicIntegersConstRingHom ℓ E)
  let φF := (MonObj.Γ.mapFunctor (upperStarFromPoint Y)).comp
    ((CondensedRing.padicIntegersConstRingHom ℓ F).comp
      (finiteCoefficientIntegersMap ℓ h))
  let := Mod.linearOfRingHom φE
  let := Mod.linearOfRingHom φF
  let a := coefficientMap (finiteCoefficientIntegersPointMap ℓ h) Y
  have hc (r : PadicAlgCl.integers ℓ E.1) : Γ.map a (φE r) = φF r := by
    have hp : Γ.map (finiteCoefficientIntegersPointMap ℓ h)
        (CondensedRing.padicIntegersConstRingHom ℓ E r) =
        CondensedRing.padicIntegersConstRingHom ℓ F (finiteCoefficientIntegersMap ℓ h r) := by
      exact Sheaf.Γ_map_ringHomΓSheafCompose _
        (Profinite.continuousMapRingSheafMap (finiteCoefficientIntegersMap ℓ h)
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _))
        (Profinite.continuousMapConstSectionRingHom _) (fun _ _ ↦ rfl)
        (Profinite.continuousMapConstSectionRingHom _) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    change Γ.map ((upperStarFromPoint Y).map (finiteCoefficientIntegersPointMap ℓ h))
        (Γ.mapFunctor (upperStarFromPoint Y)
          (CondensedRing.padicIntegersConstRingHom ℓ E r)) = _
    rw [Γ.map_map_mapFunctor, hp]
    rfl
  have : (Mod.comap a).Linear (PadicAlgCl.integers ℓ E.1) :=
    Mod.linear_comap a φE φF hc
  have : (Mod.extendScalars a).Linear (PadicAlgCl.integers ℓ E.1) :=
    (Mod.extendRestrictAdjunction a).left_adjoint_linear
  have : PreservesFiniteLimits (Mod.extendScalars a) :=
    ((cartesianCoefficients_finiteFree ℓ h).2.2 Y).1
  have : (Mod.extendScalars a).mapDerivedCategory.Linear (PadicAlgCl.integers ℓ E.1) :=
    inferInstance
  have : (integralScalarExtension ℓ h Y).Linear (PadicAlgCl.integers ℓ E.1) :=
    Functor.linear_of_iso _ (Mod.extendScalars a).leftDerivedFunctorIsoMapDerivedCategory.symm
  constructor
  intro K L f r
  apply ObjectProperty.hom_ext
  exact (integralScalarExtension ℓ h Y).map_smul r f.hom

end AlgebraicGeometry.ProEtale
