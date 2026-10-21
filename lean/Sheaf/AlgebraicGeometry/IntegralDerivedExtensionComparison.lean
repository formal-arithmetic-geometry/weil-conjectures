/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Sheaf.Paper.ContinuousIntegralScalarExact

/-! # Integral scalar extension and its termwise triangulated comparison

Source: Bhatt--Scholze, Section 6.8, Proposition 6.8.14(2), preparatory comparison
(blueprint: lem-sfb-integral-derived-extension-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- Cache of the existing continuous coefficient structure, with exactly its original data.
Source: the coefficient-ring morphism and monoidal inverse image of Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison). -/
instance integralExtensionIntegralMonoid [TopologicalSpace.NoetherianSpace X] :
    MonObj (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) := inferInstance

/-- Cache of the existing continuous coefficient structure, with exactly its original data.
Source: the coefficient-ring morphism and monoidal inverse image of Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison). -/
instance integralExtensionIntegralCommutative [TopologicalSpace.NoetherianSpace X] :
    IsCommMonObj (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) := inferInstance

/-- Cache of the existing continuous coefficient structure, with exactly its original data.
Source: the coefficient-ring morphism and monoidal inverse image of Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison). -/
instance integralExtensionFieldMonoid [TopologicalSpace.NoetherianSpace X] :
    MonObj (condensedRingObj (Profinite.continuousMapRingObj E.1) X) := inferInstance

/-- Cache of the existing continuous coefficient structure, with exactly its original data.
Source: the coefficient-ring morphism and monoidal inverse image of Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison). -/
instance integralExtensionFieldCommutative [TopologicalSpace.NoetherianSpace X] :
    IsCommMonObj (condensedRingObj (Profinite.continuousMapRingObj E.1) X) := inferInstance

/-- Cache of the existing continuous coefficient structure, with exactly its original data.
Source: the coefficient-ring morphism and monoidal inverse image of Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison). -/
instance integralExtensionCoefficientMonoidHom [TopologicalSpace.NoetherianSpace X] :
    IsMonHom (padicIntegersToPadicSubfield X ℓ E) := inferInstance

/-- Cache of the existing integral module-category structure, with unchanged data.
Source: internal modules over the pulled-back continuous integral coefficient ring
(blueprint: lem-sfb-integral-derived-extension-comparison). -/
instance integralExtensionModuleMonoidal [TopologicalSpace.NoetherianSpace X] :
    MonoidalCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) := inferInstance

/-- Cache of the existing integral module-category structure, with unchanged data.
Source: internal modules over the pulled-back continuous integral coefficient ring
(blueprint: lem-sfb-integral-derived-extension-comparison). -/
instance integralExtensionModuleAbelian [TopologicalSpace.NoetherianSpace X] :
    Abelian (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)) := inferInstance

/-- Scalar extension along the actual integral inclusion is left exact.
Source: Bhatt--Scholze, Section 6.8, integral localization
(blueprint: lem-sfb-integral-derived-extension-comparison).
Proof: unfold the definitionally identical continuous coefficient maps and apply
lem-weil-pbc-continuous-integral-scalar-exact. Independently, the extension--restriction
adjunction of sk-def-sfb-change-of-scalars gives preservation of finite colimits;
lem-sfb-preserving-colimits-additive gives additivity. Together these are exactness. -/
@[instance] theorem integralExtension_exact
    [TopologicalSpace.NoetherianSpace X] :
    PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact CondensedRing.integralScalarExtension_exact ℓ E.1 X

/-- Cache the actual derived extension from the recorded derived adjunction's left functor.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison).
The left functor is the specified total left derived extension, with its existing
structure arguments retained. No alternative functor is chosen. -/
abbrev integralExtensionDerived [TopologicalSpace.NoetherianSpace X] :=
  (fun {A B : _} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (_ : F ⊣ G) ↦ F)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicIntegersToPadicSubfield X ℓ E))

/-- The specified counit of the actual total left derived extension.
Source: the K-flat total left derived construction, Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison). -/
def integralExtensionDerivedCounit [TopologicalSpace.NoetherianSpace X] :=
  (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctorCounit

/-- The specified derived extension with its own counit has the left derived universal property.
Source: the K-flat total left derived construction; Stacks Tag 015F
(blueprint: lem-sfb-integral-derived-extension-comparison).
Proof: integralExtensionDerived is the left functor of the recorded derived adjunction,
which is exactly Functor.leftDerivedFunctor of the specified scalar extension.
Its counit is integralExtensionDerivedCounit. The generic isLeftDerivedFunctor instance
in LeftDerivedFunctor.Defs gives the universal property, computed on K-flat resolutions.
No exactness or additional structure is assumed beyond the existing module framework. -/
@[instance] theorem integralExtensionDerived_isLeftDerived
    [TopologicalSpace.NoetherianSpace X] :
    (integralExtensionDerived X ℓ E).IsLeftDerivedFunctor
      (integralExtensionDerivedCounit X ℓ E)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  dsimp only [integralExtensionDerived, integralExtensionDerivedCounit]
  infer_instance

/-- The canonical comparison with termwise extension, for this actual coefficient map.
Source: Bhatt--Scholze, Section 6.8; Stacks Tag 015F
(blueprint: lem-sfb-integral-derived-extension-comparison).
This is the same leftDerivedUnique construction as leftDerivedFunctorIsoMapDerivedCategory:
uniqueness compares the specified derived counit with the invertible termwise counit. -/
def integralExtensionTermwiseComparison [TopologicalSpace.NoetherianSpace X] :=
  Functor.leftDerivedUnique
    (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).mapDerivedCategory
    (integralExtensionDerived X ℓ E)
    (integralExtensionDerivedCounit X ℓ E)
    (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))

/-- The shift of L transported from termwise extension along the canonical comparison.
Source: Stacks Tags 015F and 014X; Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison).
At K the map is alpha at K[1], then the termwise shift, then the shifted inverse of alpha. -/
instance integralExtensionCommShift [TopologicalSpace.NoetherianSpace X] :
    (integralExtensionDerived X ℓ E).CommShift ℤ :=
  Functor.CommShift.ofIso (integralExtensionTermwiseComparison X ℓ E).symm ℤ

/-- L preserves distinguished triangles for the transported shift.
Source: Stacks Tags 015F and 014X; Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison).
Proof: termwise exact extension is triangulated by
lem-weil-pbc-exact-functor-derived-factorization. Naturality of the canonical comparison
identifies the first two arrows, and the transported shift identifies the last arrow.
The image under L is isomorphic to the distinguished termwise image, so is distinguished. -/
@[instance] theorem integralExtension_triangulated
    [TopologicalSpace.NoetherianSpace X] :
    (integralExtensionDerived X ℓ E).IsTriangulated := by
  let := Functor.CommShift.ofIso_compatibility
    (integralExtensionTermwiseComparison X ℓ E).symm ℤ
  exact Functor.isTriangulated_of_iso (integralExtensionTermwiseComparison X ℓ E).symm

/-- Additivity of the specified restriction F to bounded constructible objects.
Source: blueprint def-sfb-bounded-constructible-extend-scalars; Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison).
Proof: F acts on morphisms by L. Addition is inherited from the ambient full subcategories.
The inclusion j is faithful, so additivity of L gives additivity of F. -/
@[instance] theorem boundedConstructibleIntegralExtension_additive
    [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructibleExtendScalars X ℓ E).Additive := by
  have : (integralExtensionDerived X ℓ E).Additive :=
    Functor.additive_of_iso (integralExtensionTermwiseComparison X ℓ E).symm
  have : (boundedConstructibleExtendScalars X ℓ E ⋙
      (boundedConstructible _).ι).Additive :=
    Functor.additive_of_iso (boundedConstructibleExtendScalarsCompatibility X ℓ E).symm
  exact Functor.additive_of_comp_faithful
    (boundedConstructibleExtendScalars X ℓ E) (boundedConstructible _).ι

/-- The shift on Fj is transported from iL along the specified compatibility beta.
Source: blueprint def-sfb-bounded-constructible-extend-scalars; Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison).
This uses the inherited shift of the integral source and does not require the rational
bounded constructible target to have a triangulated structure. -/
instance boundedConstructibleIntegralExtensionAmbientCommShift
    [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructibleExtendScalars X ℓ E ⋙ (boundedConstructible _).ι).CommShift ℤ :=
  Functor.CommShift.ofIso (boundedConstructibleExtendScalarsCompatibility X ℓ E).symm ℤ

/-- The specified beta commutes with shifts, including the shift in the last triangle arrow.
Source: blueprint def-sfb-bounded-constructible-extend-scalars; Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison).
Proof: the shift on Fj is transported from iL along beta. The defining conjugation
identity is exactly NatTrans.CommShift for beta, in every integer degree. -/
@[instance] theorem boundedConstructibleIntegralExtensionCompatibility_commShift
    [TopologicalSpace.NoetherianSpace X] :
    NatTrans.CommShift (boundedConstructibleExtendScalarsCompatibility X ℓ E).hom ℤ := by
  let := Functor.CommShift.ofIso_compatibility
    (boundedConstructibleExtendScalarsCompatibility X ℓ E).symm ℤ
  exact NatTrans.CommShift.of_iso_inv
    (boundedConstructibleExtendScalarsCompatibility X ℓ E).symm ℤ

/-- The specified beta identifies entire image triangles, with its own components at
all three vertices, rather than merely identifying the three objects.
Source: blueprint def-sfb-bounded-constructible-extend-scalars; Bhatt--Scholze, Section 6.8
(blueprint: lem-sfb-integral-derived-extension-comparison).
The first two squares are naturality and the third uses the transported shift. -/
def boundedConstructibleIntegralExtensionTriangleComparison
    [TopologicalSpace.NoetherianSpace X] :=
  Functor.mapTriangleIso (boundedConstructibleExtendScalarsCompatibility X ℓ E)

/-- Fj preserves every distinguished source triangle. Its specified comparison beta
identifies this image with the distinguished iL image as a whole triangle.
Source: Bhatt--Scholze, Proposition 6.8.14(2), preparatory triangulated comparison
(blueprint: lem-sfb-integral-derived-extension-comparison).
Proof: the integral source has inherited distinguished triangles by step 4 of the node.
Its inclusion i preserves these triangles, and integralExtension_triangulated makes
the iL image distinguished. Step 5 transports its shift along the specified beta;
boundedConstructibleIntegralExtensionTriangleComparison identifies all three arrows.
Closure of distinguished triangles under isomorphism gives the Fj image assertion. -/
theorem integralDerivedExtension_comparison
    [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructibleExtendScalars X ℓ E ⋙
      (boundedConstructible _).ι).IsTriangulated := by
  exact Functor.isTriangulated_of_iso
    (boundedConstructibleExtendScalarsCompatibility X ℓ E).symm

end AlgebraicGeometry.ProEtale
