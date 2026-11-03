/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars

import WeilConjectures.CategoryTheory.Cochain.CochainDerivedAdjunction

/-!
# Constructed derived scalar adjunctions

Source: Stacks Project, Tags 06YY, 0FND and 09T5; the scalar-adjunction construction
in paragraph three of the current blueprint proof of `lem-pur-ordinary-kunneth-finite-ring`
(blueprint: lem-pur-scalar-change-adjunctions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Cache the exact restriction instance at the fixed module universe.
Source: restriction/extension adjunction (blueprint: lem-pur-scalar-change-adjunctions). -/
local instance pointRestrictionFiniteLimits
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} φ) := by
  refine ⟨fun J _ _ ↦ ?_⟩
  let h : PreservesLimitsOfSize.{0, 0} (ModuleCat.restrictScalars.{u + 1} φ) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).rightAdjoint_preservesLimits
  exact h.preservesLimitsOfShape (J := J)

/-- Cache the coextension adjunction at the fixed module universe.
Source: ordinary coefficient restriction (blueprint: lem-pur-scalar-change-adjunctions). -/
local instance pointRestrictionLeftAdjoint
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u + 1} φ).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint

/-- Cache countable coproducts using the sheaf category's existing small colimits.
Source: ordinary sheaf colimits (blueprint: lem-pur-scalar-change-adjunctions). -/
local instance siteCountableCoproducts
    (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    HasCountableCoproducts (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  ⟨fun J _ ↦ (inferInstance :
    HasColimitsOfSize.{0, 0}
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))).has_colimits_of_shape (Discrete J)⟩

/-- The universal ordinary cochain derived pair admits its normalized scalar adjunction.
Source: Stacks 06YY, 0FND and 09T5 (blueprint: lem-pur-scalar-change-adjunctions).
Proof: categorical K-flat left resolutions form a derivability structure. Apply the
cochain derived-adjunction theorem to this structure and the fixed universal counit.
It normalizes the derived unit on every cochain complex, hence on K-flat ones. -/
theorem scalarChangePointAdjunction_exists
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    ∃ adj : ModuleCat.ordinaryDerivedExtendScalars φ ⊣
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).mapDerivedCategory,
      ∀ P : CochainComplex (ModuleCat.{u + 1} A) ℤ,
      adj.unit.app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).mapDerivedCategory.map
          ((ModuleCat.ordinaryDerivedChangeOfRings φ).counit.app P) ≫
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ).mapHomologicalComplex
            (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).mapHomologicalComplex
          (.up ℤ)).unit.app P) := by
  let d := ModuleCat.ordinaryDerivedChangeOfRings φ
  let := d.universal
  let good : ObjectProperty (CochainComplex (ModuleCat.{u + 1} A) ℤ) :=
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ)).kFlat
  have hres : ∀ K : CochainComplex (ModuleCat.{u + 1} A) ℤ,
      ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (p : P ⟶ K),
        good P ∧ QuasiIso p := by
    intro K
    obtain ⟨r⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
      (Φ := (HomologicalComplex.quasiIso (ModuleCat.{u + 1} A) (.up ℤ)).localizerMorphismKFlat)
      K
    exact ⟨r.X₁.obj, r.w, r.X₁.property, r.hw⟩
  obtain ⟨adj, hunit⟩ := Functor.exists_cochainDerivedAdjunction
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ) d.F d.counit good hres d.computes
  exact ⟨adj, hunit⟩

/-- The point scalar adjunction, chosen from a proved normalized construction.
Source: Stacks 06YY and 0FND (blueprint: lem-pur-scalar-change-adjunctions). -/
def scalarChangePointAdjunction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    ModuleCat.ordinaryDerivedExtendScalars φ ⊣
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).mapDerivedCategory :=
  Classical.choose (scalarChangePointAdjunction_exists φ)

/-- Ordinary scalar extension of module-valued sheaves inverts quasi-isomorphisms
between categorical K-flat complexes. No flatness of the ring map is assumed.
Source: Stacks 06YY (blueprint: lem-pur-scalar-change-adjunctions).
Proof: after exact conservative restriction, scalar extension is tensor with the
constant module B; K-flatness makes this tensor invert the given quasi-isomorphism. -/
theorem scalarChangeSitePreservesKFlatQuasiIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    (Sheaf.extendScalars T.smallEtaleTopology φ).PreservesKFlatQuasiIso := by
  let J := T.smallEtaleTopology
  let : Algebra A B := φ.toAlgebra
  have : (Sheaf.restrictScalars J φ).ReflectsIsomorphisms :=
    Sheaf.reflectsIsomorphisms_restrictScalars J φ
  exact ⟨fun hK hL a _ ↦ CochainComplex.quasiIso_map_of_iso_tensorRight _ _
    (Sheaf.extendScalarsCompRestrictScalarsIso J A B) a hK hL⟩

/-- The actual total left derived functor of sheafified ordinary scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-scalar-change-adjunctions). -/
def scalarChangeSiteExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    DerivedCategoryModule A T ⥤ DerivedCategoryModule B T :=
  let := scalarChangeSitePreservesKFlatQuasiIso φ T
  (Sheaf.extendScalars T.smallEtaleTopology φ).leftDerivedFunctor

/-- Derived scalar extension is left adjoint to exact scalar restriction on the site.
Source: Stacks 0FND and 09T5 (blueprint: lem-pur-scalar-change-adjunctions). -/
def scalarChangeSiteAdjunction
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u}) :
    scalarChangeSiteExtension φ T ⊣ Sheaf.derivedRestrictScalars T.smallEtaleTopology φ := by
  let := scalarChangeSitePreservesKFlatQuasiIso φ T
  exact (Sheaf.extendScalarsAdjunction T.smallEtaleTopology φ).derivedAdjunction.ofNatIsoRight
    (Sheaf.restrictScalars T.smallEtaleTopology φ).rightDerivedFunctorIsoMapDerivedCategory

end AlgebraicGeometry.Etale
