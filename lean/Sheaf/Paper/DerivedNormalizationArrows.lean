/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

/-! # Universal arrows for derived coefficient normalization

Source: Stacks Project, Tags 06YY, 07A6 and 06Y5, derived extension and its adjunction
(blueprint: def-weil-pbc-derived-normalization-arrows).

A normalization isomorphism can equivalently be supplied by its universal arrow to
restriction of scalars. This encoding retains its specific arrow, and avoids choosing
an additional model of the total derived tensor functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S]

/-- Constant module sheaves are exact, and restriction of coefficient scalars on module
sheaves is additive and exact. These are the exact functors used below.
Source: Stacks Tags 093J, 03DA and 06YY
(blueprint: def-weil-pbc-derived-normalization-arrows).
Proof: constant presheaves preserve all finite limits and colimits. Sheafification is
left exact and is a left adjoint, so the constant sheaf functor is exact. Restriction of
scalars preserves all module limits and colimits; limits of sheaves are sectionwise, and
colimits are sheafifications of presheaf colimits. Since restriction of scalars preserves
sheafification, it preserves these colimits too. It is additive on sections. -/
theorem normalizationCoefficientExactness (q : R →+* S) :
    (PreservesFiniteLimits (constantSheaf J (ModuleCat.{u + 1} R)) ∧
      PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} R))) ∧
    ((sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).Additive ∧
      PreservesFiniteLimits (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) ∧
      PreservesFiniteColimits (sheafCompose J 
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))) ∧
    J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) := by
  sorry

/-- Exactness of constants, from the coefficient exactness statement.
Source: Stacks Tag 093J (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable instance normalizationConstantLimits :
    PreservesFiniteLimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
  (normalizationCoefficientExactness J (RingHom.id R)).1.1

/-- Exactness of constants, from the coefficient exactness statement.
Source: Stacks Tag 093J (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable instance normalizationConstantColimits :
    PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
  (normalizationCoefficientExactness J (RingHom.id R)).1.2

/-- Additivity of coefficient restriction.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable instance normalizationRestrictAdditive (q : R →+* S) :
    (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).Additive :=
  (normalizationCoefficientExactness J q).2.1.1

/-- Left exactness of coefficient restriction.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable instance normalizationRestrictLimits (q : R →+* S) :
    PreservesFiniteLimits (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) :=
  (normalizationCoefficientExactness J q).2.1.2.1

/-- Right exactness of coefficient restriction.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable instance normalizationRestrictColimits (q : R →+* S) :
    PreservesFiniteColimits (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) :=
  (normalizationCoefficientExactness J q).2.1.2.2

/-- Coefficient restriction commutes with sheafification.
Source: Stacks Tag 03DA (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable instance normalizationRestrictSheafification (q : R →+* S) :
    J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) :=
  (normalizationCoefficientExactness J q).2.2

/-- The canonical derived constant sheaf functor, using the existing exact-functor
localization. Source: Stacks Tag 05RU
(blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable abbrev normalizationConstant :
    DerivedCategory (ModuleCat.{u + 1} R) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  (constantSheaf J (ModuleCat.{u + 1} R)).mapDerivedCategory

/-- Derived restriction of coefficient scalars is the exact restriction functor applied
termwise. Source: Stacks Tag 06YY
(blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable abbrev normalizationRestrict (q : R →+* S) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} S)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)).mapDerivedCategory

/-- Ordinary module restriction is additive and exact in the fixed module universe.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-normalization-arrows).
Proof: restriction leaves additive groups and maps unchanged. Kernels, cokernels, finite
products and finite coproducts have the restricted action, so their universal properties
remain valid. This proves additivity and preservation of finite limits and colimits. -/
theorem normalizationModuleRestrictExactness (q : R →+* S) :
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q).Additive ∧
      PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ∧
      PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) := by
  sorry

/-- Additivity in the fixed coefficient universe.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable instance (priority := 2000) normalizationModuleAdditive (q : R →+* S) :
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q).Additive :=
  (normalizationModuleRestrictExactness q).1

/-- Left exactness in the fixed coefficient universe.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable instance (priority := 2000) normalizationModuleLimits (q : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) :=
  (normalizationModuleRestrictExactness q).2.1

/-- Right exactness in the fixed coefficient universe.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable instance (priority := 2000) normalizationModuleColimits (q : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) :=
  (normalizationModuleRestrictExactness q).2.2

/-- Exact derived restriction of ordinary module coefficients.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable abbrev normalizationModuleRestrict (q : R →+* S) :
    DerivedCategory (ModuleCat.{u + 1} S) ⥤ DerivedCategory (ModuleCat.{u + 1} R) :=
  (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q).mapDerivedCategory

/-- Constants commute canonically with derived restriction of scalars. This is the
localization of `constantCommuteCompose`, whose components respect constant sections.
Source: Stacks Tags 03DA and 06YY
(blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable def normalizationConstantRestrict (q : R →+* S) :
    normalizationConstant (R := S) J ⋙ normalizationRestrict J q ≅
      normalizationModuleRestrict q ⋙
        normalizationConstant (R := R) J :=
  (Functor.mapDerivedCategoryCompIso (constantSheaf J (ModuleCat.{u + 1} S))
    (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (constantCommuteCompose J
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)) ≪≫
    Functor.mapDerivedCategoryCompIso
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q)
      (constantSheaf J (ModuleCat.{u + 1} R))

/-- The constant normalization arrow is the image of the specified module normalization
arrow, transported by the canonical constant/restriction comparison.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable def normalizationConstantArrow (q : R →+* S)
    {M : DerivedCategory (ModuleCat.{u + 1} R)}
    {N : DerivedCategory (ModuleCat.{u + 1} S)}
    (d : M ⟶ (normalizationModuleRestrict q).obj N) :
    (normalizationConstant J).obj M ⟶
      (normalizationRestrict J q).obj ((normalizationConstant J).obj N) :=
  (normalizationConstant J).map d ≫ (normalizationConstantRestrict J q).inv.app N

section Pullback

variable {D : Type (u + 1)} [Category.{u} D] [EssentiallySmall.{u + 1} D]
  (F : C ⥤ D) (K : GrothendieckTopology D) [F.IsContinuous J K]

/-- The canonical coefficient-restriction comparison for inverse image. It is the mate
of the identity square for sectionwise direct image and restriction of scalars.
Source: Stacks Tags 00WX and 03DA
(blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable def normalizationPullbackMate (q : R →+* S) :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{u + 1} R) J K ⟶
      Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{u + 1} S) J K ⋙
        sheafCompose K (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) :=
  ((mateEquiv
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (ModuleCat.{u + 1} S) J K)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (ModuleCat.{u + 1} R) J K)).symm
      (TwoSquare.mk _ _ _ _ (𝟙 _))).natTrans

/-- The canonical mate is invertible: coefficient restriction commutes with inverse image.
Source: Stacks Tags 00WX and 03DA
(blueprint: def-weil-pbc-derived-normalization-arrows).
Proof: restriction of module scalars preserves all colimits and all finite limits. Thus
it commutes with the comma-category colimits defining presheaf inverse image and with
sheafification. The resulting comparison is the displayed mate, by the adjunction unit
identity on each presheaf section. The two colimit comparisons are isomorphisms. -/
theorem normalizationPullbackMate_isIso (q : R →+* S) :
    IsIso (normalizationPullbackMate J F K q) := by
  sorry

/-- The canonical inverse-image comparison with coefficient restriction.
Source: Stacks Tag 00WX (blueprint: def-weil-pbc-derived-normalization-arrows). -/
noncomputable def normalizationPullbackIso (q : R →+* S) :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{u + 1} R) J K ≅
      Functor.sheafPullbackConstruction.sheafPullback F (ModuleCat.{u + 1} S) J K ⋙
        sheafCompose K (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) :=
  @asIso _ _ _ _ (normalizationPullbackMate J F K q)
    (normalizationPullbackMate_isIso J F K q)

end Pullback

end CategoryTheory
