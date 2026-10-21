/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.PointFiniteFreeSectionsTensor
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Derived descent of the point sections-tensor comparison

Source: Stacks Project, sites-cohomology.tex, Tag 06YY (lemma-derived-base-change),
derived.tex, Tags 015F and 06XN, and categories.tex, Tag 04VG
(blueprint: lem-weil-point-derived-sections-tensor-descent).

The ordinary and derived extensions and their counit are the published constructions.
The assertion retains the representative normalization, every K-flat resolution, and
naturality on roofs. All complexes and derived categories are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u wE wL
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures
namespace PointDerivedSectionsTensor

variable {k : Type t} [Field k] {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L} (d : PointFiniteFreeSectionsTensorData k l E L ι)

/-- Sections with their constant-value integral action, at the source coefficient field.
Source: Stacks 03CW (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev sectionsE := pointFiniteFreeEvaluation k l E d.coefficientE

/-- Sections with their constant-value integral action, at the target coefficient field.
Source: Stacks 03CW (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev sectionsL := pointFiniteFreeEvaluation k l L d.coefficientL

/-- The source ordinary composite A(C) = Gamma(C) tensor O_L, before localization.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev A := sectionsE d ⋙ pointFiniteFreeModuleTensor.{t, u} l E L ι

/-- The target ordinary composite B(C) = Gamma(C tensor R_L), before localization.
Source: Stacks 06YY (blueprint: lem-weil-point-derived-sections-tensor-descent). -/
abbrev B := completedOrdinaryScalarExtension l E L ι (Spec (.of k)) ⋙ sectionsL d

end PointDerivedSectionsTensor

open PointDerivedSectionsTensor

variable {k : Type t} [Field k] {l : ℕ} [Fact l.Prime]
  {E L : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  {ι : E →ₐ[ℚ_[l]] L}
  [HasDerivedCategory.{wE} (ModuleCat.{max u (t + 1)}
    (Padic.coefficientExtensionIntegers l E))]
  [HasDerivedCategory.{wL} (ModuleCat.{max u (t + 1)}
    (Padic.coefficientExtensionIntegers l L))]

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- All clauses of derived descent, with canonical normalization equations. Instance
fields assert exactness rather than assuming it. The equations use Mathlib's specified
factorizations of exact functors; these are the identifications suppressed in the node.
The resolution equation identifies the same theta component for every resolution, hence
also states independence without assuming any comparison map between resolutions.
Source: Stacks 06YY, 015F, 06XN and 04VG
(blueprint: lem-weil-point-derived-sections-tensor-descent). -/
structure PointDerivedSectionsTensorData (d : PointFiniteFreeSectionsTensorData k l E L ι) where
  [sectionsE_additive : (sectionsE d).Additive]
  [sectionsL_additive : (sectionsL d).Additive]
  [sectionsE_limits : PreservesFiniteLimits (sectionsE d)]
  [sectionsE_colimits : PreservesFiniteColimits (sectionsE d)]
  [sectionsL_limits : PreservesFiniteLimits (sectionsL d)]
  [sectionsL_colimits : PreservesFiniteColimits (sectionsL d)]
  [sheaf_limits : PreservesFiniteLimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))]
  [sheaf_colimits : PreservesFiniteColimits
    (completedOrdinaryScalarExtension l E L ι (Spec (.of k)))]
  [module_limits : PreservesFiniteLimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)]
  [module_colimits : PreservesFiniteColimits (pointFiniteFreeModuleTensor.{t, u} l E L ι)]
  sheaf_quasiIso : ∀ (C C' : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ)
    (f : C ⟶ C'), QuasiIso f →
      QuasiIso ((completedOrdinaryScalarComplex l E L ι (Spec (.of k))).map f)
  module_quasiIso : ∀ (C C' : CochainComplex
      (ModuleCat.{max u (t + 1)} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (f : C ⟶ C'), QuasiIso f →
      QuasiIso (((pointFiniteFreeModuleTensor.{t, u} l E L ι).mapHomologicalComplex
        (.up ℤ)).map f)
  sectionsE_quasiIso : ∀ (C C' : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ)
    (f : C ⟶ C'), QuasiIso f →
      QuasiIso (((sectionsE d).mapHomologicalComplex (.up ℤ)).map f)
  sectionsL_quasiIso : ∀ (C C' : CochainComplex (integralTowerModules l L (Spec (.of k))) ℤ)
    (f : C ⟶ C'), QuasiIso f →
      QuasiIso (((sectionsL d).mapHomologicalComplex (.up ℤ)).map f)
  comparison : (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).mapDerivedCategory ≅
    completedDerivedScalarExtension l E L ι (Spec (.of k))
  comparison_counit : ∀ C : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
    comparison.inv.app (DerivedCategory.Q.obj C) ≫
        (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).mapDerivedCategoryFactors.hom.app
          C = completedScalarCounit l E L ι (Spec (.of k)) C
  comparison_unique : ∀ δ :
      (completedOrdinaryScalarExtension l E L ι (Spec (.of k))).mapDerivedCategory ≅
        completedDerivedScalarExtension l E L ι (Spec (.of k)),
    (∀ C : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
      δ.inv.app (DerivedCategory.Q.obj C) ≫
          (completedOrdinaryScalarExtension l E L ι
            (Spec (.of k))).mapDerivedCategoryFactors.hom.app C =
        completedScalarCounit l E L ι (Spec (.of k)) C) → δ = comparison
  localized : (A d).mapDerivedCategory ≅ (B d).mapDerivedCategory
  localized_representative : ∀ C : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
    localized.hom.app (DerivedCategory.Q.obj C) ≫ (B d).mapDerivedCategoryFactors.hom.app C =
      (A d).mapDerivedCategoryFactors.hom.app C ≫ DerivedCategory.Q.map (d.complexes.hom.app C)
  localized_unique : ∀ τ : (A d).mapDerivedCategory ⟶ (B d).mapDerivedCategory,
    (∀ C : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ,
      τ.app (DerivedCategory.Q.obj C) ≫ (B d).mapDerivedCategoryFactors.hom.app C =
        (A d).mapDerivedCategoryFactors.hom.app C ≫
          DerivedCategory.Q.map (d.complexes.hom.app C)) → τ = localized.hom
  theta : (sectionsE d).mapDerivedCategory ⋙
      (pointFiniteFreeModuleTensor.{t, u} l E L ι).mapDerivedCategory ≅
    completedDerivedScalarExtension l E L ι (Spec (.of k)) ⋙ (sectionsL d).mapDerivedCategory
  theta_eq : theta =
    (Functor.mapDerivedCategoryCompIso (sectionsE d)
      (pointFiniteFreeModuleTensor.{t, u} l E L ι)).symm ≪≫ localized ≪≫
    Functor.mapDerivedCategoryCompIso
      (completedOrdinaryScalarExtension l E L ι (Spec (.of k))) (sectionsL d) ≪≫
    Functor.isoWhiskerRight comparison (sectionsL d).mapDerivedCategory
  resolution : ∀ (C P : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ)
    (q : P ⟶ C) [QuasiIso q],
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) P →
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology (Spec (.of k)))
      (R := completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) (P.X i)) →
    (Functor.mapDerivedCategoryCompIso (sectionsE d)
        (pointFiniteFreeModuleTensor.{t, u} l E L ι)).hom.app (DerivedCategory.Q.obj C) ≫
      theta.hom.app (DerivedCategory.Q.obj C) ≫
        (sectionsL d).mapDerivedCategory.map
          (inv ((completedDerivedScalarExtension l E L ι (Spec (.of k))).map
            (DerivedCategory.Q.map q)) ≫ completedScalarCounit l E L ι (Spec (.of k)) P) ≫
        (sectionsL d).mapDerivedCategoryFactors.hom.app
          ((completedOrdinaryScalarComplex l E L ι (Spec (.of k))).obj P) =
      inv ((A d).mapDerivedCategory.map (DerivedCategory.Q.map q)) ≫
        (A d).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map (d.complexes.hom.app P)
  roof : ∀ (C H J : CochainComplex (integralTowerModules l E (Spec (.of k))) ℤ)
    (q : H ⟶ C) (f : H ⟶ J) [QuasiIso q],
    localized.hom.app (DerivedCategory.Q.obj C) ≫
        inv ((B d).mapDerivedCategory.map (DerivedCategory.Q.map q)) ≫
        (B d).mapDerivedCategory.map (DerivedCategory.Q.map f) =
      inv ((A d).mapDerivedCategory.map (DerivedCategory.Q.map q)) ≫
        (A d).mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
        localized.hom.app (DerivedCategory.Q.obj J)

/-- Exact point functors descend, with the counit-normalized derived tensor comparison.
Source: Stacks 06YY, 015F, 06XN and 04VG
(blueprint: lem-weil-point-derived-sections-tensor-descent).

Proof:
1. The algebraic closure in def-weil-finite-field-fiber is algebraically closed.
lem-weil-point-proetale-sections-exact makes evaluation exact. Transport the section-ring
action through d.coefficientE and d.coefficientL. The two tensor functors are exact by
lem-weil-point-finite-free-sections-tensor. Apply the exact-functor factorization
lem-weil-pbc-exact-functor-derived-factorization: all four termwise functors preserve
quasi-isomorphisms, and their derived functors have the displayed factorizations.
2. The left-derived counit of lem-pur-derived-change-of-rings is invertible on K-flat
complexes, by lem-pur-left-derived-from-kflat-class. Resolve C by a K-flat complex P
with flat terms using lem-pc-kflat-resolution. Counit naturality and exactness of
ordinary extension show epsilon_C is invertible, since epsilon_P and both images of
P to C are invertible.
3. Descend this counit and its inverse using lem-weil-pbc-localization-universal-property.
This gives comparison, with its inverse composed with the ordinary factorization equal
to the counit on every complex. Full faithfulness of precomposition fixes it uniquely.
4. Descend d.complexes by the same localization property to localized. Its representative
equation and uniqueness are the natural-transformation clauses of that property.
Compose with the exact-functor composition isomorphism and comparison to obtain theta.
5. For any resolution q, put rho_q = LT(Qq)^{-1} followed by epsilon_P. Counit naturality
gives epsilon_C = rho_q followed by Q(Tq). Naturality of d.complexes and the exact-functor
factorizations then give resolution. This equation identifies the same theta_C for every
resolution, proving independence without a cochain comparison between resolutions.
6. Chain naturality for q and f, followed by inversion of their localized q images,
gives roof. The localized transformation and comparison are natural transformations
on the whole derived category, so their composite is natural for every derived morphism.
No boundedness, constructibility or completeness condition was used. -/
theorem point_derived_sections_tensor_descent
    (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (E L : IntermediateField ℚ_[l] Ω)
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L] (h : E ≤ L)
    [HasDerivedCategory.{wE} (ModuleCat.{max u (t + 1)}
      (Padic.coefficientExtensionIntegers l E))]
    [HasDerivedCategory.{wL} (ModuleCat.{max u (t + 1)}
      (Padic.coefficientExtensionIntegers l L))]
    (d : PointFiniteFreeSectionsTensorData D.k l E L (IntermediateField.inclusion h)) :
    Nonempty (PointDerivedSectionsTensorData d) := by
  sorry

end WeilConjectures
