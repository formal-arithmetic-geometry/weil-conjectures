/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleCoyoneda
import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedWeaklyContractible
import Mathlib.CategoryTheory.Sites.LocalSite
import WeilConjectures.SixFunctors.RingedSitePoint
import WeilConjectures.Algebra.Homology.RingedSitePointFlat
import WeilConjectures.SmoothPurity.RingedSitePointTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
import WeilConjectures.CategoryTheory.ZetaWeil.SectionRingGlobalSections
import WeilConjectures.CategoryTheory.ModuleObjects.Linear
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
import WeilConjectures.CategoryTheory.Preadditive.CoyonedaSectionsExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensorDataExists
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupPoint.CondensedPointTensorDataUnique

/-! # Normalized tensor on exact geometric-point sections

Source: Stacks 07A4, 03EL and 0991; the representative normalization in
the trace--cup construction. The sections functor is the recorded
coefficient-sections functor, so its scalar ring is precisely the singleton ring.
(blueprint: def-pod-condensed-point-tensor)
-/

@[expose] public noncomputable section
set_option synthInstance.maxSize 4096
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

/-- The canonical Koszul braiding on the ordinary scalar derived category.
Source: the signed point tensor convention (blueprint: def-pod-condensed-point-tensor). -/
@[irreducible] def scalarBraiding :
    BraidedCategory (DerivedCategory (ModuleCat.{u + 1} (Γ Λ))) :=
  DerivedCategory.braidedCategory' (ModuleCat.{u + 1} (Γ Λ))

/-- The canonical Koszul braiding on the native coefficient-module derived category.
Source: the signed tensor convention (blueprint: def-pod-condensed-point-tensor). -/
@[irreducible] def siteBraiding (X : Scheme.{u}) :
    BraidedCategory (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  DerivedCategory.braidedCategory'
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

/-- The section tensor is fixed on pure tensors; its chain and derived maps are fixed
by the total-summand and localization squares of ExactSectionsDerivedCup.
Source: Stacks 07A4 and 03EL, including the signed total-complex construction
(blueprint: def-pod-condensed-point-tensor).
Proof: the ordinary pairing sends two maps from the regular module to their tensor,
precomposed with the inverse unit multiplication. This is the section tensor.
Apply it on every total summand, with the Koszul differential, and localize on flat-term
K-flat resolutions. Exact point sections preserve these resolutions. The localization
square specifies the derived pairing uniquely. Pure tensors generate each ordinary
tensor, total summands generate the chain tensor, and restriction along the K-flat
localization is fully faithful, proving uniqueness of the whole data record. Its unit
is the scalar section; hence the ordinary, chain and derived units are also determined. -/
theorem tensorData_existsUnique :
    ∃! d : ExactSectionsDerivedCup (condensedRingCoefficientSections Λ (Spec (.of k))),
      ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
          (condensedRingObj Λ (Spec (.of k))))
        (x : (condensedRingCoefficientSections Λ (Spec (.of k))).obj M)
        (y : (condensedRingCoefficientSections Λ (Spec (.of k))).obj N),
        (d.ordinary.μ M N).hom (x ⊗ₜ[Γ Λ] y) = (λ_ _).inv ≫ (x ⊗ₘ y) := by
  obtain ⟨d, hd⟩ := tensorData_exists Λ k
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  exact tensorData_unique Λ k d' d hd' hd

/-- The unique normalized derived section cup, with actual total-complex data.
Source: Stacks 07A4 (blueprint: def-pod-condensed-point-tensor). -/
@[irreducible] def tensorData :
    ExactSectionsDerivedCup (condensedRingCoefficientSections Λ (Spec (.of k))) :=
  (tensorData_existsUnique Λ k).choose

/-- The recorded right derived sections, with their fixed scalar ring.
Source: point evaluation (blueprint: def-pod-condensed-point-tensor). -/
abbrev fiber := (condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor

/-- Canonical exact/right-derived comparison, kept opaque for downstream elaboration.
Source: termwise exact point sections (blueprint: def-pod-condensed-point-tensor). -/
@[irreducible] def exactComparison : fiber Λ k ≅
    (condensedRingCoefficientSections Λ (Spec (.of k))).mapDerivedCategory :=
  (condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctorIsoMapDerivedCategory

/-- The normalized tensor in the exact termwise presentation.
Source: total-summand and localization comparison
(blueprint: def-pod-condensed-point-tensor). -/
@[irreducible] def exactTensor (M N : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))) :
    (condensedRingCoefficientSections Λ (Spec (.of k))).mapDerivedCategory.obj M ⊗
      (condensedRingCoefficientSections Λ (Spec (.of k))).mapDerivedCategory.obj N ⟶
        (condensedRingCoefficientSections Λ (Spec (.of k))).mapDerivedCategory.obj (M ⊗ N) :=
  (tensorData Λ k).derived.μ M N

/-- The inverse form of the point tensor comparison, normalized on section tensors.
Source: Stacks 07A4 (blueprint: def-pod-condensed-point-tensor). -/
def tensor (M N : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))) :
    (fiber Λ k).obj M ⊗ (fiber Λ k).obj N ⟶ (fiber Λ k).obj (M ⊗ N) :=
  ((exactComparison Λ k).hom.app M ⊗ₘ (exactComparison Λ k).hom.app N) ≫
    exactTensor Λ k M N ≫ (exactComparison Λ k).inv.app (M ⊗ N)

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
