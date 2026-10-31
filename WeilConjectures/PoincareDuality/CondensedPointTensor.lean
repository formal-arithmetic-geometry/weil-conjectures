/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ExactSectionsDerivedCup
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleCoyoneda

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

/-- Exactness at the algebraically closed point for the recorded internal-module sections.
Source: Stacks 0991, final pointed neighbourhood and exact module sections
(blueprint: def-pod-condensed-point-tensor).
Proof: every covering sieve of the final pointed object contains its identity, so
sections preserve epimorphisms and all colimits. Kernels are computed sectionwise.
The internal/section module equivalence and the constant-scalar identification preserve
these statements and identify the functor with condensedRingCoefficientSections. -/
theorem sections_exact :
    PreservesFiniteLimits (condensedRingCoefficientSections Λ (Spec (.of k))) ∧
      PreservesFiniteColimits (condensedRingCoefficientSections Λ (Spec (.of k))) := by
  sorry

/-- The exactness witness changes no objects or maps.
Source: exact geometric-point sections (blueprint: def-pod-condensed-point-tensor). -/
instance sectionsLimits :
    PreservesFiniteLimits (condensedRingCoefficientSections Λ (Spec (.of k))) :=
  (sections_exact Λ k).1

/-- The exactness witness changes no objects or maps.
Source: exact geometric-point sections (blueprint: def-pod-condensed-point-tensor). -/
instance sectionsColimits :
    PreservesFiniteColimits (condensedRingCoefficientSections Λ (Spec (.of k))) :=
  (sections_exact Λ k).2

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
  sorry

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

/-- Exact point sections preserve relative tensor, with the specified comparison.
Source: Stacks 07A4 and 03EL (blueprint: def-pod-condensed-point-tensor).
Proof: final-point evaluation identifies sheafification with evaluation. Thus the
ordinary section tensor is invertible. The signed total comparison is invertible and
sends flat-term K-flat models to such models. Localizing its inverse proves the claim. -/
theorem tensor_isIso (M N : DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k))))) : IsIso (tensor Λ k M N) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.TraceCupPoint
