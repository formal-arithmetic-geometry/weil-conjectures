/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleExtensions
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartKernelsCokernels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import all WeilConjectures.AlgebraicGeometry.ConstructibleFiniteHeart

/-!
# The ind-constructible ambient derived category is triangulated

## Main statements

- `indConstructibleDerived_isTriangulated`: zero, integer shifts, and triangle closure.
- `indConstructibleDerived_isClosedUnderIsomorphisms`: the explicit repleteness clause.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

-- Package the supplied ind-heart results as the weak Serre class API.
private lemma indCohomology_triangulated
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (hKC : IndHeartKernelsCokernelsAssertions Λ X)
    (hExt : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)), S.ShortExact →
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) S.X₁ →
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) S.X₃ →
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) S.X₂) :
    ObjectProperty.IsTriangulated (fun K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ↦
      ∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj K)) := by
  let P := ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
  have : P.ContainsZero := ⟨HasZeroObject.zero.choose, isZero_zero _,
    ObjectProperty.le_ind _ _ (constantModelConstructible_of_isZero Λ X _ (isZero_zero _))⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, fork, hfork, hA, hB⟩
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hKC _ _ f hA hB
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hfork) hk⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, cofork, hcofork, hA, hB⟩
    obtain ⟨_, _, _, _, _, _, _, _, hc⟩ := hKC _ _ f hA hB
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hcofork) hc⟩
  have : P.IsClosedUnderExtensions := ⟨fun hS hA hB ↦ hExt _ hS hA hB⟩
  change (DerivedCategory.homologyProperty P).IsTriangulated
  infer_instance

/-- The full subcategory of the ordinary derived category whose cohomology objects are
ind-constructible in every degree is triangulated, for each of the two canonical coefficient
rings. `ObjectProperty.ind` uses small filtered colimits in the ambient module category. -/
theorem indConstructibleDerived_isTriangulated
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsTriangulated (fun K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ↦
      ∀ n : ℤ,
        ObjectProperty.ind.{u + 1}
          (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
          ((DerivedCategory.homologyFunctor _ n).obj K)) ∧
    ObjectProperty.IsTriangulated (fun K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicAlgClRingObj X ℓ)) ↦
      ∀ n : ℤ,
        ObjectProperty.ind.{u + 1}
          (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
          ((DerivedCategory.homologyFunctor _ n).obj K)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  obtain ⟨hE, hQ⟩ := indHeart_kernelsCokernels ℓ p k hp hpl X
  exact ⟨indCohomology_triangulated _ X (hE E)
      (indConstructible_of_shortExact ℓ E X),
    indCohomology_triangulated _ X hQ
      (indConstructible_of_shortExact_padicAlgCl ℓ X)⟩

end AlgebraicGeometry.ProEtale
