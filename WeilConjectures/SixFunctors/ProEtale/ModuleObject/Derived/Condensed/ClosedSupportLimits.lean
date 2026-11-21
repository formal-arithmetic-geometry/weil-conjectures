/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!
# Sections with closed support are left t-exact and commute with derived limits

Let `Λ` be a commutative condensed ring, `i : Z ⟶ X` a closed immersion with quasi-compact open
complement `j : V ⟶ X`, and `u : S ⟶ Z` an open immersion. On derived categories of module
objects over `Λ`, the functors

* `RΓ_Z : D(X_proét, Λ) ⥤ D(Z_proét, Λ)`
  (`ProEtale.CondensedRing.isGE_rightDerivedFunctor_closedSupport_obj`,
  `ProEtale.CondensedRing.isHomotopyLimit_mapCone_rightDerivedFunctor_closedSupport`),
* `u^* RΓ_Z : D(X_proét, Λ) ⥤ D(S_proét, Λ)`
  (`ProEtale.CondensedRing.isGE_upperStar_rightDerivedFunctor_closedSupport_obj`,
  `ProEtale.CondensedRing.isHomotopyLimit_mapCone_rightDerivedFunctor_closedSupport_upperStar`),
* `- ⊗ L : D(S_proét, Λ) ⥤ D(S_proét, Λ)` for a locally free `Λ_S`-module `L`
  (`ProEtale.CondensedRing.isGE_tensorObj_singleFunctor_of_isLocallyFree`,
  `ProEtale.CondensedRing.isHomotopyLimit_mapCone_tensorRight_singleFunctor_of_isLocallyFree`)

are left t-exact and send homotopy limits of towers (derived inverse limits of sequences) to
homotopy limits. These are collected in
`ProEtale.CondensedRing.closedSupport_upperStar_tensor_isGE_and_isHomotopyLimit`.

## Implementation details

All three functors are triangulated right adjoints: `RΓ_Z` is right adjoint to `i_*`, `u^*` to
the extension by zero `u_!`, and `- ⊗ L` to `- ⊗ L'` for the dual `L'` of `L`. Right adjoints
preserve products, and triangulated functors preserving countable products preserve homotopy
limits (`CategoryTheory.Pretriangulated.IsHomotopyLimit.map`). Left t-exactness follows by
adjunction from right t-exactness of the left adjoints `i_*` (exact) and `- ⊗ L'`
(`DerivedCategory.isLE_tensor`), and for `u^*` from its exactness.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open DerivedCategory.TStructure (t)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- A right adjoint to a functor preserving `≤ n - 1` objects preserves `≥ n` objects. -/
private lemma isGE_obj_of_adjunction {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    {F : DerivedCategory D ⥤ DerivedCategory C} {G : DerivedCategory C ⥤ DerivedCategory D}
    (adj : F ⊣ G) (n : ℤ) (hF : ∀ W : DerivedCategory D, W.IsLE (n - 1) → (F.obj W).IsLE (n - 1))
    (K : DerivedCategory C) [K.IsGE n] : (G.obj K).IsGE n :=
  (t.isGE_iff_orthogonal (n - 1) n (by lia) _).2 fun W f hW ↦ by
    have := hF W hW
    have := adj.isRightAdjoint
    rw [← (adj.homEquiv W K).apply_symm_apply f,
      t.zero ((adj.homEquiv W K).symm f) (n - 1) n (by lia), Adjunction.homEquiv_apply,
      Functor.map_zero, Limits.comp_zero]

section ClosedSupport

variable {Z V X S : Scheme.{u}} (i : Z ⟶ X) (j : V ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
  [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)
include hij

omit [IsCommMonObj Λ] in
/-- Sections with closed support `RΓ_Z : D(X_proét, Λ) ⥤ D(Z_proét, Λ)` are left t-exact. -/
theorem isGE_rightDerivedFunctor_closedSupport_obj (K : DerivedCategory (supportModules Λ X))
    (n : ℤ) [K.IsGE n] : ((closedSupport Λ i j).rightDerivedFunctor.obj K).IsGE n :=
  letI := closedSupport_lowerStarExact Λ i j hij
  isGE_obj_of_adjunction (closedSupportDerivedAdjunction Λ i j hij) n
    (fun W _ ↦ (lowerStar Λ i).isLE_mapDerivedCategory_obj W (n - 1)) K

omit [IsCommMonObj Λ] in
/-- Sections with closed support `RΓ_Z : D(X_proét, Λ) ⥤ D(Z_proét, Λ)` send homotopy limits of
towers to homotopy limits. -/
theorem isHomotopyLimit_mapCone_rightDerivedFunctor_closedSupport
    {F : ℕᵒᵖ ⥤ DerivedCategory (supportModules Λ X)} {c : Cone F} (hc : IsHomotopyLimit c) :
    IsHomotopyLimit ((closedSupport Λ i j).rightDerivedFunctor.mapCone c) :=
  letI := closedSupport_lowerStarExact Λ i j hij
  have : PreservesLimitsOfSize.{0, 0} (closedSupport Λ i j).rightDerivedFunctor :=
    (closedSupportDerivedAdjunction Λ i j hij).rightAdjoint_preservesLimits
  hc.map _

/-- The restriction `u^* RΓ_Z : D(X_proét, Λ) ⥤ D(S_proét, Λ)` of the sections with closed
support to an open subscheme `S` of `Z` is left t-exact. -/
theorem isGE_upperStar_rightDerivedFunctor_closedSupport_obj (u : S ⟶ Z)
    (K : DerivedCategory (supportModules Λ X)) (n : ℤ) [K.IsGE n] :
    ((upperStar Λ u).mapDerivedCategory.obj
      ((closedSupport Λ i j).rightDerivedFunctor.obj K)).IsGE n :=
  have := isGE_rightDerivedFunctor_closedSupport_obj Λ i j hij K n
  (upperStar Λ u).isGE_mapDerivedCategory_obj _ n

/-- The restriction `u^* RΓ_Z : D(X_proét, Λ) ⥤ D(S_proét, Λ)` of the sections with closed
support to an open subscheme `S` of `Z` sends homotopy limits of towers to homotopy limits. -/
theorem isHomotopyLimit_mapCone_rightDerivedFunctor_closedSupport_upperStar
    (u : S ⟶ Z) [IsOpenImmersion u]
    {F : ℕᵒᵖ ⥤ DerivedCategory (supportModules Λ X)} {c : Cone F} (hc : IsHomotopyLimit c) :
    IsHomotopyLimit (((closedSupport Λ i j).rightDerivedFunctor ⋙
      (upperStar Λ u).mapDerivedCategory).mapCone c) :=
  have : PreservesLimitsOfSize.{0, 0} (upperStar Λ u).mapDerivedCategory :=
    (openImmersionLowerShriekUpperStarAdjunction Λ u).mapDerivedCategoryAdjunction
      |>.rightAdjoint_preservesLimits
  (isHomotopyLimit_mapCone_rightDerivedFunctor_closedSupport Λ i j hij hc).map
    (upperStar Λ u).mapDerivedCategory

end ClosedSupport

section Tensor

variable {S : Scheme.{u}} {L : supportModules Λ S}
  (hL : IsLocallyFree (condensedRingObj Λ S) L)
include hL

/-- Tensoring `- ⊗ L : D(S_proét, Λ) ⥤ D(S_proét, Λ)` with a locally free `Λ_S`-module `L` is
left t-exact. -/
theorem isGE_tensorObj_singleFunctor_of_isLocallyFree (K : DerivedCategory (supportModules Λ S))
    (n : ℤ) [K.IsGE n] : (K ⊗ (DerivedCategory.singleFunctor _ 0).obj L).IsGE n := by
  obtain ⟨L', -, ⟨e⟩⟩ := hL.exists_exactPairing_singleFunctor 0
  exact isGE_obj_of_adjunction (tensorRightAdjunction
    ((DerivedCategory.singleFunctor _ (-0)).obj L') ((DerivedCategory.singleFunctor _ 0).obj L)) n
    (fun W _ ↦ by
      simpa using DerivedCategory.isLE_tensor W
        ((DerivedCategory.singleFunctor _ (-0)).obj L') (n - 1) (-0)) K

/-- Tensoring `- ⊗ L : D(S_proét, Λ) ⥤ D(S_proét, Λ)` with a locally free `Λ_S`-module `L` sends
homotopy limits of towers to homotopy limits. -/
theorem isHomotopyLimit_mapCone_tensorRight_singleFunctor_of_isLocallyFree
    {F : ℕᵒᵖ ⥤ DerivedCategory (supportModules Λ S)} {c : Cone F} (hc : IsHomotopyLimit c) :
    IsHomotopyLimit ((tensorRight ((DerivedCategory.singleFunctor _ 0).obj L)).mapCone c) := by
  obtain ⟨L', -, ⟨e⟩⟩ := hL.exists_exactPairing_singleFunctor 0
  have : PreservesLimitsOfSize.{0, 0}
      (tensorRight ((DerivedCategory.singleFunctor _ 0).obj L)) :=
    (tensorRightAdjunction ((DerivedCategory.singleFunctor _ (-0)).obj L')
    ((DerivedCategory.singleFunctor _ 0).obj L)).rightAdjoint_preservesLimits
  exact hc.map _

end Tensor

/-- Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j : V ⟶ X`,
`u : S ⟶ Z` an open immersion and `L` a locally free `Λ_S`-module. The functors
`RΓ_Z : D(X_proét, Λ) ⥤ D(Z_proét, Λ)`, `u^* RΓ_Z : D(X_proét, Λ) ⥤ D(S_proét, Λ)` and
`- ⊗ L : D(S_proét, Λ) ⥤ D(S_proét, Λ)` are left t-exact and send homotopy limits of towers to
homotopy limits. -/
theorem closedSupport_upperStar_tensor_isGE_and_isHomotopyLimit
    {Z V X S : Scheme.{u}}
    (i : Z ⟶ X) (j : V ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (u : S ⟶ Z) [IsOpenImmersion u]
    (L : supportModules Λ S) (hL : IsLocallyFree (condensedRingObj Λ S) L) :
    (∀ (K : DerivedCategory (supportModules Λ X)) (n : ℤ), K.IsGE n →
      ((closedSupport Λ i j).rightDerivedFunctor.obj K).IsGE n) ∧
    (∀ (F : ℕᵒᵖ ⥤ DerivedCategory (supportModules Λ X)) (c : Cone F), IsHomotopyLimit c →
      IsHomotopyLimit ((closedSupport Λ i j).rightDerivedFunctor.mapCone c)) ∧
    (∀ (K : DerivedCategory (supportModules Λ X)) (n : ℤ), K.IsGE n →
      ((upperStar Λ u).mapDerivedCategory.obj
        ((closedSupport Λ i j).rightDerivedFunctor.obj K)).IsGE n) ∧
    (∀ (F : ℕᵒᵖ ⥤ DerivedCategory (supportModules Λ X)) (c : Cone F), IsHomotopyLimit c →
      IsHomotopyLimit (((closedSupport Λ i j).rightDerivedFunctor ⋙
        (upperStar Λ u).mapDerivedCategory).mapCone c)) ∧
    (∀ (K : DerivedCategory (supportModules Λ S)) (n : ℤ), K.IsGE n →
      (K ⊗ (DerivedCategory.singleFunctor _ 0).obj L).IsGE n) ∧
    (∀ (F : ℕᵒᵖ ⥤ DerivedCategory (supportModules Λ S)) (c : Cone F), IsHomotopyLimit c →
      IsHomotopyLimit ((tensorRight ((DerivedCategory.singleFunctor _ 0).obj L)).mapCone c)) :=
  ⟨fun K n _ ↦ isGE_rightDerivedFunctor_closedSupport_obj Λ i j hij K n,
    fun _ _ hc ↦ isHomotopyLimit_mapCone_rightDerivedFunctor_closedSupport Λ i j hij hc,
    fun K n _ ↦ isGE_upperStar_rightDerivedFunctor_closedSupport_obj Λ i j hij u K n,
    fun _ _ hc ↦ isHomotopyLimit_mapCone_rightDerivedFunctor_closedSupport_upperStar Λ i j hij u hc,
    fun K n _ ↦ isGE_tensorObj_singleFunctor_of_isLocallyFree Λ hL K n,
    fun _ _ hc ↦ isHomotopyLimit_mapCone_tensorRight_singleFunctor_of_isLocallyFree Λ hL hc⟩

end AlgebraicGeometry.ProEtale.CondensedRing
