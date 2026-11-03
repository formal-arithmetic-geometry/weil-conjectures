/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionRoosData
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Homology.TotalTensorSigns.TotalTensorHomotopyConeSigns
import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionKoszulDeltaRawAssembly

/-! # The strict Koszul/Roos comparison maps are isomorphisms

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 3.5.5 (comparison a)
(blueprint: lem-sp-perfect-reduction-koszul-delta-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
universe u v r wR wA
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone SheafOfModules.TotalTensorSigns
open scoped ChangeOfRings
namespace CategoryTheory.PerfectReductionRoos
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]
  [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]

/-- Every raw Koszul/Roos comparison map is an isomorphism (stated as an isomorphism whose
`hom` is the raw map). Source: Bhatt--Scholze, Lemma 3.5.5, comparison a.

Proof: the coordinate formulas of `KoszulDeltaRawData` determine `r.hom m P` (the summands
`ι` are jointly epimorphic, the product projections and biproduct projections jointly
monomorphic), so it suffices to show that the map they define is invertible degreewise.
Each term `K^p` of the two-term Koszul complex is the unit module, so `K^p ⊗ -` is
isomorphic to the identity by the right unitor and commutes with countable products; the
comparison `K^p ⊗ ∏_j X_j ⟶ ∏_j (K^p ⊗ X_j)` is therefore an isomorphism. In each degree the
map is a finite direct sum over `p ∈ {-1, 0}` of these comparisons on the shifted and
unshifted products, multiplied by the units `(-1)^p` and `1`; hence it is an isomorphism, and
the degreewise inverses form the inverse chain map.
(blueprint: lem-sp-perfect-reduction-koszul-delta-iso) -/
theorem nonempty_koszulDeltaIso
    (ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d)
    (r : KoszulDeltaRawData R t) :
    Nonempty (∀ m P, {e : ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
      roosF.obj (tensorTower R (principalKoszul R t m) P) //
      e.hom = r.hom m P}) := by
  classical
  have hcomp : ∀ m P n, IsIso ((r.hom m P).f n) :=
    koszulDeltaRaw_component_isIso R t r
  have hmap : ∀ m P, IsIso (r.hom m P) :=
    koszulDeltaRaw_isIso_of_components R t r hcomp
  refine ⟨fun m P ↦ ?_⟩
  letI := hmap m P
  exact ⟨asIso (r.hom m P), rfl⟩
end CategoryTheory.PerfectReductionRoos
