/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionKoszulDeltaRawComponents

/-! Assembly of componentwise isomorphisms into a chain-map isomorphism.

Source: Mathlib's homological-complex componentwise isomorphism criterion together with the
finite signed Koszul/Roos inverse construction
(blueprint: new-lem-sp-perfect-reduction-koszul-raw-assembly).
The component inverses obtained from the preceding finite calculation satisfy the chain-map
equations because the raw coordinate formulas include the totalization signs; assembling them
degreewise yields an inverse chain map.
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

/-- Componentwise invertibility of a raw comparison assembles to invertibility of its chain map.
Source: the homological-complex componentwise isomorphism criterion and the signed inverse
calculation of Bhatt--Scholze Lemma 3.5.5
(blueprint: new-lem-sp-perfect-reduction-koszul-raw-assembly).
The supplied component inverses are assembled degreewise; the shifted and unshifted equations
make the resulting degreewise inverse commute with the differential.
-/
theorem koszulDeltaRaw_isIso_of_components
    (r : KoszulDeltaRawData R t)
    (h : ∀ m P n, IsIso ((r.hom m P).f n)) :
    ∀ m P, IsIso (r.hom m P) := by
  intro m P
  let (n : ℤ) := h m P n
  exact HomologicalComplex.Hom.isIso_of_components (r.hom m P)

end CategoryTheory.PerfectReductionRoos
