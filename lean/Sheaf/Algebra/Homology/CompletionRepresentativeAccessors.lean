/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchange
/-! # Named projections of normalized completion representatives
These are the existing subtype projections, with their concrete output types recorded once.
-/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v r wR wS
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.PrincipalQuotientCompletion
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
  [HasDerivedCategory.{wR}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
attribute [local irreducible] quotientTower roosF SheafOfModules.monoidalCategory

/-- The underlying actual Roos comparison of the existing subtype.
Source: the definition of RepresentativeComparison, Stacks 0941
(blueprint: def-pur-completion-representative-accessors). -/
def RepresentativeComparison.val
    {F : SheafOfModules.DerivedChangeOfRingsCochainModel φ}
    {t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections}
    {vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections}
    {e : ℕ} {CR : Model R t} {CS : Model S vS}
    {ε : CR.completion ⋙ F.T ≅ F.T ⋙ CS.completion}
    {P : CochainComplex
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ}
    (d : RepresentativeComparison F t vS e CR CS ε P) :
    RepresentativeRoosComparison F.E (sourceTower t P) (targetTower F vS P) e :=
  Subtype.val d

/-- The original quotient and counit equations, with no additional hypothesis.
Source: the definition of RepresentativeComparison, Stacks 06YT and 0941
(blueprint: def-pur-completion-representative-accessors). -/
theorem RepresentativeComparison.property
    {F : SheafOfModules.DerivedChangeOfRingsCochainModel φ}
    {t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections}
    {vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections}
    {e : ℕ} {CR : Model R t} {CS : Model S vS}
    {ε : CR.completion ⋙ F.T ≅ F.T ⋙ CS.completion}
    {P : CochainComplex
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ}
    (d : RepresentativeComparison F t vS e CR CS ε P) :
    (∀ n : ℕ,
    (extendedComplex F).map (quotientMap R t P n) ≫
        d.val.β.hom.app (op n) =
      quotientMap S vS ((extendedComplex F).obj P) (e * (n + 1) - 1)) ∧
    ε.hom.app (DerivedCategory.Q.obj P) ≫
      CS.completion.map (F.ε.app P) ≫ CS.counit.app ((extendedComplex F).obj P) ≫
        DerivedCategory.Q.map d.val.a =
      F.T.map (CR.counit.app P) ≫ F.ε.app (roosF.obj (sourceTower t P)) ≫
        DerivedCategory.Q.map d.val.δ.hom := by
  exact Subtype.property d

end CategoryTheory.PrincipalQuotientCompletion
