import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # A locally injective map into a sheaf induces an injective map on sheafification

Source: literature/stacks-project/sites.tex, Theorem 00WB and Lemma 00WK,
with sites-modules.tex Lemma 03CY
(blueprint: lem-weil-pbc-site-module-sheafification-lift-injective).
-/

universe v u₁ v₁ u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A locally injective morphism from a presheaf of modules to a sheaf of modules
induces an injective morphism after sheafification.
Source: literature/stacks-project/sites.tex, Theorem 00WB and Lemma 00WK,
with sites-modules.tex Lemma 03CY
(blueprint: lem-weil-pbc-site-module-sheafification-lift-injective).
The proof uses the local-sections description of sheafification, refinement and
composition of coverings, compatibility of module sheafification with underlying
sheaves of sets, and separatedness of sheaves.
-/
lemma site_module_sheafification_lift_injective
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [HasWeakSheafify J AddCommGrpCat.{v}]
    {P : PresheafOfModules.{v} R.obj}
    {F : SheafOfModules.{v} R}
    (f : P ⟶ (SheafOfModules.forget R).obj F)
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map f)] :
    (∀ (X : Cᵒᵖ), Function.Injective (((SheafOfModules.toSheaf R).map
      ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f)).hom.app X)) ∧
      Mono ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm f) := by
  sorry

end CategoryTheory
