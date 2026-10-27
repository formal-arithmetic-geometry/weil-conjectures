module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization

/-! # Homotopical injectivity of sheaf dg modules

Source: Stacks Project, sdga.tex, definition-K-injective and Tag 0FSY,
with the signed left-module convention
(blueprint: def-sfb-sheaf-dg-homotopical-injectivity).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v w
open CategoryTheory
namespace CategoryTheory.SheafDg
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {S : Sheaf J CommRingCat.{w}}

/-- Acyclicity of global signed homogeneous Hom from every acyclic dg module:
every closed degree-r map is the differential of a degree-(r-1) signed map.
The existing Hom differential is d_I h - (-1)^r h d_M. The source acyclicity
is vanishing of all underlying cohomology sheaves, not sectionwise exactness.
Source: Stacks, sdga.tex, definition-K-injective and Tag 0FSY, with all shifts
(blueprint: def-sfb-sheaf-dg-homotopical-injectivity). -/
def IsHomotopicallyInjective (A : Algebra S) (I : LeftModule A) : Prop :=
  ∀ (M : LeftModule A), M.X.Acyclic → ∀ (r : ℤ) (f : GradedMap A M I r),
    CochainComplex.HomComplex.δ r (r + 1) f.val = 0 →
      ∃ g : GradedMap A M I (r - 1),
        CochainComplex.HomComplex.δ (r - 1) r g.val = f.val

end CategoryTheory.SheafDg
