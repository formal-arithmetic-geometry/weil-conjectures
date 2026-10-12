module
public import Sheaf.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.AlgebraicTopology.SetCechNerveFreeResolution
@[expose] public section
universe u v w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Sheaf
/-- Kernel criterion for the presheaf Cech Ext edge map.
Source: the kernel step in Tag 079Z; this is the direct lifting argument reducing
edge injectivity to vanishing of a kernel class.
(blueprint: lem-sc-presheaf-cech-ext-edge-kernel) -/
theorem presheafCech_ext_edge_kernel
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (f : Arrow (Cᵒᵖ ⥤ Type v))
    (hf : Presheaf.IsLocallySurjective J f.hom) (q : ℕ) (hq : 0 < q)
    (hlower : ∀ (P : Cᵒᵖ ⥤ Type v) (b : ℕ), 0 < b → b < q →
      Subsingleton
        (Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F b))
    (hcech : IsZero ((presheafCechComplex f F.obj).homology q)) :
    ∀ (x : Ext ((presheafToSheaf J AddCommGrpCat).obj (f.right ⋙ AddCommGrpCat.free)) F q),
      (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
      (Functor.whiskerRight f.hom AddCommGrpCat.free))).comp x (Nat.zero_add q) = 0 → x = 0 := by
  sorry
end CategoryTheory.Sheaf
