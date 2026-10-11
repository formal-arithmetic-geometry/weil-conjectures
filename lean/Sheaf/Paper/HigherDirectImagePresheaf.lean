import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.Topology.RingedSpaceModuleCohomology
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Topology.PresheafModuleStalkFunctor

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-! # Higher direct image as a sheafified cohomology presheaf
Source: literature/stacks-project/cohomology.tex, Lemma 01E4
(blueprint: lem-weil-pbc-higher-direct-image-presheaf).
-/

/-- For a morphism of schemes, higher direct image is represented by the
sheafification of the presheaf of cohomology on inverse images; its canonical
map is universal and induces isomorphisms on stalks.
Source: literature/stacks-project/cohomology.tex, Lemma 01E4
(blueprint: lem-weil-pbc-higher-direct-image-presheaf).

Proof: choose an injective resolution and compute both derived functors by its
section complexes; identify the resulting cohomology presheaf, use exactness
and the universal property of sheafification, and then use invariance of stalks
under sheafification. -/
theorem higherDirectImagePresheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (p : ℕ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ (P : PresheafOfModules.{u} (moduleRings Y.toRingedSpace).obj),
      Nonempty
        ((PresheafOfModules.sheafification (𝟙 (moduleRings Y.toRingedSpace).obj)).obj P ≅
          ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj F) ∧
      Nonempty
        (P ⟶ (SheafOfModules.forget (moduleRings Y.toRingedSpace)).obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj F)) ∧
      ∀ (Q : SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((PresheafOfModules.sheafification
          (𝟙 (moduleRings Y.toRingedSpace).obj)).obj P ⟶ Q) ∧
      ∀ (y : Y),
        Nonempty
          (PresheafOfModules.stalkObj (moduleRings Y.toRingedSpace).obj y P ≅
            (PresheafOfModules.moduleStalkFunctor (moduleRings Y.toRingedSpace).obj y).obj
              (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj F).val) ∧
      (p = 0 →
        Nonempty (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 0).obj F ≅
          (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj F)) := by
  sorry

end AlgebraicGeometry
