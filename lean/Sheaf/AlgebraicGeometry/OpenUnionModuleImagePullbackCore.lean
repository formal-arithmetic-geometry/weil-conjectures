module

public import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisData
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Sheaf.AlgebraicGeometry.OpenModuleImageSectionRestriction

/-! Sectionwise gluing and its assembly for an arbitrary open union. -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Sectionwise amalgamation of direct-image restrictions.

Source: Stacks Project, Tags 01EB and 08BV.
(blueprint: lem-pc-open-union-module-image-pullback-core-sectionwise)
The two-open sheaf axiom, after the section-restriction comparison, gives the
existence and uniqueness of the amalgamated section at each test open. -/
theorem schemeOpenUnionModuleImage_sectionwise_gluing
    (X : Scheme.{u}) (U V : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    ∀ T : X.Opens,
      ∀ b : ((schemeOpenModuleImage X U).obj M).val.obj (.op T),
      ∀ c : ((schemeOpenModuleImage X V).obj M).val.obj (.op T),
      (((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M).val.app (.op T) b =
        ((schemeOpenModuleImageRestriction X
          (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M).val.app (.op T) c) →
      ∃! a : ((schemeOpenModuleImage X (U ⊔ V)).obj M).val.obj (.op T),
        ((schemeOpenModuleImageRestriction X
          (homOfLE (le_sup_left : U ≤ U ⊔ V))).app M).val.app (.op T) a = b ∧
        ((schemeOpenModuleImageRestriction X
          (homOfLE (le_sup_right : V ≤ U ⊔ V))).app M).val.app (.op T) a = c := by
  sorry

/-- Sectionwise amalgamations assemble into the categorical pullback.

Source: Stacks Project, Tags 01EB and 08BV.
(blueprint: lem-pc-open-union-module-image-pullback-core-assembly)
The sectionwise existence and uniqueness data is natural in the test open and
therefore assembles to a morphism of module sheaves.  Its two composites are
the prescribed restrictions, and sectionwise uniqueness gives the pullback
universal property. -/
theorem schemeOpenUnionModuleImage_isPullback_of_sectionwise
    (X : Scheme.{u}) (U V : X.Opens)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (h : ∀ T : X.Opens,
      ∀ b : ((schemeOpenModuleImage X U).obj M).val.obj (.op T),
      ∀ c : ((schemeOpenModuleImage X V).obj M).val.obj (.op T),
      (((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M).val.app (.op T) b =
        ((schemeOpenModuleImageRestriction X
          (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M).val.app (.op T) c) →
      ∃! a : ((schemeOpenModuleImage X (U ⊔ V)).obj M).val.obj (.op T),
        ((schemeOpenModuleImageRestriction X
          (homOfLE (le_sup_left : U ≤ U ⊔ V))).app M).val.app (.op T) a = b ∧
        ((schemeOpenModuleImageRestriction X
          (homOfLE (le_sup_right : V ≤ U ⊔ V))).app M).val.app (.op T) a = c) :
    IsPullback
      ((schemeOpenModuleImageRestriction X
        (homOfLE (le_sup_left : U ≤ U ⊔ V))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (le_sup_right : V ≤ U ⊔ V))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_left : U ⊓ V ≤ U))).app M)
      ((schemeOpenModuleImageRestriction X
        (homOfLE (inf_le_right : U ⊓ V ≤ V))).app M) := by
  sorry

end AlgebraicGeometry
