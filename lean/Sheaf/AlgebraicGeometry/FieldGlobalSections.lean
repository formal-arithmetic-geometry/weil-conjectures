module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-! # Global sections over a base field

Source: Stacks Project, Varieties, Tag 08A7, the vector spaces of global sections
in the multiplication map; the scalar action is induced by the structure morphism.
(blueprint: def-sfb-field-global-sections)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProjectiveSpace

/-- Global sections as a vector space over the specified base field, by restriction of
scalars along the structure morphism.
Source: Stacks Project, Varieties, Tag 08A7
(blueprint: def-sfb-field-global-sections). -/
def fieldSections (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (F : X.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := X))).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj F)

end AlgebraicGeometry.ProjectiveSpace
