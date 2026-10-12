module

public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Sheaf.Topology.PresheafModuleStalkFunctor

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Stalks of the extension-by-zero sheaf vanish outside the open.
Source: Stacks Project, Sheaves, Lemma 00A7 (3).
(blueprint: new-extension-by-zero-outside-stalk)

The extension-by-zero presheaf has zero sections on every neighbourhood of a
point outside the open.  Passing to the filtered colimit defining the stalk,
and then through sheafification (which preserves stalks), gives the zero
module. -/
theorem module_extensionByZero_outside_stalk (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    ∀ (F : SheafOfModules.{u} (R.over U)) (x : X), x ∉ U →
      IsZero (TopCat.Presheaf.stalk (L.obj F).val.presheaf x) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
