module

public import Sheaf.CategoryTheory.SheafDgModuleLocalization
public import Sheaf.CategoryTheory.SmallSiteModuleSubsheafCodes

/-! # Actual subsheaves of left sheaf dg modules

Source: Stacks Project, sdga.tex, Tag 0FST, generated-submodule paragraph
(blueprint: def-sfb-sheaf-dg-submodule).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.SheafDg

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {S : Sheaf J CommRingCat.{u}} (A : Algebra S) (M : LeftModule A)

/-- An actual dg subsheaf: module-subsheaf codes in each degree, closed under the
inherited differential and every homogeneous left action. The codes already impose
restriction stability and the sheaf axiom, including the empty covering.
Source: Stacks, sdga.tex, Tag 0FST, generated-submodule paragraph
(blueprint: def-sfb-sheaf-dg-submodule). -/
structure Subsheaf where
  /-- The actual coefficient-module subsheaf in each degree. -/
  piece (q : ℤ) : SheafOfModules.ModuleSubsheafCode (M.X.X q)
  /-- Stability under the differential. -/
  d_mem (q : ℤ) (U : Cᵒᵖ) (x : (M.X.X q).val.obj U) :
    x ∈ (piece q).val U →
      (M.X.d q (q + 1)).val.app U x ∈ (piece (q + 1)).val U
  /-- Stability under the homogeneous algebra action. -/
  action_mem (p q : ℤ) (U : Cᵒᵖ) (a : (A.X.X p).val.obj U)
      (x : (M.X.X q).val.obj U) :
    x ∈ (piece q).val U → actionSection A M p q U a x ∈ (piece (p + q)).val U

variable {A M}

/-- Sectionwise inclusion of the actual dg subsheaves.
Source: Stacks, sdga.tex, Tag 0FST, smallest-submodule assertion
(blueprint: def-sfb-sheaf-dg-submodule). -/
def Subsheaf.IsContained (F G : Subsheaf A M) : Prop :=
  ∀ (q : ℤ) (U : Cᵒᵖ), (F.piece q).val U ⊆ (G.piece q).val U

/-- All sections of a dg subsheaf, with their object and degree labels.
This uses the actual subsets, so no choice of a representative sheaf is involved.
Source: Stacks, sdga.tex, Tag 0FST, definition of the size of a dg module
(blueprint: def-sfb-sheaf-dg-submodule). -/
def Subsheaf.sectionSet (F : Subsheaf A M) : Type u :=
  Σ U : Cᵒᵖ, Σ q : ℤ, {x : (M.X.X q).val.obj U // x ∈ (F.piece q).val U}

end CategoryTheory.SheafDg
