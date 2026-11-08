/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.CommSq

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The free abelian presentation of a torsor extension

Source: Stacks Project, Lemma 02FQ, first construction.
(blueprint: lem-sc-zariski-torsor-free-extension-short-exact)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace CategoryTheory.Sheaf.Torsor

set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u})
variable {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (T : Torsor G)

namespace FreeExtension

/-- The free abelian sheaf on the sections of the torsor. -/
noncomputable abbrev freeSheaf :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (T.sheaf.obj ⋙ AddCommGrpCat.free)

/-- The free abelian sheaf on pairs of sections. -/
noncomputable abbrev relations :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (T.pairs ⋙ AddCommGrpCat.free)

/-- The relation sending `(x,y)` to `[y]-[x]`. -/
noncomputable abbrev difference : relations X T ⟶ freeSheaf X T :=
  (presheafToSheaf _ _).map T.pairsDiff

/-- The relation sending `(x,y)` to the unique `g` with `g +ᵥ x = y`. -/
noncomputable def displacement : relations X T ⟶ G :=
  ⟨sheafifyLift _ T.pairsSub G.property⟩

/-- The quotient of `G ⊕ ℤ[T]` by `[y]-[x] = y-x`, formed as a pushout. -/
noncomputable abbrev extension := pushout (difference X T) (displacement X T)

/-- The map of the free generators to the presented extension. -/
noncomputable abbrev generators : freeSheaf X T ⟶ extension X T :=
  pushout.inl (difference X T) (displacement X T)

/-- The constant integer presheaf, in the coefficient universe of the torsor. -/
abbrev integers : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u, 0} ℤ))

/-- A local section of the torsor gives a degree-one section of the extension. -/
noncomputable def generator (U : (Opens X)ᵒᵖ) (t : T.sheaf.obj.obj U) :
    (extension X T).obj.obj U :=
  (generators X T).hom.app U
    ((toSheafify (Opens.grothendieckTopology X)
      (T.sheaf.obj ⋙ AddCommGrpCat.free)).app U (FreeAbelianGroup.of t))

end FreeExtension
end CategoryTheory.Sheaf.Torsor
