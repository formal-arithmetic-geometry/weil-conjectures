/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Chosen pullbacks of preimages of an open cover

Let `U a` be a family of opens of a scheme `S` and `g : Z ⟶ S` a morphism. The intersections
`g⁻¹ (U a ⊓ U b)` and `g⁻¹ (U a ⊓ U b ⊓ U c)` are chosen (wide) pullbacks of the open immersions
of the `g⁻¹ U a` (`AlgebraicGeometry.Scheme.Modules.preimageChosenPullback`,
`AlgebraicGeometry.Scheme.Modules.preimageChosenPullback₃`), with diagonals
`AlgebraicGeometry.Scheme.Modules.preimageDiag`. A morphism `h : Z' ⟶ Z` over `S` restricts to
morphisms between these preimages (`AlgebraicGeometry.Scheme.Modules.resTo`), compatibly with the
projections.

This is the input for gluing modules along the open cover `g⁻¹ U a` of `Z` with
`CategoryTheory.Pseudofunctor.DescentData'.ofGlue`, and for pulling gluing morphisms back along
morphisms between stages of a cofiltered system of schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pseudofunctor LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

section Res

variable {S T Z Z' : Scheme.{u}} {G : T ⟶ S} {g : Z ⟶ S}

end Res

section ChosenPullback

variable {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens) {Z : Scheme.{u}} (g : Z ⟶ S)

variable (a b c : ι)

end ChosenPullback

section ResTo

/-! ### Restrictions of a morphism over `S` to the chosen pullbacks -/

variable {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens) {Z Z' : Scheme.{u}} {g : Z ⟶ S}
  {g' : Z' ⟶ S} (h : Z' ⟶ Z) (hg : h ≫ g = g') (a b c : ι)

end ResTo

end AlgebraicGeometry.Scheme.Modules
