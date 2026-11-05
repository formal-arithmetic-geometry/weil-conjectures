/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.SiteExtensionByZeroExact

/-!
# Exactness of extension by zero on the small Zariski site

Source: Stacks Project, Modules on Sites, Lemma 03DJ
(blueprint: lem-weil-pbc-zariski-extension-by-zero-exact).

`U_Zar` is the localized site `(Opens.grothendieckTopology X).over U` (the opens `W ⊆ U`,
with the coverings of `X_Zar`), and extension by zero `j_! : Ab(U_Zar) ⥤ Ab(X_Zar)` is
`sheafToPresheaf ⋙ (Over.forget U).op.lan ⋙ presheafToSheaf`
(`Functor.sheafPullbackConstruction.sheafPullback`): the left Kan extension of `F` along
the inclusion is the presheaf `j_{p!} F` (`F(V)` for `V ⊆ U`, the empty colimit `0`
otherwise), followed by sheafification on `X_Zar`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

end AlgebraicGeometry
