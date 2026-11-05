/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitConstructible

/-!
# Dévissage of constructible sheaves to extensions by zero of lisse sheaves

Let `Λ` be a commutative condensed ring such that `Λ_X` is flat on every scheme `X`, and `T` a
scheme with noetherian underlying space. Let `P` be a class of objects of `D(T, Λ)` closed under
isomorphisms and extensions in distinguished triangles, containing the complexes
`Rc_* j_! Rc'_* L` for `c : D ⟶ T` a closed immersion, `j : V ⟶ D` the inclusion of an open
subscheme, `c' : E ⟶ V` a closed immersion and `L` a locally finitely presented (lisse)
`Λ_E`-module placed in degree `0`. Then `P` contains every constructible `Λ_T`-module placed in
degree `0` (`ProEtale.CondensedRing.prop_singleFunctor_of_isConstructibleModuleObject`).

This is the noetherian induction of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitConstructible`, for
a general class `P`: a constructible sheaf `G` on a closed subscheme `c : D ⟶ T` is split, along a
nonempty open `V` of `D` contained in a stratum, by the open–closed triangle
`j_! Lj^* G ⟶ G ⟶ Ri_* Li^* G ⟶` into the extension by zero of a lisse sheaf and a sheaf
supported on a smaller closed subset.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
