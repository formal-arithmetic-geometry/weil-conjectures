/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# The small étale site is essentially small

For a scheme `X : Scheme.{u}`, the category `X.Etale` has objects in `Type (u + 1)` and morphisms
in `Type u`, so it is essentially small with respect to `u + 1`. Instance search does not derive
this from `locallySmall_of_univLE` and `essentiallySmall_of_small_of_locallySmall`, since it
cannot solve the universe constraint `UnivLE.{u, u + 1}`; these instances supply it directly.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Etale

instance locallySmall (X : Scheme.{u}) : LocallySmall.{u + 1} X.Etale :=
  @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)

instance essentiallySmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  essentiallySmall_of_small_of_locallySmall _

end AlgebraicGeometry.Scheme.Etale
