/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-!
# The pro-étale site has sheafification

The small pro-étale site of a scheme `S : Scheme.{u}` has sheafification for `Type (u + 1)`- and
`Ab.{u + 1}`-valued presheaves, and its category of sheaves of sets is a Grothendieck topos
(`AlgebraicGeometry.Scheme.ProEt.isGrothendieckTopos_sheaf`): it is presented by the small site
`AsSmall S.ProEt`, whose objects and morphisms lie in `Type (u + 1)`.
-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme.ProEt

/-- The pro-étale site on `S : Scheme.{u}` has sheafification for `Type (u + 1)`-valued sheafs. -/
instance (S : Scheme.{u}) : HasSheafify (ProEt.topology S) (Type (u + 1)) :=
  inferInstance

/-- The pro-étale site on `S : Scheme.{u}` has sheafification for `Ab.{u + 1}`-valued sheafs. -/
instance (S : Scheme.{u}) : HasSheafify (ProEt.topology S) Ab.{u + 1} :=
  inferInstance

/-- The category of sheaves of sets on the small pro-étale site of a scheme `S` is a Grothendieck
topos relative to the universe `u + 1`: it is equivalent to the sheaves on the small site
`AsSmall S.ProEt`, whose objects and morphisms lie in `Type (u + 1)`, for the topology induced
along the equivalence `AsSmall.down`. -/
theorem isGrothendieckTopos_sheaf (S : Scheme.{u}) :
    IsGrothendieckTopos.{u + 1} (Sheaf (ProEt.topology S) (Type (u + 1))) := by
  let e : S.ProEt ≌ AsSmall.{u + 1} S.ProEt := AsSmall.equiv
  let K : GrothendieckTopology (AsSmall.{u + 1} S.ProEt) :=
    e.inverse.inducedTopology (ProEt.topology S)
  have : e.inverse.IsDenseSubsite K (ProEt.topology S) := inferInstance
  exact ⟨AsSmall.{u + 1} S.ProEt, inferInstance, K,
    ⟨e.sheafCongr (ProEt.topology S) K (Type (u + 1))⟩⟩

end AlgebraicGeometry.Scheme.ProEt
