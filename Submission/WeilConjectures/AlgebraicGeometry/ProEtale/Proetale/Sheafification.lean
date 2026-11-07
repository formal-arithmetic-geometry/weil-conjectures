/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The pro-étale site has sheafification

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

end AlgebraicGeometry.Scheme.ProEt
