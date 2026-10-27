/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Sheafification for constant-size commring coefficients -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- Ring-valued presheaves on the pro-etale site admit sheafification at the
coefficient universe. This specialized instance avoids repeated generic searches.
Source: Mathlib Sites.LeftExact, concrete plus-plus sheafification; Stacks 00W1
(blueprint: lem-coef-proetale-commring-sheafification).
Proof: the site's cover types are small in u+1. The forgetful functor on rings
preserves the required limits and filtered colimits and reflects isomorphisms.
The concrete plus-plus construction therefore gives left-exact sheafification.
Its adjunction proves that the inclusion of sheaves has a left adjoint. -/
@[instance 2000] theorem proetaleCommRingSheafification (W : AlgebraicGeometry.Scheme.{u}) :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) CommRingCat.{u + 1} := by
  infer_instance

end AlgebraicGeometry.ProEtale
