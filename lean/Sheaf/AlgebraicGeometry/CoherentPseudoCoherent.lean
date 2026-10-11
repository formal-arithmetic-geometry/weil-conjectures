/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Coherent modules are pseudo-coherent on Noetherian schemes

Source: Stacks Project, Derived Categories of Schemes, Tag 08E8,
`lemma-identify-pseudo-coherent-noetherian` (blueprint: lem-sc-coherent-pseudo-coherent).
-/

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A coherent module on a Noetherian scheme, regarded as a complex concentrated in degree
zero, is pseudo-coherent. Source: Stacks Project, Tag 08E8,
`lemma-identify-pseudo-coherent-noetherian` (blueprint: lem-sc-coherent-pseudo-coherent).

Proof: At each point of `Y`, `lem-sc-coherent-affine-free-resolution` gives an affine
neighbourhood and a bounded-above complex of finite-rank free modules quasi-isomorphic to
`F` restricted to that neighbourhood, concentrated in degree zero. Its image in the derived
category is therefore isomorphic to the restriction of `F[0]`. These local resolutions give
exactly the condition of `def-pur-pseudo-coherent-complex` at every point, hence the result. -/
theorem isPseudoCoherent_singleFunctor_obj_of_isCoherent (Y : Scheme.{u}) [IsNoetherian Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (F : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hF : RingedSpace.IsCoherent Y.toRingedSpace F) :
    Y.IsPseudoCoherent
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
