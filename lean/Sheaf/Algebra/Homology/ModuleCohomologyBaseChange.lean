/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Algebra.Homology.RingTensorCohomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Cohomology base change for module complexes

Source: Stacks Project, More on Algebra, Tag 0A1U, Lemma better-cut-complex-in-two
(blueprint: def-pc-module-cohomology-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace ModuleCat

/-- The canonical map `B ⊗ Hⁱ(K) → Hⁱ(B ⊗ K)` is the adjoint of cohomology of the
extension-restriction unit. Restriction is exact, so its homology comparison is invertible.
For a bounded-above free complex the target computes derived tensor cohomology.
Source: Stacks Project, More on Algebra, Tag 0A1U
(blueprint: def-pc-module-cohomology-base-change). -/
noncomputable def cohomologyBaseChange {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (extendScalars (algebraMap R B)).obj (K.homology i) ⟶
      ((RingTensorCohomology.extend R B).obj K).homology i :=
  ((extendRestrictScalarsAdj (algebraMap R B)).homEquiv _ _).symm
    (ShortComplex.homologyMap
        ((K.sc i).mapNatTrans (extendRestrictScalarsAdj (algebraMap R B)).unit) ≫
      (((K.sc i).map (extendScalars (algebraMap R B))).mapHomologyIso
        (restrictScalars (algebraMap R B))).hom)

end ModuleCat
