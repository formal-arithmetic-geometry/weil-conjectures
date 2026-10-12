/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-! # The shifted determinant of the dual evaluates against the determinant

Source: Stacks Project, Tag 0BRT, determinant inversion in the conclusion of the proof.
(blueprint: lem-sc-shifted-determinant-dual-evaluation).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The shifted top exterior powers of a finite locally free sheaf and its dual are
mutually inverse derived tensor objects.
Source: Stacks Project, Tag 0BRT, final determinant inversion.
(blueprint: lem-sc-shifted-determinant-dual-evaluation).

Proof: on an open cover trivializing M as O_X^d, use a basis e₁,...,e_d and its dual.
The determinant evaluation pairs their top wedges to 1 and is therefore an isomorphism
from wedge^d M^dual tensor wedge^d M to O_X on that cover. A basis change multiplies
the two determinant generators by inverse determinants, so this evaluation is
independent of the chosen bases and glues. Sectionwise exterior powers sheafify to
these local determinant lines, and internal Hom restricts to the dual free module.
Both determinant lines are locally free of rank one, hence flat, so their ordinary
product computes their derived tensor product. The single functor in degree zero
therefore carries the evaluation to an isomorphism with the derived unit. Compatibility
of derived tensor with shifts identifies the displayed product with that unshifted
product shifted by -d+d=0. Compose with the zero-shift isomorphism. When d=0 the empty
wedge is the structure sheaf and the evaluation is multiplication; the same argument
works on an empty scheme as well. -/
theorem shiftedDeterminant_dual_evaluation
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : X.Modules) (d : ℕ) (hfree : M.IsFiniteLocallyFreeOfRank d) :
    Nonempty ((((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
        (Scheme.Modules.exteriorSheaf
          (SheafOfModules.homObj (R := X.sheaf) M
            (SheafOfModules.unit X.ringCatSheaf)) d))⟦-(d : ℤ)⟧ ⊗
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (Scheme.Modules.exteriorSheaf M d))⟦(d : ℤ)⟧) ≅
      𝟙_ (schemeDerivedCategory X)) := by sorry

end AlgebraicGeometry
