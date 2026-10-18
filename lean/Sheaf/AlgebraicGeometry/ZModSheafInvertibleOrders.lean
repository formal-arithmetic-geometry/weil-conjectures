/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Point.Basic
import Sheaf.AlgebraicGeometry.PointedEtaleStalk

/-!
# Invertible orders of sheaves of Z/nZ-modules

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-zn-sheaf-invertible-orders.md` (blueprint: lem-kun-zn-sheaf-invertible-orders).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every sheaf of modules over the constant ring sheaf Z/nZ has orders invertible in K
when n is a positive integer invertible in K.

Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/`
`lem-kun-zn-sheaf-invertible-orders.md` (blueprint: lem-kun-zn-sheaf-invertible-orders).

Proof: the constant-presheaf-to-sheafification map gives, on every etale object U, a unital
ring homomorphism from Z/nZ to its constant ring sheaf's sections. Since n times 1 is zero
in Z/nZ, it is zero in these sections. The module axioms give n times every section of F
equal to zero (def-weil-pbc-constant-sheaf, def-weil-pbc-sheafification,
def-weil-sheaf-of-modules-category, def-weil-pbc-etale-sheaves).
The maps from sections into a geometric stalk are additive, hence commute with n-fold
addition. Multiplication by n and zero therefore agree after every colimit cocone map;
the colimit universal property makes them equal on the stalk
(def-weil-pbc-geometric-stalks). The positive integer n gives local torsion using the
identity covering and witnesses the allowed annihilator in every geometric stalk
(def-kun-torsion-invertible). The universe lift changes only the universe of the
coefficient ring. -/
theorem zmodSheaf_hasFieldInvertibleOrders (K : Type u) [Field K]
    (n : Etale.invertibleTorsionOrders K) (T : Over (Spec (.of K)))
    (F : SheafOfModules.{u + 1}
      ((constantSheaf T.left.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} (ZMod n.val))))) :
    Etale.IsTorsionOfInvertibleOrder K T ((SheafOfModules.toSheaf _).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
