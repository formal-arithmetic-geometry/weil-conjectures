/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.AlgebraicGeometry.FiniteLocalCyclicModuleForget
import Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison

/-! # Prime-field coefficients on a prime-annihilated constructible sheaf

Source: Stacks Project, Theorem 03SC, second proof paragraph.
(blueprint: lem-pbc-prime-coefficient-constructibility-transfer)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A prime-field module sheaf with the same underlying abelian sheaf as a
constructible sheaf over finite coefficients is constructible.
Source: Stacks Project, Theorem 03SC, second proof paragraph; Definition 03RW.
(blueprint: lem-pbc-prime-coefficient-constructibility-transfer)

Proof: Choose a finite constructible stratification for F and finite locally constant
module trivializations on each stratum. Forgetting coefficients commutes with inverse
image and restriction and sends each constant finite module value to its constant
abelian group. The given abelian sheaf isomorphism therefore gives local constant
finite abelian values for G on the same strata. Discard empty members of the covers.
On every remaining member, such a constant value is a geometric stalk. It is killed
by r, since G is a sheaf of prime-field modules. Equip this finite group with its
canonical ZMod r action, lifted to ULift (ZMod r). Every additive map between groups
killed by r commutes with that action: choose an integer representative of the scalar
and use preservation of repeated addition. Thus each abelian trivialization uniquely
lifts to a module trivialization of G. The finite values are finitely generated over
the prime field, so G is finite locally constant on every stratum. This witnesses
constructibility in the recorded module-sheaf sense. Empty strata need no nonempty
cover members; the zero sheaf and the zero coefficient ring cause no exception. -/
theorem isConstructibleSheaf_prime_of_underlyingAbelianIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (r : ℕ) [Fact r.Prime]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (e : (sheafCompose _ (forget₂
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})).obj G ≅
        (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) :
    IsConstructibleSheaf G := by sorry

end AlgebraicGeometry.Scheme
