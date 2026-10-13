/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Local chain models for the lowest truncation arrow

Source: Stacks Project, Tags 0BDL, 0BCD, 0EWY and 08CR.
(blueprint: lem-sc-perfect-universal-h0-local-chain-model).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The specified truncation arrow admits a finite-free local chain representative
with no negative terms, zero outgoing differential in degree zero, and invertible
component in degree zero.

Source: Stacks Project, Tag 0BDL, matrix-chart argument; Tags 0BCD, 0EWY, 08CR.
(blueprint: lem-sc-perfect-universal-h0-local-chain-model).

Proof: At s choose the universal rank-r neighbourhood and test its condition on
Spec kappa(s). Use the finite-free residue model of 0BCD and shrink its affine
neighbourhood into that neighbourhood. Negative fibre cohomology vanishes, so
all negative terms of the residue model vanish; the first term has rank r.
The identity test gives a rank-r locally free kernel of its first differential.
Shrink again to trivialize the kernel. Its inclusion into the first term is an
injective square matrix. The transpose is injective by 0EWY, equivalently the
dual of the cokernel vanishes. Each coordinate of the outgoing differential
factors through that cokernel, hence is zero. This argument does not require a
reduced base. The isomorphism H0(a) identifies M locally with that kernel, so
M is finite free on a further affine neighbourhood. Represent M[0] by its
single finite-free complex A and K by the model B. The affine perfect map
representative theorem (08CR) represents the conjugate of the restricted a by
an actual chain map alpha. Since both incoming and outgoing differentials at
zero vanish, H0(alpha) is alpha.f 0, so the latter is invertible. The chosen
object identifications give the stated square in the derived category.
For rank zero these are zero first terms; an empty scheme has no points. -/
theorem perfect_universalH0_local_chain_model
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (K : schemeDerivedCategory S) (hK : IsPerfect S K)
    (hnegative : ∀ (Y : Scheme.{u}) (k : Y ⟶ S) (i : ℤ), i < 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
          ((derivedPullback k).obj K)))
    (hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ,
      ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback (k ≫ U.ι)).obj K)) r)
    (M : S.Modules)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M ⟶ K)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a))
    (s : S) :
    ∃ U : S.Opens, s ∈ U ∧
      ∃ A B : CochainComplex
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ,
        IsStrictlyPerfect S U A ∧ IsStrictlyPerfect S U B ∧
        (∀ i : ℤ, i ≠ 0 → IsZero (A.X i)) ∧
        (∀ i : ℤ, i < 0 → IsZero (B.X i)) ∧ B.d 0 1 = 0 ∧
        ∃ α : A ⟶ B, IsIso (α.f 0) ∧
          ∃ (eA : (SheafOfModules.overFunctor.{u}
                (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M) ≅
                DerivedCategory.Q.obj A)
            (eB : (SheafOfModules.overFunctor.{u}
                (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
                DerivedCategory.Q.obj B),
            (SheafOfModules.overFunctor.{u}
              (moduleRings S.toRingedSpace) U).mapDerivedCategory.map a ≫ eB.hom =
                eA.hom ≫ DerivedCategory.Q.map α := by sorry

end AlgebraicGeometry.Scheme
