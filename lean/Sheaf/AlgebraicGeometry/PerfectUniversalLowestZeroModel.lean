/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.PerfectJumpLoci
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Sheaf.AlgebraicGeometry.TorAmplitudeOpenLocal
import Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion
import Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology

/-! # Zero bottom differential on a universally free locus
Source: Stacks Project, Tags 0BDL, 0BCD and 0EWY.
(blueprint: lem-sc-perfect-universal-lowest-zero-model). -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

/-- Universal rank freeness forces a local finite-free model with zero bottom differential.
Source: Stacks Project, Tag 0BDL, matrix-chart proof; Tags 0BCD and 0EWY.
(blueprint: lem-sc-perfect-universal-lowest-zero-model).

Proof:
1. For t in T, test hfree on Spec kappa(t) -> T. The bottom fibre dimension is r.
   The fibre dimension base-change formula identifies this with the dimension at h(t).
   Tor amplitude implies that the derived fibre at h(t) has no cohomology below a.
   Choose the residue model at h(t) by 0BCD. Its terms below a are zero, its a-th
   term has rank r, and it is bounded above and finite free in every degree.
2. Shrink an affine neighbourhood of t into the inverse image of this chart. Termwise
   tensor pullback represents Lh*E there by 06YD/06YJ and derived composition.
   Tensor pullback preserves finite free terms, zero terms and the upper bound.
3. On this chart the kernel of d^a is H^a(Lh*E), finite locally free of rank r by
   hfree with the identity. Shrink again to trivialize it. Its inclusion into K^a
   is an injective square map between free rank-r modules. By 0EWY its cokernel
   has zero dual. Each coordinate of d^a factors through that cokernel, hence is
   zero. Thus d^a is zero on this neighbourhood. The derived identifications are
   obtained from the termwise counits and compose to the displayed isomorphism.
   When r=0 the first term is zero. For the empty T the assertion is vacuous.
   This is a structural assertion about models; it asserts no cohomology comparison. -/
theorem perfectUniversalLowest_zero_model
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S) (hE : IsPerfect S E) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes S E F i)
    (r : ℕ)
    (T : Scheme.{u}) (h : T ⟶ S)
    (hfree :
      ∀ (T' : Scheme.{u}) (u' : T' ⟶ T),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
              ((derivedPullback (u' ≫ h)).obj E)) r)
 :
    ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      ∃ K : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ,
        (∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (K.X i)) ∧ K.d a (a + 1) = 0 ∧
        (∀ i : ℤ, ∃ n : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin n)))) ∧
        Nonempty ((derivedPullback U.ι).obj ((derivedPullback h).obj E) ≅
          DerivedCategory.Q.obj K) := by sorry

end AlgebraicGeometry.Scheme
