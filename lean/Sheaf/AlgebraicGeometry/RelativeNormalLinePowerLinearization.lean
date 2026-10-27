/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.EquivariantCoherentGZero
public import Sheaf.AlgebraicGeometry.RelativelyVeryAmple
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Positive-power linearization for a relative split-torus action

Source: Thomason, Equivariant resolution, linearization, and Hilbert's fourteenth
problem over arbitrary base schemes, Adv. Math. 65 (1987), proof of Theorem 3.3,
printed p.32, first paragraph; the split-torus proof in the DAG node.
(blueprint: lem-sfb-relative-normal-line-power-linearization)

The Laurent algebra is the existing group algebra on the free character lattice.
The descent equations use section-normalized tensor pullback. The forward
isomorphism is theta; its inverse has the existing groupoid descent convention.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.EquivariantCoherent

namespace AlgebraicGeometry

/-- A relatively very ample invertible module on a normal separated finite-type scheme
has a linearized positive tensor power for a split torus over a Noetherian affine base.
The model D presents the actual action groupoid: its group_coordinate field fixes
composition to (g,h,x) ↦ (gh,x). Its source and target laws fix the other coordinate.
The unit and cocycle are equalities of pulled-back sheaf maps, using the canonical
section-normalized tensor comparisons. Empty and disconnected X, a zero or nonreduced
base ring, and rank zero are included. No normality is imposed on the base.

Source: Thomason (1987), proof of Theorem 3.3, printed p.32, first paragraph;
the split-torus argument recorded in the DAG.
(blueprint: lem-sfb-relative-normal-line-power-linearization)

Proof plan:
1. The affine Noetherian base is locally Noetherian (pqf-def-locnoeth), and finite
   type implies locally finite type, so pqf-lem-locnoeth-lft makes X locally Noetherian.
   The Laurent basis and tensor universal property identify T ×_S X over each affine
   Spec R in X with Spec R[t_1^±1,...,t_r^±1], including its projection and unit section.
2. Pullback preserves the rank-one local frames (def-sc-invertible-module and
   def-pc-module-pullback). Apply lem-sfb-normal-laurent-line-invariance to a^*L.
   The action unit and pullback composition identify e^*a^*L with L, giving
   theta_0 : p_2^*L ≅ a^*L.
3. In a rank-one frame an automorphism is multiplication by a unique unit. Frame
   changes preserve the scalar, so these units glue. For alpha = e^*theta_0 replace
   theta_0 by theta_0 composed with p_2^*(alpha inverse). Its unit restriction is 1.
4. On T ×_S T ×_S X, associativity identifies the sources and targets of the two
   cocycle maps. Their ratio is a global unit d, and normalization gives
   d(1,h,x) = d(g,1,x) = 1 as identities of regular functions on the two faces.
5. At x in X the local ring R is a domain. Write d and its inverse as finite
   Laurent polynomials in g,h over R. Order the exponent lattice lexicographically.
   The least and greatest exponents of a product are the sums of the corresponding
   extrema: their coefficients are products of nonzero coefficients, with no other
   pair contributing. The widths of inverse polynomials are nonnegative and sum to
   zero, so each support is a singleton. Thus d = c g^u h^v. Its two face identities
   force c = 1 and u = v = 0 by uniqueness of Laurent coefficients. On an affine
   open of X every coefficient of d-1 therefore has zero germ at every point and
   vanishes by the sheaf axiom. Hence d = 1 globally and the cocycle holds. This
   linearizes L itself, so m = 1 witnesses the positive-power assertion using
   def-pur-sheaf-tensor-product. The same calculation includes rank zero; disconnected
   X is treated locally, and the empty scheme has unique sheaf maps.
-/
theorem exists_relative_normal_line_tensorPow_linearization
    (A : Type u) [CommRing A] [IsNoetherianRing A] (r : ℕ)
    (X : Over (Spec (.of A)))
    [ModObj (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (hnormal : ∀ x : X.left, IsDomain (X.left.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.left.presheaf.stalk x))
    (L : X.left.Modules) [L.IsInvertible]
    (hL : Scheme.Modules.IsRelativelyVeryAmple X.hom L) :
    ∃ m : ℕ, 1 ≤ m ∧
      ∃ D : ActionGroupoidModel (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X,
        ∃ theta :
          (Scheme.groupoidModulePullback
            (source (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X)).obj
              (L.tensorPow m) ≅
          (Scheme.groupoidModulePullback
            (target (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X)).obj
              (L.tensorPow m),
          Scheme.groupoidModuleUnitLaw
            (source (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X)
            (target (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X)
            (identityArrow (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X)
            D.laws.source_id D.laws.target_id (L.tensorPow m) theta.symm ∧
          Scheme.groupoidModuleCocycleLaw
            (source (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X)
            (target (ringDiagonalizableGroup A (ULift.{u} (Fin r → ℤ))).X X)
            D.comp D.laws.source_comp D.laws.target_comp (L.tensorPow m) theta.symm := by
  sorry

end AlgebraicGeometry
