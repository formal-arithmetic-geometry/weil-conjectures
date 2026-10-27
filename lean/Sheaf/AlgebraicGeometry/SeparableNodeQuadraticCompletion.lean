/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.JacobsonSpace
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.ZetaSeries
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.TensorProduct
import Sheaf.RingTheory.GeometricFieldStalkDescent
import Sheaf.RingTheory.PresentationFittingIdeal
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation
import Sheaf.TraceFormula.FormalJacobianQuadraticCriterion
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.ClosedPointDimensionLocalRing
import WeilConjectures.RingTheory.Depth
import WeilConjectures.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete

/-! # Quadratic completion at a node with finite separable residue field

Source: Stacks Project, curves.tex, Tags 0C4D (lemma-nodal), (3) implies (2), and
0C49 (lemma-nodal-algebraic), condition (3) and its coefficient-field construction
(blueprint: lem-sfb-separable-node-quadratic-completion).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A geometric node with finite separable residue field has a reduced, Noetherian,
one-dimensional local ring, essentially of finite type over the ground field, and a
nondegenerate binary quadratic completed equation over its own residue field.

The section is expressed as a ring map with the explicit ground-field compatibility
and residue-section equations. It equips the completion with the residue-field algebra
structure used in `e`. The topologies in the continuity assertion are the extended
maximal-ideal-adic topology on the completion and the quotient of the variable-adic
topology on the power series ring. The last equation says that the isomorphism induces
the identity of the residue field, using constant coefficient on the quadratic quotient.

Source: Stacks Project, curves.tex, Tags 0C4D (lemma-nodal), (3) implies (2), and
0C49 (lemma-nodal-algebraic), condition (3), with the coefficient section of Tag 0C34
(blueprint: lem-sfb-separable-node-quadratic-completion).

Proof:
1. Choose an affine neighbourhood U = Spec S of x. The locally finite type affine-pairs
   criterion makes S finite type over k. The affine-open stalk-localization theorem
   identifies A with S_p at the maximal ideal p of x. This proves essential finite type.
   The open fibre-product and affine fibre-product theorems identify U over the algebraic
   closure K with Spec (S tensor_k K); its stalk at xbar is (S tensor_k K)_q, denoted B.
2. Geometric-field-stalk descent identifies q as the kernel of evaluation to K through
   an embedding of kappa into K. Separable-closed-point formal presentation gives A,
   its completion, and B Noetherian local, a faithfully flat local map A to B with
   m B = n, closed fibre K, and a k-algebra residue section sigma into the completion.
   Apply it again to S tensor_k K at q to present the completion of B over K.
3. Equidimensional-open local dimension gives dimension one at the closed point.
   Dimension-at-point open-subspace invariance and closed-point local-ring dimension
   identify this dimension with ringKrullDim A.
4. The differentials of finite algebra generators generate the differential modules.
   Differential localization and base change identify Omega_{B/K} with Omega_{A/k}
   tensor_A B. Independence and base change for first Fitting ideals give J_B = J_A B.
5. The formal-presentation theorem identifies completed differentials with the Jacobian
   cokernel. The assumed ring isomorphism to K[[u,v]]/(uv) satisfies condition (c) of
   the formal Jacobian quadratic criterion with a = c = 0, b = 1. Thus completed B has
   depth one and Jacobian-minor ideal its maximal ideal. Fitting presentation
   independence identifies this ideal with J_B times completed B: multilinearity of
   minors compares the finite relation rows with every row in the kernel.
6. Completion of the Noetherian local ring B is faithfully flat. Faithfully-flat ideal
   contraction gives J_B = n. Contracting again along A to B gives J_A = m.
7. Local completion is flat. The flat local depth formula for B to completed B, A to B,
   and A to completed A has respective closed fibres K, K, kappa. These fields have
   depth zero, so completed B of depth one implies completed A of depth one.
8. In the presentation of completed A over kappa, the Jacobian-minor ideal is m times
   completed A by Fitting base change. Condition (a) implies (b) of the formal Jacobian
   quadratic criterion now gives a,b,c, nonzero discriminant, and the kappa-algebra
   isomorphism for the coefficient section sigma. Constants exhaust the residue field,
   so the residue map is the identity. An isomorphism of these local rings preserves
   their maximal ideals and every power, proving the stated continuity.
9. The map K[[u,v]] to K[[u]] times K[[v]], obtained by setting respectively v and u
   equal to zero, has kernel (uv): its nonzero coefficients must involve both variables.
   The one-variable power series rings are domains by power-series field regularity,
   so the split quadratic quotient and completed B are reduced. Faithfully-flat ideal
   contraction at zero makes A to B to completed B injective, hence A is reduced. -/
theorem separable_node_quadratic_completion
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hdim : C.IsPureDimension 1)
    (x : C) (hx : x ∈ closedPoints C)
    (hfinite : @FiniteDimensional k (C.residueField x) inferInstance inferInstance
      (f.residueFieldAlgebraMap x).toAlgebra.toModule)
    (hsep : @Algebra.IsSeparable k (C.residueField x) inferInstance inferInstance
      (f.residueFieldAlgebraMap x).toAlgebra)
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    (xbar : pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hxbar : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) xbar = x)
    (hgeom : Nonempty
      (AdicCompletion
        (IsLocalRing.maximalIdeal
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk xbar))
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf.stalk xbar)
        ≃+* (MvPowerSeries (Fin 2) K ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) * MvPowerSeries.X 1}))) :
    IsReduced (C.presheaf.stalk x) ∧ IsNoetherianRing (C.presheaf.stalk x) ∧
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.presheaf.Γgerm x).hom).EssFiniteType ∧
      ringKrullDim (C.presheaf.stalk x) = (1 : WithBot ℕ∞) ∧
      ∃ σ : C.residueField x →+*
          AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x),
        (∀ t : k, σ (f.residueFieldAlgebraMap x t) =
          algebraMap (C.presheaf.stalk x) _
            (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ C.presheaf.Γgerm x).hom t)) ∧
        (∀ t : C.residueField x,
          AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (σ t) = t) ∧
        ∃ a b c : C.residueField x, b ^ 2 - 4 * a * c ≠ 0 ∧
          ∃ e : @AlgEquiv (C.residueField x)
              (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
                (C.presheaf.stalk x))
              (MvPowerSeries (Fin 2) (C.residueField x) ⧸
                Ideal.span ({MvPowerSeries.C a * (MvPowerSeries.X 0) ^ 2 +
                  MvPowerSeries.C b * (MvPowerSeries.X 0 * MvPowerSeries.X 1) +
                  MvPowerSeries.C c * (MvPowerSeries.X 1) ^ 2} :
                  Set (MvPowerSeries (Fin 2) (C.residueField x))))
              inferInstance inferInstance inferInstance σ.toAlgebra inferInstance,
            @Continuous _ _
              ((IsLocalRing.maximalIdeal (C.presheaf.stalk x)).map
                (algebraMap (C.presheaf.stalk x)
                  (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
                    (C.presheaf.stalk x)))).adicTopology
              (TopologicalSpace.coinduced (Ideal.Quotient.mk _)
                (Ideal.span (Set.range
                  (fun i : Fin 2 ↦ (MvPowerSeries.X i :
                    MvPowerSeries (Fin 2) (C.residueField x))))).adicTopology) e ∧
            ∀ h : MvPowerSeries (Fin 2) (C.residueField x),
              AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (C.presheaf.stalk x))
                (e.invFun (Ideal.Quotient.mk _ h)) = MvPowerSeries.constantCoeff h := by
  sorry

end AlgebraicGeometry
