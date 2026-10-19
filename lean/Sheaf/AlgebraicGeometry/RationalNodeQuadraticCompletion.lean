/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.ZetaSeries
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Sheaf.RingTheory.PresentationFittingIdeal
import Sheaf.TraceFormula.FormalJacobianQuadraticCriterion
import Sheaf.RingTheory.FlatLocalDepthFormula
import WeilConjectures.RingTheory.Depth
import Sheaf.RingTheory.SeparableClosedPointFormalPresentation

/-!
# Quadratic completed equation at a rational geometric node

Source: Stacks Project, curves.tex, Tag 0C4D, implication (3) to (2), and Tag 0C49,
condition (3), with residue field equal to the ground field
(blueprint: lem-trf-rational-node-quadratic-completion).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A rational geometric node has a nondegenerate binary quadratic completed equation
as an algebra over its original ground field. Since `z` is rational, its geometric lift
is the unique point of the base change mapping to `z`; `hzbar` specifies that point.
The algebra on the completion is explicitly induced by the structure map on global
sections followed by the germ map and the canonical completion map.

Source: Stacks Project, curves.tex, Tag 0C4D, implication (3) to (2), followed by
Tag 0C49, condition (3), with residue field equal to the ground field
(blueprint: lem-trf-rational-node-quadratic-completion).

Proof:
1. Choose an affine neighbourhood Spec S of z. By lem-weil-pbc-lft-affine-pairs,
   S is finite type over F. Its rational augmentation has maximal kernel p. Put
   A = S_p and B = (S tensor_F Omega)_q at the induced rational point. Apply
   lem-trf-separable-closed-point-formal-presentation to F/F and Omega/F: A, B and
   the completion of A are Noetherian local, A to B is faithfully flat with extended
   maximal ideal the maximal ideal of B and closed fibre Omega, and the completion
   of A has a formal presentation and residue field F. The corresponding facts about
   the completion of B come from the SECOND application in step 3. The coefficient
   section of F into the completion of A is its structural F-algebra map.
2. Kahler differentials are finite, since the differentials of finitely many algebra
   generators generate them. Use lem-weil-pbc-kahler-differentials-localization and
   lem-weil-pbc-kahler-differentials-base-change to identify Omega_{B/Omega} with
   Omega_{A/F} tensor_A B. Let J_A and J_B be their first Fitting ideals. Clause (2)
   of lem-trf-fitting-ideal-independence-base-change gives J_B = J_A B.
3. Apply lem-trf-separable-closed-point-formal-presentation a second time, now to
   S tensor_F Omega over Omega at q. Its completion is Noetherian local, with
   maximal ideal n times the completion and residue field Omega. Choose its formal
   presentation with at least two variables. Its Jacobian cokernel is the completed
   differential module. The given RING isomorphism satisfies clause (c) of
   lem-trf-formal-jacobian-quadratic-criterion, with a = c = 0 and b = 1. Thus the
   completed B has depth one and its Jacobian-minor ideal is its maximal ideal.
   Presentation independence and base change identify this ideal with completed J_B.
4. By lem-weil-pbc-local-completion-faithfully-flat, B to its completion is faithfully
   flat. Contract the equality of extended ideals using
   lem-weil-pbc-faithfully-flat-ideal-contraction to get J_B = n. Contract once more
   along A to B to obtain J_A = m.
5. Apply lem-weil-pbc-flat-local-depth-formula to B to its completion, A to B, and A
   to its completion. Their closed fibres are respectively Omega, Omega and F, all
   of depth zero by def-weil-pbc-depth. The depth-one result of step 3 therefore gives
   depth one for B, A, and the completion of A.
6. In the formal presentation of the completion of A, its Jacobian cokernel is the
   completed differential module. Fitting base change identifies its minor ideal
   with J_A times the completion, hence the maximal ideal by step 4. Together with
   step 5, clause (a) of lem-trf-formal-jacobian-quadratic-criterion gives clause (b):
   coefficients a,b,c in F, nonzero discriminant, and the required F-algebra
   isomorphism. Step 1 identifies its F-structure with the original structural map. -/
theorem rational_node_quadratic_completion
    {F : Type u} [Field F] {X : Scheme.{u}} (f : X ⟶ Spec (.of F))
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = (1 : WithBot ℕ∞))
    (z : X) (hz : z ∈ closedPoints X)
    (hrat : Function.Bijective (f.residueFieldAlgebraMap z))
    (Ω : Type u) [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (zbar : pullback (C := Scheme.{u}) f
      (Spec.map (CommRingCat.ofHom (algebraMap F Ω))))
    (hzbar : pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) zbar = z)
    (hgeom : Nonempty
      (AdicCompletion
        (IsLocalRing.maximalIdeal
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))).presheaf.stalk zbar))
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap F Ω)))).presheaf.stalk zbar)
        ≃+* (MvPowerSeries (Fin 2) Ω ⧸
          Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) * MvPowerSeries.X 1}))) :
    ∃ (a b c : F), b ^ 2 - 4 * a * c ≠ 0 ∧
      Nonempty
        (@AlgEquiv F
          (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z)) (X.presheaf.stalk z))
          (MvPowerSeries (Fin 2) F ⧸
            Ideal.span ({MvPowerSeries.C a * (MvPowerSeries.X 0) ^ 2 +
              MvPowerSeries.C b * (MvPowerSeries.X 0 * MvPowerSeries.X 1) +
              MvPowerSeries.C c * (MvPowerSeries.X 1) ^ 2} : Set (MvPowerSeries (Fin 2) F)))
          inferInstance inferInstance inferInstance
          (((algebraMap (X.presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
                (X.presheaf.stalk z))).comp
            (((Scheme.ΓSpecIso (.of F)).inv ≫ f.appTop ≫ X.presheaf.Γgerm z).hom)).toAlgebra)
          inferInstance) := by
  sorry

end AlgebraicGeometry
