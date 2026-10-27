/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Coefficient-change mates before common-stage descent

Source: Bhatt--Scholze 6.7.2, 6.8.14(2), Remark 6.8.15; the finite-coefficient
construction of derived direct image in the blueprint.
(blueprint: lem-sf-rational-direct-image-coefficient-compatibility).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients

/-- Coherent coefficient pullback comparisons and invertible direct-image mates.
Source: Bhatt--Scholze 6.8.14(2), Remark 6.8.15; finite-free scalar change
(blueprint: lem-sf-rational-direct-image-coefficient-compatibility).
Proof: use the normalized integral scalar/pullback maps and their coefficient-tower
identity. On simultaneous flat-term K-flat representatives, the two tower composites
multiply the new coefficients in the same order. Ordinary scalar associativity and
the normalized completion maps give this identity for completed scalar extension.
Localize these precise maps and conjugate by operationStageTransitionIso.
This constructs the stage morphism with the prescribed components. Its functor
family is fixed literally. Naturality and the displayed component normalization
fix every comparison natural isomorphism, and proof irrelevance fixes coherence.
Thus the entire stage morphism is unique, in equality, not just up to isomorphism.
For an inclusion E into F, O_F is finite free over O_E. Write T for scalar extension
from E to F and Res for restriction of scalars (exact on finite free coefficients, so it
preserves constructibility). T is left adjoint to Res, and, after rationalization, the
trace form of F over E is nondegenerate, so Hom_E(O_F, -) agrees with T and Res is
also left adjoint to T. Pullback commutes with Res: the mate of the comparison
L_F T = T L_E under Res left adjoint to T is the comparison Res L_F to L_E Res, invertible
because derived pullback is computed termwise and forgets the O_F-module structure.
The mate T R_E to R_F T of the inverse comparison under the given adjunctions a and the
mate Res L_F to L_E Res are conjugate under the composite adjunctions L_E Res left
adjoint to T R_E and Res L_F left adjoint to R_F T; a transformation of left adjoints is
invertible exactly when its conjugate is. This uses only the supplied R and a, not
any geometric description of a right adjoint, so it holds for arbitrary scheme maps.
Hence the specified mate is invertible. Here only invertibility is asserted; the
consumer obtains the counit equation from Mathlib's mateEquiv_counit. This statement
concerns coefficient change only: it asserts no pointwise adjoint existence, common-stage
adjunction or Weil lift.
Repeated fields use the tensor unit; the argument also applies to zero objects,
empty schemes and arbitrary scheme maps: only coefficient extension is used.
The right adjoints are supplied, not asserted to exist on arbitrary schemes. -/
theorem sfRationalDirectImageCoefficientCompatibility
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    ∃! L : (stageSystem l Ω Y).Morphism
        (stageSystem l Ω X),
      L.Φ = (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) f) ∧
      (∀ (E F : Index l Ω) (h : E ≤ F)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
          Y),
        HEq ((L.β h).app K)
          (commonStagePullbackComparison l Ω f ⟨E, K⟩ F h)) ∧
      ∀ (R : ∀ E : Index l Ω,
        sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            X ⥤
          sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            Y)
        (a : ∀ E, L.Φ E ⊣ R E),
        ∀ {E F : Index l Ω} (h : E ≤ F),
          IsIso ((mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _ (L.β h).inv)).natTrans) := by
  sorry

end WeilConjectures
