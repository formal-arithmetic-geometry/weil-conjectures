/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
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
For an inclusion E into F, O_F is finite free over O_E. A basis identifies its tensor
extension with a finite direct sum;
ordinary direct image and total inverse limit commute with that sum. The normalized
finite-reduction maps identify the resulting isomorphism with the geometric
right-adjoint mate of the inverse pullback comparison. Rationalize it. For any other
specified right adjoints R and a, transport the isomorphism by rightAdjointUniq.
The counit normalization of that uniqueness isomorphism identifies this map with
the specified mate. Here only invertibility is asserted; the consumer obtains the
counit equation from Mathlib's mateEquiv_counit. This statement concerns coefficient
change only: it asserts no pointwise adjoint existence, common-stage adjunction or Weil lift.
Repeated fields use the tensor unit; the argument also applies to zero objects,
empty schemes and nonseparated finite-type maps. -/
theorem sfRationalDirectImageCoefficientCompatibility
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f : X₀ ⟶ Y₀) :
    letI := sfWeilPrimeInvertible D l hl X₀
    letI := sfWeilPrimeInvertible D l hl Y₀
    ∃! L : (stageSystem l Ω (D.geometricFiber Y₀).left).Morphism
        (stageSystem l Ω (D.geometricFiber X₀).left),
      L.Φ = (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) (zlFiberMap D f)) ∧
      (∀ (E F : Index l Ω) (h : E ≤ F)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
          (D.geometricFiber Y₀).left),
        HEq ((L.β h).app K)
          (commonStagePullbackComparison l Ω (zlFiberMap D f) ⟨E, K⟩ F h)) ∧
      ∀ (R : ∀ E : Index l Ω,
        sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            (D.geometricFiber X₀).left ⥤
          sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            (D.geometricFiber Y₀).left)
        (a : ∀ E, L.Φ E ⊣ R E),
        ∀ {E F : Index l Ω} (h : E ≤ F),
          IsIso ((mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _ (L.β h).inv)).natTrans) := by
  sorry

end WeilConjectures
