/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparisonSystem
public import WeilConjectures.FourierTransform.FdPullbackAugmentationCounitMatching

/-! # Mixed transformation of the selected normalized finite pullbacks

Source: trace-definition auxiliary whole-tower argument, as recorded in the parent
comparison node; Stacks 0941 and 099N
(blueprint: lem-fd-normalized-pullback-mixed). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Fixed normalized finite pullbacks form a compatible transformation of the
actual scalar stage families. The finite components are retained literally.
Source: trace-definition whole-tower argument, steps 9--10, and common-stage
comparison descent, steps 9--12; Stacks 0941 and 099N
(blueprint: lem-fd-normalized-pullback-mixed).

Proof: the normalized Roos matching and finite chain normalization identify each
inverse ambient component with the common strict-tower comparison: both carry
the quotient/zero-coordinate augmentation to the actual PBC unit. Cancel the
invertible framework augmentation on complete inputs. Fullness identifies their
integral restrictions. Raw localization then identifies every rational component
by FdPullbackComparison.rationalization. Apply
fdScalarRoosComparisonIntertwining at E <= L and substitute these identifications.
Its rational equation is the mixed scalar square for these fixed components.
The supplied framework beta and the coefficient finite_functor equations insert
only their recorded presentation transports. Rearranging the square by its
invertible beta factors is precisely StageSystem.Morphism.Hom.comm. Define tau
by the finite rational homs transported through sfFinite and finite_functor;
the preceding equation gives comm and its construction gives components below.
Equality of fields uses the actual multiplication/completeness unit, so does not
need strict identity transitions. The same argument applies to zero objects,
identity scheme maps and ramified coefficient inclusions; no individual quotient
map is inverted and no Karoubi envelope is used. -/
theorem fdNormalizedPullbackMixed (R : IntegralComparisonSystem.{u} l)
    {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (CU : FdCoefficientComparison l Ω U) (CT : FdCoefficientComparison l Ω T)
    (h : U ≅ T) (finite : ∀ E, FdPullbackComparison l Ω CU CT h E)
    (_matching : ∀ E, FdPullbackRoosMatching l Ω CU CT h E R (finite E))
    (F : StageSystem.Morphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω U))
    (_sfFinite : ∀ E, HEq (F.Φ E)
      (rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) h.hom))
    (_sfBeta : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (e : E ≤ L)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
      HEq ((F.β e).hom.app K)
        (commonStagePullbackComparison l Ω h.hom ⟨E, K⟩ L e).hom) :
    ∃ mixed : StageSystem.Morphism.Hom
      (CT.family.comp (pbcQbarPullFamily l Ω h.hom)) (F.comp CU.family),
      ∀ E, HEq (mixed.τ E) (finite E).rational.hom := by sorry

end WeilConjectures
