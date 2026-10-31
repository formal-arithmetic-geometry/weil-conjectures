/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFunctor
public import WeilConjectures.SixFunctors.Supporting.IntrinsicQbarCategory
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierBiduality
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierExactness
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierScalars
import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierComparison

/-! # Exact linear biduality for the constructed common-stage dual

Source: thm-coef-qbar-verdier, proof steps 3--4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion transition)
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

set_option maxHeartbeats 800000 in
-- Assembling the components elaborates the transported stage-system and scalar structures.
-- The default budget is exhausted during type comparison; this proof compiles in 22 seconds.
attribute [-instance] intrinsicQbarStageLocalizedLinear intrinsicQbarStageLinear in
/-- The constructed representative functor is exact and linear, and the finite
biduality isomorphisms descend with their prescribed comparisons.
Source: thm-coef-qbar-verdier, proof steps 3--4 and the biduality portion of step 5
(blueprint: lem-coef-qbar-verdier-biduality-equations).

Proof: use the fixed descendedDual, obtained by reversing representatives and
applying the finite dual functors. At a common field containing a given scalar,
the rational finite linearity equation commutes with its two beta factors.
The intrinsic quotient scalar formula therefore proves Omega-linearity. Computing
this action at E itself gives the displayed coefficient normalization. Tower
coherence identifies the map of an inclusion-transition isomorphism with its
beta factors, giving the scalar comparison equation, including repeated fields.
At (E,K), define delta by including the finite bidual map and transporting twice
through descendedComparison, in precisely the displayed order. The finite scalar
biduality square and naturality of beta show these components are natural on
every common-stage representative. Include the finite inverse bidual map in the
reverse order. At each finite representative the two composites cancel to the
identity, so delta is a natural isomorphism. The resulting anti-equivalence is
a formal consequence of this biduality and is proved separately by the consumer.
Finally descend its finite shift comparisons, whose scalar compatibility follows
by the uniqueness of evaluation transposes. The finite shift coherence equations
hold on every object pair. A distinguished opposite triangle is isomorphic to
an included finite distinguished opposite triangle; finite exactness and these
same shift comparisons carry it to a distinguished triangle. This establishes
exactness for the prescribed triangulation. Every object is a literal finite pair,
so the displayed compatibility determines delta uniquely from the finite maps.
All formulas cover zero objects,
the empty scheme, torsion integral representatives and identity extensions. -/
theorem descended_duality_exists (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    ∃ δ : 𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω X) ≅
        (descendedDual D l hl Ω X F hF).rightOp ⋙ descendedDual D l hl Ω X F hF,
    (∃ s : (descendedDual D l hl Ω X F hF).CommShift ℤ,
      ∀ T : Triangle (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ,
        T ∈ distTriang (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ →
        Triangle.mk ((descendedDual D l hl Ω X F hF).map T.mor₁)
          ((descendedDual D l hl Ω X F hF).map T.mor₂)
          ((descendedDual D l hl Ω X F hF).map T.mor₃ ≫
            (s.commShiftIso (1 : ℤ)).hom.app T.obj₁) ∈
          distTriang (generalAlgebraicallyClosedConstructibleCategory l Ω X)) ∧
    (∀ (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
        (f : K ⟶ M) (c : Ω),
      (descendedDual D l hl Ω X F hF).map (c • f).op =
        c • (descendedDual D l hl Ω X F hF).map f.op) ∧
    (∀ (E : Index l Ω)
        (K M : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X)
        (f : K ⟶ M) (c : Coefficient.{u} l Ω E),
      (inclusion (Y := X) E).map
        ((sfRationalCoefficientEquiv l (Coefficient.{u} l Ω E)).symm c •
          (f : (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X) ⟶ M)) =
        ((Shrink.algEquiv (Padic l) E.val c : E.val) : Ω) • (inclusion E).map f) ∧
    (∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
      (inclusion L).map ((F.beta E L h).hom.app (op K)) ≫
        (descendedComparison D l hl Ω X F hF L).hom.app
          (op ((transition l Ω X E L h).obj K)) ≫
        (descendedDual D l hl Ω X F hF).map
          ((inclusionTransition l Ω X E L h).inv.app K).op =
      (inclusionTransition l Ω X E L h).hom.app ((F.datum E).dual.obj (op K)) ≫
        (descendedComparison D l hl Ω X F hF E).hom.app (op K)) ∧
    (∀ E : Index l Ω,
      SfClassEvaluationCompatible (inclusion (Y := X) E) (F.datum E).dual
        (descendedDual D l hl Ω X F hF) (F.datum E).bidual.hom δ.hom
        (descendedComparison D l hl Ω X F hF E)) := by
  obtain ⟨δ, hδ⟩ := descended_biduality D l hl Ω X F hF
  obtain ⟨s, hs⟩ := descended_exactness D l hl Ω X F hF
  obtain ⟨hΩ, hE⟩ := descended_scalar_formulas D l hl Ω X F hF
  have hcomp := descended_comparison_formula D l hl Ω X F hF
  exact ⟨δ, ⟨s, hs⟩, hΩ, hE, hcomp, hδ⟩

end WeilConjectures.CoefQbarVerdier
