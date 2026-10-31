/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeMaps

/-! # Derived closed-unit evaluation and its naturality

Source: Stacks Project, proetale.tex, Tags 09BK and 09BL; sites-cohomology.tex, Tag 0D6F.
(blueprint: lem-sfb-nonaffine-closed-derived-evaluation). -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedTestSectionSteps

open ClosedTestDerivedExchangeModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual closed-unit comparison commutes with admissible test restrictions
on unbounded derived inputs.
Source: Stacks Project, Tags 09BK, 09BL and 0D6F
(blueprint: lem-sfb-nonaffine-closed-derived-evaluation).

Proof: expand closedComparison as restriction along the closed-site inclusion,
the equality of its composite with the structural morphism, and pullComp.
The inclusion is a natural transformation of the affine pro-etale site functors,
so a test arrow gives a commuting square of these inclusions. Adjunction units
are natural, and the unit of a composite adjunction is the composite of its units.
Apply this identity to that square, then use associativity of pullComp and the
normalization of pushDerivedSectionsIso by ordinary section composition.
The two resulting maps are precisely the displayed composites of sectionsArrow
and closedComparison. Equivalently compute these maps on K-injective resolutions:
both are the presheaf restriction followed by the same inverse-image unit.
The equality descends through the universal right-derived comparison.
No invertibility is needed. Identity arrows, zero complexes, I=0 and empty tests
satisfy the same unit and composition identities. -/
theorem closed_derived_evaluation
    (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)] :
    ∀ (V' : (Spec (.of (A ⧸ I))).AffineProEt) (r : V' ⟶ V)
        [IsWContractibleRing Γ(V'.left, ⊤)]
        [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V').left, ⊤)]
        (K : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
            (condensedRingObj Λ (Spec (.of A))))),
        (closedComparison Λ A I V).app K ≫
            (sectionsArrow Λ r.left (MorphismProperty.Over.w r)).app
              ((pull Λ (closedMap A I)).obj K) =
          (sectionsArrow Λ ((Scheme.AffineProEt.closedSiteLift A I).map r).left
              (MorphismProperty.Over.w ((Scheme.AffineProEt.closedSiteLift A I).map r))).app
                K ≫ (closedComparison Λ A I V').app K := by sorry

end AlgebraicGeometry.ProEtale.ClosedTestSectionSteps
