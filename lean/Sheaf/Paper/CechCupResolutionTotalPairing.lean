/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechCupProduct

/-! # The two axis squares of the signed total Cech pairing

Source: Stacks Project, Tags 07MB and 0FKV.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The signed total Cech pairing preserves both axes: restriction of global
resolution cocycles and augmentation of coefficient Cech cocycles.
Source: Stacks Project, Tag 07MB (signed total map) and Tag 0FKV, proof, final diagram.
(blueprint: lem-sc-cech-cup-resolution-total-pairing)

Proof: on the summand with resolution/Cech bidegrees (r,i) and (s,j), restrict the
first factor to the front i+1 vertices and the second to the last j+1 vertices,
apply D.pair r s on their common intersection, and multiply by (-1)^(i*s).
Include the resulting section in bidegree (r+s,i+j) of the target total complex.
Finite direct-sum assembly and bilinearity give the map from the tensor of total
complexes. The Cech Leibniz identity follows by adjacent omitted-vertex cancellation;
the resolution Leibniz identity is D.leibniz. The displayed sign makes these agree
with the total differentials, so the map is a cochain pairing and descends to the
bilinear map t on homology: the Leibniz identity pairs cycles to cycles and pairs
a boundary with a cycle to a boundary in either factor, so quotient descent is
well-defined. On alpha images i=j=0: the sign is one and restriction
compatibility of D.pair gives the first square. On beta images r=s=0: again the
sign is one and D.augmentation_pair gives the front/back formula for cechCupCochain.
The alpha_f and beta_f equations identify the maps in the statement with these
axis inclusions. Pass both equalities to homology to get the two asserted cycle
formulas. Terms with zero factors vanish by bilinearity; degrees zero and empty
index sets obey the same finite-sum identities. No acyclicity of the resolutions
is used in this step. -/
theorem cupCechResolution_total_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (A : CupCechResolutionComparison U D.left)
    (B : CupCechResolutionComparison U D.right)
    (C : CupCechResolutionComparison U D.target) (p q : ℕ) :
    ∃ t : ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).homology p →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).homology q →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).homology (p + q),
      (∀ (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          t (HomologicalComplex.homologyMap A.alpha p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap B.alpha q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap C.alpha (p + q) (cupCycleClass _ (p + q) c)) ∧
      (∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
          p).moduleCatLeftHomologyData.K)
        (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
          q).moduleCatLeftHomologyData.K)
        (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
          (p + q)).moduleCatLeftHomologyData.K),
        c.val = cechCupCochain U F G p q a.val b.val →
          t (HomologicalComplex.homologyMap A.beta p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap B.beta q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap C.beta (p + q) (cupCycleClass _ (p + q) c)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
