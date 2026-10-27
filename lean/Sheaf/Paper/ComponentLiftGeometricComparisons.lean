/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.ComponentLiftSectionDefs
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.ComponentLiftBaseChange

/-! # Coherent geometric comparisons for component lifts

Source: Hemo--Richarz--Scholbach, Definition 3.3, Lemma 4.1 and Proposition 4.3(3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Coherent component pullbacks, their normalized test comparisons, and equivalence on
objects admitting duals. This is the geometric part of the component section theorem.

Source: HRS construction (4.1), Lemma 4.1 and Proposition 4.3(3)
(blueprint: lem-sfb-component-lift-geometric-comparisons).

Proof: transport the relative component-test site along e. Its coordinate is the
coordinate of the universal component lift; the equation over S follows by applying e
to its equation over pi_0(T). Its universal mapping property transports along e.symm.
The inverse image is the sheafified left Kan extension with its constructed adjunction;
continuity and finite-limit preservation follow from the relative-site theorem, and
finite-colimit preservation from this adjunction. The monoidal point factorization
identifies its image of the restricted coefficient ring with Lambda_T. Derive this exact
module functor termwise, using its tensor and unit comparisons.
For a component-preserving g, the universal properties of the two relative lifts give
inverse projection-preserving maps between V times_S E and V times_U (U times_S E).
Uniqueness proves naturality. The induced inverse-image isomorphism has commuting
adjunction units on every test, which is precisely ComponentLiftInducedComparison.
Lift it through the coefficient-ring comparison and localize to obtain c by the
specified componentLiftDerivedComparison formula. Ringed-derived comparisons prove
monoidality. For successive maps, both test comparisons have the same projections;
uniqueness, then the adjunction mate and localization, give the displayed composition.
Finally transport the component equivalence of condensed_wcontractible_lisse_evaluation
from pi_0(T) to S. It gives full faithfulness on dualizable objects, preservation of
dualizable objects, and essential surjectivity, exactly ComponentLiftEquivalence.
Empty component spaces and the zero coefficient ring use the same universal properties. -/
theorem component_lift_geometric_comparisons
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) [ExtremallyDisconnected S] :
    ∃ d : ∀ (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
        (e : affineComponentSpace T ≃ₜ S), ComponentLiftCoefficient Λ S T e,
      ∃ m : ∀ (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
          (e : affineComponentSpace T ≃ₜ S), (componentLiftDerived (d T e)).Monoidal,
        ∃ c : ∀ (U V : Scheme.{u}) [IsAffine U] [IsAffine V]
            [IsWContractibleRing Γ(U, ⊤)] [IsWContractibleRing Γ(V, ⊤)]
            (eU : affineComponentSpace U ≃ₜ S) (eV : affineComponentSpace V ≃ₜ S)
            (g : V ⟶ U), IsComponentLiftMap eU eV g →
            ((componentLiftDerived (d U eU) ⋙ moduleObjectDerivedPullback Λ.X g) ≅
              componentLiftDerived (d V eV)),
          (∀ (U V : Scheme.{u}) [IsAffine U] [IsAffine V]
            [IsWContractibleRing Γ(U, ⊤)] [IsWContractibleRing Γ(V, ⊤)]
            (eU : affineComponentSpace U ≃ₜ S) (eV : affineComponentSpace V ≃ₜ S)
            (g : V ⟶ U) (hg : IsComponentLiftMap eU eV g),
            (∃ k : componentLiftTests V S eV ≅ componentLiftTests U S eU ⋙
                MorphismProperty.Over.pullback @WeaklyEtale ⊤ g,
              (∀ (E : Over S) (v : ((componentLiftTests V S eV).obj E).left),
                (d U eU).projection E
                  (pullback.fst ((componentLiftTests U S eU).obj E).hom g
                    ((k.app E).hom.left v)) = (d V eV).projection E v) ∧
              ∃ q : componentLiftModules (d U eU) ⋙ upperStar Λ.X g ≅
                  componentLiftModules (d V eV),
                ComponentLiftInducedComparison (d U eU) (d V eV) g k q ∧
                c U V eU eV g hg =
                  componentLiftDerivedComparison (d U eU) (d V eV) g q) ∧
            ComponentLiftMonoidal (m U eU) (m V eV) (c U V eU eV g hg)) ∧
          (∀ (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)]
            (e : affineComponentSpace T ≃ₜ S), ComponentLiftEquivalence (d T e)) ∧
          (∀ (U V W : Scheme.{u}) [IsAffine U] [IsAffine V] [IsAffine W]
            [IsWContractibleRing Γ(U, ⊤)] [IsWContractibleRing Γ(V, ⊤)]
            [IsWContractibleRing Γ(W, ⊤)]
            (eU : affineComponentSpace U ≃ₜ S) (eV : affineComponentSpace V ≃ₜ S)
            (eW : affineComponentSpace W ≃ₜ S) (g : V ⟶ U) (h : W ⟶ V)
            (hg : IsComponentLiftMap eU eV g) (hh : IsComponentLiftMap eV eW h)
            (hc : IsComponentLiftMap eU eW (h ≫ g))
            (N : Evaluation.D ((coherentTopology Profinite.{u}).over S)
              (profiniteCoefficient Λ.X S)),
            (leftDerivedUpperStarComp Λ.X h g).hom.app ((componentLiftDerived (d U eU)).obj N) ≫
              (moduleObjectDerivedPullback Λ.X h).map ((c U V eU eV g hg).hom.app N) ≫
              (c V W eV eW h hh).hom.app N = (c U W eU eW (h ≫ g) hc).hom.app N)
 := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
