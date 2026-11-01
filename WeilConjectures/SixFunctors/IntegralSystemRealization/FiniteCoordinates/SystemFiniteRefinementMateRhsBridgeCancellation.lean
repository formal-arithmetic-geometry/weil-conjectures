/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteEvaluationCoordinates
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData

/-! # Canonical bridge cancellation for the finite refinement mate

Source: Stacks 00YV and 0F7B; the finite-evaluation step of
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-finite-refinement-mate-rhs-normalization-bridge-cancellation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.AmbientProperOpen
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  scalarReductionTargetDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

private theorem insertBridgeFactors
    {B C D : Type*} [Category B] [Category C] [Category D]
    (R : B ⥤ C) (F : C ⥤ D) {U : C} {V W : B}
    (p : U ≅ R.obj V) (s : V ≅ W)
    {T₀ T₁ T₂ T₃ : D} (a : T₀ ⟶ T₁) (b : T₁ ⟶ F.obj U)
    (c : F.obj U ⟶ T₂) (d : T₂ ⟶ T₃) :
    a ≫ b ≫ c ≫ d =
      a ≫ b ≫ F.map p.hom ≫ F.map (R.map s.hom) ≫
        F.map (R.map s.inv ≫ p.inv) ≫ c ≫ d := by
  rw [F.map_comp, Category.assoc,
    ← F.map_comp_assoc (R.map s.hom) (R.map s.inv), ← R.map_comp,
    s.hom_inv_id, R.map_id, F.map_id, Category.id_comp,
    ← F.map_comp_assoc p.hom p.inv, p.hom_inv_id, F.map_id, Category.id_comp]

/-- Cancelling the identity canonical bridge and expanding the finite push and shriek
coordinates leaves the evaluated system mate with its canonical bridge factors.

Source: Stacks 00YV and 0F7B; coefficient-equivalence triangle identities.
Expand `push`, `fixedShriek`, and `shriek`, use naturality of the canonical bridge
isomorphisms, and cancel the unit and counit of the intrinsic equivalence. The
argument is a direct categorical calculation and covers identity refinements,
zero objects, and empty opens.
(blueprint: lem-sf-system-finite-refinement-mate-rhs-normalization-bridge-cancellation).
-/
theorem rhsCoreBridgeCancellation (D : FiniteFieldDatum.{u}) (o : Operations l E)
    (z : Realizations l E D o) (m : ℕ)
    {X Y : Spaces D} {f : X ⟶ Y} [QuasiCompact f.hom.left]
    (c d : Compactification f.hom.left) (r : c.Refinement d)
    (M : System l E X.obj.left) :
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))
    let RW := sfIntrinsicDerivedEquivalence d.Z (Padic.coefficientExtensionRing l E (m + 1))
    haveI := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
    haveI := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
    (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((Operations.shriek l E o d.i).map
          ((z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
            SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
              X.obj.left).inv.app M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
          (r.i_hom.trans (Category.id_comp _).symm)).app M) ≫
      (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom ≫
      RW.functor.map ((ProperOpenPush A r.hom).map (fixedShriek l E o m c.i M).hom) =
    (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((Operations.shriek l E o d.i).map
          ((z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
            SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
              X.obj.left).inv.app M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
          (r.i_hom.trans (Category.id_comp _).symm)).app M) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.canonicalBridge.push l E r.hom).hom.app
          ((Operations.shriek l E o c.i).obj M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r.hom).map
          ((z.canonicalBridge.shriek l E c.i).hom.app M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r.hom).map
          ((z.canonicalBridge.shriek l E c.i).inv.app M) ≫
          (z.canonicalBridge.push l E r.hom).inv.app
            ((Operations.shriek l E o c.i).obj M)) ≫
      (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom ≫
      RW.functor.map ((ProperOpenPush A r.hom).map (fixedShriek l E o m c.i M).hom) := by
  exact insertBridgeFactors
    (SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r.hom)
    (coefficientSequenceDerivedEvaluation l E d.Z m)
    ((z.canonicalBridge.push l E r.hom).app ((Operations.shriek l E o c.i).obj M))
    ((z.canonicalBridge.shriek l E c.i).app M) _ _ _ _

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
