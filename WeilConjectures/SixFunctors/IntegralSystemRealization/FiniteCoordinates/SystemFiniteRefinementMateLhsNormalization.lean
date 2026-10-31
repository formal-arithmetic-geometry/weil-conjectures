/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteEvaluationCoordinates

/-! # Left normalization for the finite refinement mate

Source: Stacks 03DI, 07A7 and 0F7B; the finite-evaluation step of
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-finite-refinement-mate-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.AmbientProperOpen
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

private theorem insert_bridge
    {C D T : Type*} [Category C] [Category D] [Category T]
    (V : D ⥤ T) {F G : C ⥤ D} (α : F ≅ G)
    {x y : C} (β : x ≅ y) {a b : D} {t : T}
    (u : a ⟶ b) (v : b ⟶ F.obj x) (w : V.obj (F.obj x) ⟶ t) :
    V.map (u ≫ v) ≫ w =
      V.map (u ≫ v ≫ α.hom.app x ≫ G.map β.hom) ≫
        V.map (α.inv.app y) ≫ V.map (F.map β.inv) ≫ w := by
  have hn := α.hom.naturality β.hom
  have hc : α.hom.app x ≫ G.map β.hom ≫ α.inv.app y ≫ F.map β.inv = 𝟙 _ := by
    rw [← reassoc_of% hn]
    simp only [Iso.hom_inv_id_app_assoc, ← F.map_comp, β.hom_inv_id,
      F.map_id]
  have he := congrArg (fun z ↦ V.map (u ≫ v) ≫ V.map z ≫ w) hc
  simpa only [V.map_id, Category.id_comp, Functor.map_comp, Category.assoc] using he.symm

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  scalarReductionTargetDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

/-- The evaluated system word is the canonical bridge word after the finite
coefficient comparison is inserted.  This is the left transport and cancellation
step in the proof of `refinementMate`.

Source: Stacks 03DI and 0F7B; proper/open mate evaluation and the normalized
identity-open comparison.
The proof expands the finite open and direct evaluations, applies
`SemilinearProperOpen.gamma_evaluation`, and cancels the coefficient
equivalence units.  Identity refinements, zero objects, and empty opens are
covered by the same naturality and triangle identities.
(blueprint: lem-sf-system-finite-refinement-mate-coordinates).
-/
theorem lhsNormalization (D : FiniteFieldDatum.{u}) (o : Operations l E)
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
              X.obj.left).inv.app M) ≫
          (z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
            (r.i_hom.trans (Category.id_comp _).symm)).app M) ≫
      (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom ≫
      RW.functor.map ((ProperOpenPush A r.hom).map (fixedShriek l E o m c.i M).hom) =
    (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((Operations.shriek l E o d.i).map
          ((z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
            SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
              X.obj.left).inv.app M) ≫
          (z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
            (r.i_hom.trans (Category.id_comp _).symm)).app M ≫
          (z.canonicalBridge.push l E r.hom).hom.app
            ((Operations.shriek l E o c.i).obj M) ≫
          (SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) r.hom).map
            ((z.canonicalBridge.shriek l E c.i).hom.app M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.canonicalBridge.push l E r.hom).inv.app
          ((SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) c.i).obj M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((Operations.push l E o r.hom).map
          ((z.canonicalBridge.shriek l E c.i).inv.app M)) ≫
      (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom ≫
      RW.functor.map ((ProperOpenPush A r.hom).map (fixedShriek l E o m c.i M).hom) := by
  dsimp only
  exact insert_bridge (coefficientSequenceDerivedEvaluation l E d.Z m)
    (z.canonicalBridge.push l E r.hom) ((z.canonicalBridge.shriek l E c.i).app M)
    _ _ _

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
