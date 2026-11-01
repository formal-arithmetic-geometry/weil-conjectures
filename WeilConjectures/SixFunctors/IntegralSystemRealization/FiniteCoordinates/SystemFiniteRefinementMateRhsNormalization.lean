/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateCanonical
public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteEvaluationCoordinates
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateRhsCore

/-! # Right normalization for the finite refinement mate

Source: Stacks 00YV and 0F7B; the finite-evaluation step of
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-finite-refinement-mate-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.AmbientProperOpen
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

private theorem iso_naturality_cancel
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    {F G : C' ⥤ D} {H K : C ⥤ C'} (α : F ≅ G) (β : H ≅ K) (M : C) :
    α.hom.app (H.obj M) ≫ G.map (β.hom.app M) ≫ α.inv.app (K.obj M) ≫
        F.map (β.inv.app M) = 𝟙 _ := by
  have hn := α.hom.naturality (β.hom.app M)
  have hc : α.hom.app (H.obj M) ≫ G.map (β.hom.app M) ≫
      α.inv.app (K.obj M) ≫ F.map (β.inv.app M) = 𝟙 _ := by
    rw [← reassoc_of% hn]
    simp only [Iso.hom_inv_id_app_assoc, ← F.map_comp, β.hom_inv_id_app,
      F.map_id]
  exact hc

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  scalarReductionTargetDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

/-- The canonical bridge target is the fixed finite proper/open mate.  This is
the right transport and cancellation step in the proof of `refinementMate`.

Source: Stacks 00YV and 0F7B; coefficient-equivalence triangle identities and
the normalized proper/open mate.
The proof expands `fixedShriek`, transports the identity-open comparison through
the intrinsic equivalence, and uses naturality of `properOpenMate`.  It uses no
faithfulness or detection by finite evaluation; zero inputs and empty opens are
included by the same functorial identities.
(blueprint: lem-sf-system-finite-refinement-mate-coordinates).
-/
theorem rhsNormalization (D : FiniteFieldDatum.{u}) (o : Operations l E)
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
          (z.canonicalBridge.shriek l E d.i).hom.app
            ((Operations.push l E o (𝟙 X.obj.left)).obj M) ≫
          (SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) d.i).map
            ((z.canonicalBridge.push l E (𝟙 X.obj.left)).hom.app M) ≫
          (SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
            c.i (𝟙 X.obj.left) r.hom d.i
            (r.i_hom.trans (Category.id_comp _).symm)).app M) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.canonicalBridge.push l E r.hom).inv.app
          ((SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) c.i).obj M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((Operations.push l E o r.hom).map
          ((z.canonicalBridge.shriek l E c.i).inv.app M)) ≫
      (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom ≫
      RW.functor.map ((ProperOpenPush A r.hom).map (fixedShriek l E o m c.i M).hom) =
      (shriek l E o m d.i M).hom ≫
        RW.functor.map
          ((ProperOpenShriek A d.i).map
            (((ordinary D A).sId X).inv.app (input l E m X.obj.left M)) ≫
            (properOpenMate A c.i (𝟙 X.obj.left) r.hom d.i
              (r.i_hom.trans (Category.id_comp _).symm)).app
                (input l E m X.obj.left M)) := by
  dsimp only
  letI := c.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  letI := d.quasiCompact_openImmersion (inferInstance : QuasiCompact f.hom.left)
  have hc := canonicalEvaluation l E D o z m c d r M
  have ht := congrArg
    (fun t ↦
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
          ((Operations.shriek l E o d.i).map
            ((z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
              SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
                X.obj.left).inv.app M)) ≫
        t ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((z.canonicalBridge.push l E r.hom).inv.app
          ((SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) c.i).obj M)) ≫
      (coefficientSequenceDerivedEvaluation l E d.Z m).map
        ((Operations.push l E o r.hom).map
          ((z.canonicalBridge.shriek l E c.i).inv.app M)) ≫
      (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom ≫
      (sfIntrinsicDerivedEquivalence d.Z
        (Padic.coefficientExtensionRing l E (m + 1))).functor.map
        ((ProperOpenPush
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) r.hom).map
            (fixedShriek l E o m c.i M).hom)) hc
  let V := coefficientSequenceDerivedEvaluation l E d.Z m
  let α := z.canonicalBridge.push l E r.hom
  let β := z.canonicalBridge.shriek l E c.i
  have hcan := congrArg V.map (iso_naturality_cancel α β M)
  have hcan₀ :
      V.map (α.hom.app ((Operations.shriek l E o c.i).obj M)) ≫
          V.map ((SemilinearProperOpen.R (scalarRings l E)
            (scalarTransitions l E) r.hom).map (β.hom.app M)) ≫
        V.map (α.inv.app ((SemilinearProperOpen.J (scalarRings l E)
          (scalarTransitions l E) c.i).obj M)) ≫
      V.map ((Operations.push l E o r.hom).map (β.inv.app M)) = V.map (𝟙 _) := by
    simpa only [V, α, β, Functor.map_comp, Category.assoc] using hcan
  have hcan' :
      V.map (α.hom.app ((Operations.shriek l E o c.i).obj M)) ≫
          V.map ((SemilinearProperOpen.R (scalarRings l E)
            (scalarTransitions l E) r.hom).map (β.hom.app M)) ≫
        V.map (α.inv.app ((SemilinearProperOpen.J (scalarRings l E)
          (scalarTransitions l E) c.i).obj M)) ≫
      V.map ((Operations.push l E o r.hom).map (β.inv.app M)) = 𝟙 _ :=
    hcan₀.trans (V.map_id _)
  have hcore := rhsCore l E D o z m c d r M
  have hmid := congrArg
    (fun t ↦
      V.map ((Operations.shriek l E o d.i).map
        ((z.canonicalBridge.push l E (𝟙 X.obj.left) ≪≫
          SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E)
            X.obj.left).inv.app M)) ≫
      V.map ((z.properOpen.gamma c.i (𝟙 X.obj.left) r.hom d.i
        (r.i_hom.trans (Category.id_comp _).symm)).app M) ≫ t ≫
      (push l E o m r.hom ((Operations.shriek l E o c.i).obj M)).hom ≫
      (sfIntrinsicDerivedEquivalence d.Z
        (Padic.coefficientExtensionRing l E (m + 1))).functor.map
        ((ProperOpenPush
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) r.hom).map
            (fixedShriek l E o m c.i M).hom)) hcan'
  calc
    _ = _ := by simpa only [Functor.map_comp, Category.assoc] using ht.symm
    _ = _ := by simpa only [V, α, β, Functor.map_comp, Category.assoc] using hmid
    _ = _ := by simpa [V] using hcore

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
