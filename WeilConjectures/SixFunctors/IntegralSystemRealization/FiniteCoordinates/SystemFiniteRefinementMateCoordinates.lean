/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteEvaluationCoordinates
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateCanonical
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateLhsNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateRhsNormalization

/-! # Finite evaluation of the identity-normalized proper/open factor

Source: Stacks 03DI, 07A7, 0F7B and the compactification-independence paragraph
of prop-sf-pf-coherence.proof.md.
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

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  scalarReductionTargetDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

/-- The proper/open factor of a refinement, with its identity direct image, in one
finite evaluation. There is no outer proper direct image or support compositor.

Source: Stacks 03DI, 07A7 and 0F7B; the identity and proper/open factors in the
finite-evaluation step of prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-finite-refinement-mate-coordinates).

Proof: substitute z.properOpen.canonical to express the whole-system gamma through
its section-normalized canonical bridge. Apply semilinear gamma_evaluation. The
evaluation comparisons for open extension are inverse-image adjunction mates;
those for direct image preserve its unit and counit. Adjoint uniqueness therefore
identifies their bridge transports with the given o evaluations. The same argument
for the identity morphism transports the inverse canonical system identity to the
finite identity direct image. The canonical intrinsic coefficient equivalence
preserves these maps: open extension is its specified adjoint transport and the
direct comparison is normalized on scalar-unit sections and K-injectives. Thus the
evaluated gamma is the intrinsic realization of the fixed finite proper/open mate.
Naturality moves the inverse identity through its open comparison. Cancel the
intermediate coefficient unit-counit pair. The displayed square follows without
inverting gamma and without claiming evaluations detect equality. Identity
refinements, zero inputs and empty opens obey the same mate identities. -/
theorem refinementMate (D : FiniteFieldDatum.{u}) (o : Operations l E)
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
  have hl := lhsNormalization l E D o z m c d r M
  have hc := canonicalEvaluation l E D o z m c d r M
  have hr := rhsNormalization l E D o z m c d r M
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
  calc
    _ = _ := hl
    _ = _ := by simpa only [Functor.map_comp, Category.assoc] using ht
    _ = _ := hr

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
