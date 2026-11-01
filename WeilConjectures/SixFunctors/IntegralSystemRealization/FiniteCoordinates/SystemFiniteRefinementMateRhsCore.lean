/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateCanonical
public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteEvaluationCoordinates
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateRhsBridgeCancellation
import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteRefinementMateRhsCoreFiniteMate
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus

/-! # Core finite proper/open mate transport

Source: Stacks 00YV and 0F7B; the finite-evaluation step of
prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-system-finite-refinement-mate-rhs-normalization-core).
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

/-- The finite proper/open mate transport after the canonical bridge factors have
been cancelled.  It is the direct evaluated mate equation used by right
normalization; the omitted bridge factors are handled by naturality of the
canonical push and shriek isomorphisms.

Source: Stacks 00YV and 0F7B; coefficient-equivalence triangle identities and
finite proper/open mate normalization.  Expand the finite push and shriek
comparisons, apply the evaluated proper/open mate compatibility, and cancel the
intrinsic coefficient equivalence unit and counit.  This argument is functorial
and includes identity refinements, zero inputs, and empty opens.
(blueprint: lem-sf-system-finite-refinement-mate-rhs-normalization-core).
-/
theorem rhsCore (D : FiniteFieldDatum.{u}) (o : Operations l E)
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
    (shriek l E o m d.i M).hom ≫
      RW.functor.map
        ((ProperOpenShriek A d.i).map
          (((ordinary D A).sId X).inv.app (input l E m X.obj.left M)) ≫
          (properOpenMate A c.i (𝟙 X.obj.left) r.hom d.i
            (r.i_hom.trans (Category.id_comp _).symm)).app
              (input l E m X.obj.left M)) := by
  have hb := rhsCoreBridgeCancellation l E D o z m c d r M
  have hf := rhsCoreFiniteMate l E D o z m c d r M
  simpa only [Category.assoc] using hb.trans hf

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
