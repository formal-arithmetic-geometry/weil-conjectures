/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompatibility
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarCompatibility
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAffineGeometry
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem
public import WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Condensed smooth purity and a change of ground-field structure

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-trace/sec-base-change-and-composition/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc.proof.md, Opening coefficient-transport,
Orientation and Tensor map paragraphs
(blueprint: lem-pur-condensed-ground-field-structure-invariance).

The statement records the canonical comparison after retagging the same underlying
geometric data.  The comparison of exceptional targets is required to preserve the
compact-support counit; the displayed equality is therefore equality of the actual
counit-normalized purity maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.PurityTransport

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The same smooth datum with both structural maps changed by `Spec σ`: the
underlying schemes, the morphism `f`, its relative dimension and its compactification
are kept. This is the node's `X^σ`, `Y^σ`, `f^σ`; the finite-type, separatedness and
smoothness instances are those of step 1 of the node's proof.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-trace/sec-base-change-and-composition/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc.proof.md, Opening coefficient-transport
paragraph and Tensor map paragraph (same underlying compactification)
(blueprint: lem-pur-condensed-ground-field-structure-invariance). -/
def retagSmoothDatum
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (σ : D.k ≃+* D.k)
    (s : SmoothDatum D) : SmoothDatum D := by
  let X := (Over.map (Spec.map (CommRingCat.ofHom σ.toRingHom))).obj s.X
  let Y := (Over.map (Spec.map (CommRingCat.ofHom σ.toRingHom))).obj s.Y
  let f : X.left ⟶ Y.left := s.map
  letI : LocallyOfFiniteType X.hom := by
    simpa [X] using
      (MorphismProperty.comp_mem @LocallyOfFiniteType s.X.hom
        (Spec.map (CommRingCat.ofHom σ.toRingHom)) s.xFinite inferInstance)
  letI : QuasiCompact X.hom := by
    simpa [X] using
      (MorphismProperty.comp_mem @QuasiCompact s.X.hom
        (Spec.map (CommRingCat.ofHom σ.toRingHom)) s.xQuasiCompact inferInstance)
  letI : IsSeparated X.hom := by
    simpa [X] using
      (MorphismProperty.comp_mem @IsSeparated s.X.hom
        (Spec.map (CommRingCat.ofHom σ.toRingHom)) s.xSeparated inferInstance)
  letI : LocallyOfFiniteType Y.hom := by
    simpa [Y] using
      (MorphismProperty.comp_mem @LocallyOfFiniteType s.Y.hom
        (Spec.map (CommRingCat.ofHom σ.toRingHom)) s.yFinite inferInstance)
  letI : QuasiCompact Y.hom := by
    simpa [Y] using
      (MorphismProperty.comp_mem @QuasiCompact s.Y.hom
        (Spec.map (CommRingCat.ofHom σ.toRingHom)) s.yQuasiCompact inferInstance)
  letI : IsSeparated Y.hom := by
    simpa [Y] using
      (MorphismProperty.comp_mem @IsSeparated s.Y.hom
        (Spec.map (CommRingCat.ofHom σ.toRingHom)) s.ySeparated inferInstance)
  letI : f.IsOver (Spec (.of D.k)) := by
    refine ⟨?_⟩
    change f ≫ Y.hom = X.hom
    simpa [X, Y, f, Category.assoc] using
      congrArg (fun q ↦ q ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) s.isOver.1
  letI : IsSeparated f := s.separated
  letI : LocallyOfFiniteType f := s.finiteType
  letI : QuasiCompact f := s.quasiCompact
  letI : SmoothOfRelativeDimension s.dim f := s.smooth
  exact
    { X := X
      Y := Y
      map := f
      dim := s.dim
      compactification := s.compactification }

end AlgebraicGeometry.ProEtale.PurityTransport
