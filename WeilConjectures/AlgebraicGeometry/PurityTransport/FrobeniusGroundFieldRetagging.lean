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

/-! # Purity and geometric-Frobenius ground-field retagging

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-def-ops/sk-thm-sf-package/thm-pur-weil-equivariance-of-purity-and-trace.proof.md,
Steps 1--2 (blueprint: lem-pur-frobenius-ground-field-retagging).

The retagged datum below is the actual same scheme with both structure maps
postcomposed by the recorded geometric Frobenius. The family and its Brown
adjunctions are the recorded transport constructions; the displayed purity
maps are `semilinearGamma`, hence are fixed by their counit equations rather
than supplied as arbitrary isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.PurityTransport
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The geometric Frobenius `gamma = Frob_q` of def-pur-scheme-geometric-frobenius,
used to retag the two structure morphisms (the same equivalence as in
`FiniteFieldDatum.purityGaloisMap`).
Source: thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Step 1
(blueprint: lem-pur-frobenius-ground-field-retagging). -/
noncomputable def groundFieldGamma (D : WeilConjectures.FiniteFieldDatum.{u}) :
    D.k ≃ₐ[D.k₀] D.k :=
  @FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
    (Fintype.ofFinite D.k₀) _ _ _

/-- Retagging changes only the structure morphism of an object of `Over`:
`T^<gamma>` is `T` with structure map `Spec(gamma) ∘ a_T`.
Source: thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Step 1
(blueprint: lem-pur-frobenius-ground-field-retagging). -/
noncomputable def groundFieldRetagOver (D : WeilConjectures.FiniteFieldDatum.{u})
    (T : Over (Spec (.of D.k))) : Over (Spec (.of D.k)) :=
  (Over.map (Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom))).obj T

/-- `Spec(gamma)` is an isomorphism, since `gamma` is a ring automorphism.
Source: thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Step 1
(blueprint: lem-pur-frobenius-ground-field-retagging). -/
instance groundFieldRetagIso (D : WeilConjectures.FiniteFieldDatum.{u}) :
    IsIso (Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom)) := by
  let e := (groundFieldGamma D).toRingEquiv.toCommRingCatIso
  let _ : IsIso (CommRingCat.ofHom (groundFieldGamma D).toRingHom) := e.isIso_hom
  infer_instance

/-- The smooth datum obtained by retagging both structure maps by `gamma`: same
underlying schemes, morphism `f`, relative dimension and compactification; finite
type, quasi-compactness, separatedness and smoothness are proved, not assumed.
Source: thm-pur-weil-equivariance-of-purity-and-trace.proof.md, Step 1
(blueprint: lem-pur-frobenius-ground-field-retagging). -/
noncomputable def groundFieldRetagSmooth
    (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D) : SmoothDatum D := by
  have hOver : s.map ≫ s.Y.hom = s.X.hom :=
    (inferInstance : s.map.IsOver (Spec (.of D.k))).1
  let X := groundFieldRetagOver D s.X
  let Y := groundFieldRetagOver D s.Y
  letI : X.left.Over (Spec (.of D.k)) := ⟨X.hom⟩
  letI : Y.left.Over (Spec (.of D.k)) := ⟨Y.hom⟩
  haveI : LocallyOfFiniteType X.hom := by
    change LocallyOfFiniteType
      (s.X.hom ≫ Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom))
    infer_instance
  haveI : QuasiCompact X.hom := by
    change QuasiCompact
      (s.X.hom ≫ Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom))
    infer_instance
  haveI : IsSeparated X.hom := by
    change IsSeparated
      (s.X.hom ≫ Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom))
    infer_instance
  haveI : LocallyOfFiniteType Y.hom := by
    change LocallyOfFiniteType
      (s.Y.hom ≫ Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom))
    infer_instance
  haveI : QuasiCompact Y.hom := by
    change QuasiCompact
      (s.Y.hom ≫ Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom))
    infer_instance
  haveI : IsSeparated Y.hom := by
    change IsSeparated
      (s.Y.hom ≫ Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom))
    infer_instance
  let fγO : X ⟶ Y := Over.homMk s.map (by
    change s.map ≫
        (s.Y.hom ≫ Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom)) =
      s.X.hom ≫ Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom)
    simpa only [Category.assoc] using
      congrArg (fun h => h ≫ Spec.map (CommRingCat.ofHom (groundFieldGamma D).toRingHom)) hOver)
  let fγ := fγO.left
  haveI : IsSeparated fγ := by change IsSeparated s.map; infer_instance
  haveI : LocallyOfFiniteType fγ := by change LocallyOfFiniteType s.map; infer_instance
  haveI : QuasiCompact fγ := by change QuasiCompact s.map; infer_instance
  haveI : SmoothOfRelativeDimension s.dim fγ := by
    change SmoothOfRelativeDimension s.dim s.map
    infer_instance
  exact { X := X, Y := Y, map := fγ, dim := s.dim, compactification := s.compactification }

end AlgebraicGeometry.ProEtale.PurityTransport
