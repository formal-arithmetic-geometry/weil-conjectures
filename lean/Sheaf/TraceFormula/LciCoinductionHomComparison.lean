/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.TraceFormula.LciCoinductionComplexHom
public import Sheaf.AlgebraicGeometry.SheafExt
public import WeilConjectures.Algebra.Homology.HomComplexComponents

/-! # The canonical underlying Hom comparison for a Koszul chart

Source: Stacks Project, Tags 0BUZ, 0BV1 and 0A95
(blueprint: def-trf-lci-coinduction-hom-comparison).
The comparison is fixed on K-injective representatives by the ordinary evaluation-normalized
coinduction comparison and projection onto source degree zero in the Hom complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option Elab.async false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable [∀ Z : RingedSpace.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z))]

attribute [local instance] LciKoszulDuality.schemeDerived LciKoszulDuality.imageRingDerived
  LciKoszulDuality.imageRingInjectives

/-- The underlying derived coinduction functor, forgetting the quotient action exactly.
Source: Stacks 0BV1 (blueprint: def-trf-lci-coinduction-hom-comparison). -/
def coinductionUnderlyingHom {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) (h : PolynomialChartExactData T.chart.i) :
    schemeDerivedCategory T.chart.P ⥤ schemeDerivedCategory T.chart.P :=
  polynomialChartDerivedHom T.chart.i h ⋙ T.scalarDerived h

/-- The ambient RHom functor from the quotient module in degree zero.
Source: Stacks 0BV1 (blueprint: def-trf-lci-coinduction-hom-comparison). -/
def coinductionInternalHom {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) :
    schemeDerivedCategory T.chart.P ⥤ schemeDerivedCategory T.chart.P :=
  (Functor.curry.obj (derivedInternalHom.{u, w}
    (Opens.grothendieckTopology T.chart.P) T.chart.P.sheaf)).obj
      (op ((DerivedCategory.singleFunctor.{w} (SheafOfModules.{u}
        (moduleRings T.chart.P.toRingedSpace)) 0).obj T.quotientModule))

/-- Canonical representative comparison for RHom, using its defining localization
factorization and the same functorial K-injective replacement as its definition.
Source: Stacks 0A95 (blueprint: def-trf-lci-coinduction-hom-comparison). -/
@[no_expose] def coinductionInternalHomFactor {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) (K : CochainComplex (SheafOfModules.{u}
      (moduleRings T.chart.P.toRingedSpace)) ℤ) :
    haveI : IsGrothendieckAbelian.{u}
        (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace)) :=
      SheafOfModules.isGrothendieckAbelian _
    (coinductionInternalHom T).obj (DerivedCategory.Q.{w}.obj K) ≅
      DerivedCategory.Q.{w}.obj (homComplex.{u, u, u, u} (R := T.chart.P.sheaf)
        ((CochainComplex.singleFunctor (SheafOfModules.{u}
          (moduleRings T.chart.P.toRingedSpace)) 0).obj T.quotientModule)
        ((CochainComplex.kInjectiveResolutionFunctor.{u} _).obj K)) :=
  haveI : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  (Localization.fac _ (derivedInternalHom_inverts.{u, w}
    (Opens.grothendieckTopology T.chart.P) T.chart.P.sheaf _
    (CochainComplex.toKInjectiveResolution.{u} _)
    (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} _ M⟩))
    ((DerivedCategory.Q.{w}).op.prod DerivedCategory.Q.{w})).app
      (op ((CochainComplex.singleFunctor (SheafOfModules.{u}
        (moduleRings T.chart.P.toRingedSpace)) 0).obj T.quotientModule), K)

/-- The comparison on a K-injective representative, before descending to the localization.
The ordinary comparison and single-source projection fix its scale.
Source: Stacks 0BV1 (blueprint: def-trf-lci-coinduction-hom-comparison). -/
@[no_expose] def coinductionUnderlyingHomFactor {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) (h : PolynomialChartExactData T.chart.i)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace))
      ℤ) [I.IsKInjective] :
    ((coinductionUnderlyingHom T) h).obj (DerivedCategory.Q.{w}.obj I) ≅
      DerivedCategory.Q.{w}.obj (homComplex.{u, u, u, u} (R := T.chart.P.sheaf)
        ((CochainComplex.singleFunctor (SheafOfModules.{u}
          (moduleRings T.chart.P.toRingedSpace)) 0).obj T.quotientModule) I) := by
  letI : HasDerivedCategory.{w} (SheafOfModules.{u} T.chart.P.ringCatSheaf) :=
    inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace)))
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
    (((TopologicalSpace.Opens.map T.chart.i.base).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology T.chart.P)
      (Opens.grothendieckTopology T.chart.U.toScheme)).obj
        T.chart.U.toScheme.ringCatSheaf)) :=
    inferInstanceAs (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace T.chart.i))))
  letI : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI : (polynomialChartCoinduction T.chart.i).Additive := h.additive
  letI : PreservesFiniteLimits T.scalars := h.limits
  letI : PreservesFiniteColimits T.scalars := h.colimits
  letI : T.scalars.Additive :=
    SheafOfModules.instAdditiveRestrictScalars T.chart.i.toRingCatSheafHom
  let e₁ := (T.scalarDerived h).mapIso
    ((polynomialChartCoinduction T.chart.i).rightDerivedFunctorObjQIso I)
  let e₂ := T.scalars.mapDerivedCategoryFactors.app
    (((polynomialChartCoinduction T.chart.i).mapHomologicalComplex (.up ℤ)).obj I)
  exact e₁ ≪≫ e₂ ≪≫ DerivedCategory.Q.{w}.mapIso
    ((coinductionComplexIso T h).app I)

/-- Unique descent of the specified representative comparison. Source: Stacks 0BV1, 0A95
(blueprint: def-trf-lci-coinduction-hom-comparison).
Proof: For any complex K replace it by its functorial K-injective resolution I(K).
The right-derived-functor unit identifies coinduction with termwise coinduction on I(K).
Exact scalar restriction commutes with localization. The ordinary evaluation-normalized
comparison followed by the inverse single-source projection identifies this complex
with Hom(A[0],I(K)). The defining localization factorization of derivedInternalHom
identifies the latter with RHom(A[0],QK). These identifications are natural in K:
projection and the ordinary comparison are natural, and the resolution unit is natural.
Every quasi-isomorphism is inverted. Descend by the localization universal property;
full faithfulness of precomposition with Q proves uniqueness of this specified map. -/
theorem existsUnique_coinductionHomComparison {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) (h : PolynomialChartExactData T.chart.i) :
    haveI : IsGrothendieckAbelian.{u}
        (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace)) :=
      SheafOfModules.isGrothendieckAbelian _
    ∃! e : (coinductionUnderlyingHom T) h ≅ (coinductionInternalHom T),
      ∀ K : CochainComplex (SheafOfModules.{u} (moduleRings T.chart.P.toRingedSpace)) ℤ,
        e.hom.app (DerivedCategory.Q.{w}.obj K) ≫ ((coinductionInternalHomFactor T) K).hom =
          ((coinductionUnderlyingHom T) h).map (DerivedCategory.Q.{w}.map
            ((CochainComplex.toKInjectiveResolution.{u} _).app K)) ≫
            ((coinductionUnderlyingHomFactor T) h
              ((CochainComplex.kInjectiveResolutionFunctor.{u} _).obj K)).hom := by
  sorry

/-- The uniquely normalized comparison. Only its universal-property proof is postponed;
its statement determines the isomorphism, including its scalar, on every representative.
Source: Stacks 0BV1, 0A95 (blueprint: def-trf-lci-coinduction-hom-comparison). -/
@[no_expose] def coinductionHomComparison {X S : Scheme.{u}} {f : X ⟶ S} {d : ℕ}
    (T : LciKoszulDuality.Chart f d) (h : PolynomialChartExactData T.chart.i) :
    (coinductionUnderlyingHom T) h ≅ (coinductionInternalHom T) :=
  ((existsUnique_coinductionHomComparison T) h).choose

end AlgebraicGeometry
