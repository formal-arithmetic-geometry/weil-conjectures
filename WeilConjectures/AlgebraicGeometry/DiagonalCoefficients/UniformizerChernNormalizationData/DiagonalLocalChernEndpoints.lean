/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralKummer
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRootLimitCompatibility
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFiniteRootsCanonicalMap
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernStageTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernStagedArrow

/-! # Unit and line endpoints of a local uniformizer reduction
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the same abelian structure on module sheaves as the exact-derived comparison APIs.
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

namespace UniformizerChernNormalizationData

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory HasDerivedCategory.standard
  Scheme.finiteEtaleTateLine

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

open CategoryTheory.MonoidalCategory MonObj in
/-- The integer-cast map into a ring sheaf is its monoid unit. -/
private theorem integerMap_eq_one (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    diagonalCoefficientIntegerMap X R = η[(completedAbFunctor X).obj R] := by
  let J := Scheme.ProEt.topology X
  apply (sheafToPresheaf _ _).map_injective
  apply sheafify_hom_ext J _ _ ((completedAbFunctor X).obj R).property
  ext V n
  obtain ⟨n⟩ := n
  let S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  have h := ConcreteCategory.congr_hom
    (congr_app (Sheaf.ε_sheafToPresheaf_comp_map_one_sheafCompose J S) V) (ULift.up n)
  have hε : Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) =
      (sheafificationAdjunction J Ab.{u + 1}).unit.app (𝟙_ (X.ProEtᵒᵖ ⥤ Ab.{u + 1})) := by
    change (sheafificationAdjunction J Ab.{u + 1}).unit.app _ ≫
      (sheafToPresheaf J Ab.{u + 1}).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  rw [hε] at h
  change (η[(completedAbFunctor X).obj R]).hom.app V
    ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V (ULift.up n)) = _ at h
  erw [Functor.one_compForget₂_app, AddCommGrpCat.ringMonObj_one_apply] at h
  change (diagonalCoefficientIntegerMap X R).hom.app V
    ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V (ULift.up n)) =
    (η[(completedAbFunctor X).obj R]).hom.app V
    ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V (ULift.up n))
  rw [h, integerMap_sections]

open CategoryTheory.MonoidalCategory MonObj in
/-- The finite integer generator is the unit of the constant finite coefficient ring. -/
private theorem siteIntegralGenerator_one (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DiagonalTrace.siteIntegralGenerator A T ≫ (finiteConstantAbComparison A T).hom =
      η[((sfbConstantRing T).obj (RingCat.of A)).X] := by
  let J := Scheme.ProEt.topology T
  let F := constantSheaf J Ab.{u + 1}
  apply DiagonalTrace.constantAb_ext_one
  have hs := DiagonalTrace.siteIntegralGenerator_section A T (ULift.up 1)
  change (finiteConstantAbComparison A T).hom.hom.app _
    ((DiagonalTrace.siteIntegralGenerator A T).hom.app _ _) = _
  rw [hs, constant_forget_generator]
  have hc : Functor.LaxMonoidal.ε F = 𝟙 _ := by
    change 𝟙 _ ≫ (presheafToSheaf J Ab.{u + 1}).map (𝟙 _) = 𝟙 _
    exact (Category.id_comp _).trans ((presheafToSheaf J Ab.{u + 1}).map_id _)
  change _ = ((Functor.LaxMonoidal.ε F ≫ F.map η[AddCommGrpCat.of A]).hom.app _)
    ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app _ (ULift.up 1))
  rw [hc, Category.id_comp]
  have h := ConcreteCategory.congr_hom (congr_app
    (toSheafify_naturality J
      ((Functor.const T.ProEtᵒᵖ).map η[AddCommGrpCat.of A])) (op (Scheme.ProEt.mk (𝟙 T))))
        (ULift.up (1 : ℤ))
  exact h

open CategoryTheory.MonoidalCategory MonObj in
/-- The unit endpoint carries the completed integer generator to the finite one. -/
theorem localUnitEndpoint_generator (s : UniformizerChernNormalizationData l Y) :
    localCompletedGenerator l (ProjectiveLine Y) ≫ localUnitEndpoint l Y s =
      (SpTowerClasses.integerComparison (ProjectiveLine Y)).inv ≫
        (comparisonUpperStar AddCommGrpCat.{u + 1} (ProjectiveLine Y)).map
          (Etale.ordinaryFiniteIntegralGenerator
            (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)) ≫
        (forgetComparisonIso (ULift.{u + 1} (completedResidue l s.E s.π s.n))
          (ProjectiveLine Y)).hom.app (Etale.ordinaryFiniteConstant
            (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)) ≫
        (cartierForget (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)).map
          (DiagonalTrace.finiteEtaleConstantIso
            (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)).hom := by
  apply (cancel_mono (finiteConstantAbComparison
    (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (ProjectiveLine Y)).hom).mp
  refine Eq.trans ?_ (siteIntegralGenerator_one _ _).symm
  have hv := unitRealization_one l (ProjectiveLine Y) s.completedP
  have hu : localCompletedGenerator l (ProjectiveLine Y) ≫
      ((s.completedP.underlying ≪≫ localCompletedForgetIso l (ProjectiveLine Y)).inv.app _ ≫
        (Mod.forget _).map s.completedP.unitIso.hom) =
      η[condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) (ProjectiveLine Y)] := by
    unfold localCompletedGenerator localCompletedForgetIso
    rw [integerMap_eq_one]
    exact hv
  have hk := s.eP.unit_normalization
  rw [← Category.assoc] at hk
  unfold localUnitEndpoint
  exact comp_unit_chain _ _ _ _ _ _ _ _ _ _ _ hu
    (IsMonHom.one_hom (f := coefficientMap (integralMap l s.E) (ProjectiveLine Y)))
    (IsMonHom.one_hom (f := coefficientMap (quotientMap l s.E s.π s.n) (ProjectiveLine Y)))
    hk (IsMonHom.one_hom (f := s.eP.coefficient.hom.hom))

attribute [local semireducible] QuotientLineRealization in
/-- The line endpoint is the projection of the root limit followed by the root map. -/
theorem localLineEndpoint_eq (s : UniformizerChernNormalizationData l Y) :
    localLineEndpoint l Y s = (localCompletedRoots l (ProjectiveLine Y)).hom ≫
      limit.π (Scheme.proEtaleRootsOfUnityTower (ProjectiveLine Y) l (Fact.out : l.Prime))
        (op s.n) ≫
      cartierProRootMap (ULift.{u + 1} (completedResidue l s.E s.π s.n)) (l ^ (s.n + 1)) s.hA
        (ProjectiveLine Y) (pow_pos (Fact.out : l.Prime).pos _)
        (affineTraceProjectiveInvertible (l ^ (s.n + 1)) Y s.hYpow) := by
  have h₁ := eq_of_heq s.completedP.line_normalization
  have h₂ := diagonalIntegralRoots_transition l (ProjectiveLine Y) s.E s.completedP.roots s.lineP.1
  have h₃ := s.lineP.2.2.normalization
  unfold FiniteRealization.LineNormalization at h₃
  rw [← finiteRoots_toLine_eq_cartierProRootMap s.lineP.2.1 _ s.hA]
  refine Eq.trans ?_ (congrArg (fun t ↦ (localCompletedRoots l (ProjectiveLine Y)).hom ≫ t) h₃)
  refine Eq.trans ?_ (congrArg (fun t ↦ (localCompletedRoots l (ProjectiveLine Y)).hom ≫
    (t ≫ quotientLineMap l s.E s.π s.n (ProjectiveLine Y)) ≫ _) h₂)
  refine Eq.trans ?_ (congrArg (fun t ↦ (localCompletedRoots l (ProjectiveLine Y)).hom ≫
    ((t ≫ integralLineMap l s.E (ProjectiveLine Y)) ≫
      quotientLineMap l s.E s.π s.n (ProjectiveLine Y)) ≫ _) h₁)
  unfold localLineEndpoint
  simp only [Iso.trans_inv, NatTrans.comp_app]
  exact comp_reassoc_seven _ _ _ _ _ _ _

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
