/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.Paper.CompletedExtensionZeroComparison
public import Sheaf.Paper.CompletedPullback
public import Sheaf.Paper.RingedEtaleOriginWitness
import Sheaf.Paper.CompletedFiniteExchangeCoordinates
import all Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import Sheaf.Paper.BoundedConstructibleComplete
import all Sheaf.Paper.AdicCoefficientDatum

/-!
# Finite etale origins after completed-coefficient open extension

Source: blueprint thm-cbc-complete-proetale, proof step 2; Stacks 03DI, 09AF and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open ProEtale.StrictTower in
private def originToC (T : Scheme.{t}) (Λ : Type (t + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    etaleOriginRealization T Λ ≅ C Λ T Λ (RingHom.id Λ) := by
  let r := finiteScalarMap Λ T Λ (RingHom.id Λ)
  have h := finiteScalarMap_unit Λ T Λ (RingHom.id Λ)
  let e := (pbcAssociatedRestriction_exists T Λ Λ
    ((adicLisseForget T).obj (etaleOriginRing T Λ))
    (ProEtale.finiteCoefficientRingSheaf T Λ)
    (etaleOriginScalars T Λ) (ProEtale.finiteCoefficientScalarMap T Λ)
    (RingHom.id Λ) r h).exists.choose
  exact e

private theorem finiteComparison_eq
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) :
    pbcLevelConstantComparison T d n =
      finiteOriginConstantIso T (A ⧸ d.ideal ^ (n + 1)) := by
  apply (pbcLevelConstantComparison_exists T d n).unique
  · exact (pbcLevelConstantComparison_exists T d n).exists.choose_spec
  · intro V b
    exact ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (ProEt.topology T)
        (AdicCoefficients.constants T (A ⧸ d.ideal ^ (n + 1)))) V) b |>.symm

private theorem restriction_exact
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    PreservesFiniteLimits (cbcOpenRestriction d j inferInstance) ∧
      PreservesFiniteColimits (cbcOpenRestriction d j inferInstance) := by
  let G := cbcOpenSiteFunctor j inferInstance
  have : G.IsCocontinuous (ProEt.topology U) (ProEt.topology T) :=
    ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  let F := cbcOpenRestriction d j inferInstance
  let V := SheafOfModules.toSheaf (reductionModuleRing U (d.completedRing U))
  let H := G.sheafPushforwardContinuous AddCommGrpCat.{t + 1}
    (ProEt.topology U) (ProEt.topology T)
  have : PreservesFiniteLimits H := inferInstance
  have : PreservesColimitsOfSize.{t + 1, t + 1} H :=
    (G.sheafAdjunctionCocontinuous AddCommGrpCat.{t + 1}
      (ProEt.topology U) (ProEt.topology T)).leftAdjoint_preservesColimits
  have : PreservesFiniteLimits (F ⋙ V) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.toSheaf (reductionModuleRing T (d.completedRing T)) ⋙ H))
  have : PreservesFiniteColimits (F ⋙ V) :=
    inferInstanceAs (PreservesFiniteColimits
      (SheafOfModules.toSheaf (reductionModuleRing T (d.completedRing T)) ⋙ H))
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F V,
    preservesFiniteColimits_of_reflects_of_preserves F V⟩

-- Localize an exact adjunction directly; no resolution choices are needed.
private def exactAdjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) : F.mapDerivedCategory ⊣ G.mapDerivedCategory := by
  letI : CatCommSq (F.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  letI : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  exact (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory

-- Restriction along a coefficient isomorphism has identity sectionwise round trips.
section RestrictionEquivalence
variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{t + 1}}

private def restrictionRoundTrip (c : R ≅ S) :
    SheafOfModules.restrictScalars.{t + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{t + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private theorem restrictionTriangle (c : R ≅ S) (M : SheafOfModules.{t + 1} S) :
    (SheafOfModules.restrictScalars c.hom).map ((restrictionRoundTrip c).inv.app M) ≫
      (restrictionRoundTrip c.symm).hom.app
        ((SheafOfModules.restrictScalars c.hom).obj M) = 𝟙 _ := by
  ext U x
  rfl

private def restrictionEquivalence (c : R ≅ S) :
    SheafOfModules.{t + 1} S ≌ SheafOfModules.{t + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp := restrictionTriangle c

end RestrictionEquivalence

private theorem finiteRes_additive
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) : (cbcFiniteRes d T n).Additive := by
  change (pbcRestrict (cbcFiniteProjection d T n)).Additive
  infer_instance

private theorem finiteRes_limits
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) : PreservesFiniteLimits (cbcFiniteRes d T n) := by
  change PreservesFiniteLimits (pbcRestrict (cbcFiniteProjection d T n))
  infer_instance

private theorem finiteRes_colimits
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) : PreservesFiniteColimits (cbcFiniteRes d T n) := by
  change PreservesFiniteColimits (pbcRestrict (cbcFiniteProjection d T n))
  infer_instance

attribute [local instance] finiteRes_additive finiteRes_limits finiteRes_colimits

private def finiteReductionAdjunction
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) (n : ℕ) :
    cbcFiniteReduction d T n ⊣ (cbcFiniteRes d T n).mapDerivedCategory := by
  let c := (adicLisseForget T).mapIso (pbcLevelConstantComparison T d n)
  let E := restrictionEquivalence c
  have : E.functor.Additive := by
    change (SheafOfModules.restrictScalars c.hom).Additive
    infer_instance
  have : E.inverse.Additive := by
    change (SheafOfModules.restrictScalars c.inv).Additive
    infer_instance
  have : PreservesFiniteLimits E.functor := inferInstance
  have : PreservesFiniteColimits E.functor := inferInstance
  have : PreservesFiniteLimits E.inverse := inferInstance
  have : PreservesFiniteColimits E.inverse := inferInstance
  let b := exactAdjunction E.toAdjunction
  let a := (scalarDerivedAdjunction_exists T (d.projection T n)).some
  exact (a.comp b).ofNatIsoRight
    (pbcDerivedRestrictComp (d.projection T n)
      (pbcLevelConstantComparison T d n).inv (cbcFiniteProjection d T n) rfl)

open ProEtale.StrictTower in
private def finiteReductionOpenIso
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] (n : ℕ) :
    cbcDerivedOpenShriek d j inferInstance ⋙ cbcFiniteReduction d T n ≅
      cbcFiniteReduction d U n ⋙ (moduleJ (cbcFiniteRing d n) j).mapDerivedCategory := by
  have := (restriction_exact d j).1
  have := (restriction_exact d j).2
  have : (cbcOpenRestriction d j inferInstance).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  let a := exactAdjunction (cbcOpenAdjunction d j inferInstance)
  let b := exactAdjunction (moduleJAdj (cbcFiniteRing d n) j)
  let q : (modulePullback (cbcFiniteRing d n) j).mapDerivedCategory ⋙
      (cbcFiniteRes d U n).mapDerivedCategory ≅
      (cbcFiniteRes d T n).mapDerivedCategory ⋙
        (cbcOpenRestriction d j inferInstance).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (cbcFiniteOpenRestriction d j inferInstance n) ≪≫
        Functor.mapDerivedCategoryCompIso _ _
  exact ((conjugateIsoEquiv (a.comp (finiteReductionAdjunction d T n))
    ((finiteReductionAdjunction d U n).comp b)).symm q.symm).symm

/-- Open extension preserves an independently retained bounded-below etale origin at
each positive quotient. Neither completeness nor a common bound is required.

Source: blueprint thm-cbc-complete-proetale, proof step 2; Stacks 03DI, 09AF and 0GL1
(blueprint: lem-cbc-completed-open-finite-etale-origins).
Proof: fix n and put B = A/I^(n+1). The normalized constants-to-functions
comparison is the same one used by the finite-coordinate reduction functor.
Scalar extension followed by this coefficient equivalence is left adjoint to
restriction along the completed-to-constant projection. Exact open extension is
left adjoint to open restriction, both for completed and constant coefficients.
The existing finite-coordinate comparison identifies the two composites of right
adjoints. Uniqueness of left adjoints therefore identifies reduction of completed
open extension with constant-coefficient open extension of the reduction.
The associated-module restriction comparison identifies the published etale-origin
realization with the finite constant realization H. Extend each retained etale
antecedent by exact etale extension by zero and apply its derived open comparison.
Compose this with extension of the supplied origin isomorphism and the inverse
reduction/open comparison. Exact etale extension preserves the antecedent's own
lower bound. Repeat independently for each n. No common bound or compatibility is
used. All comparisons apply also to the empty open and the zero quotient ring. -/
theorem cbcCompletedOpenFiniteEtaleOrigins
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness U (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction U n).obj K)) :
    Nonempty (∀ n : ℕ, FiniteEtaleOriginWitness T (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction T n).obj ((cbcDerivedOpenShriek d j inferInstance).obj K))) := by
  refine ⟨fun n ↦ ?_⟩
  obtain ⟨L, e⟩ := W n
  let Λ := A ⧸ d.ideal ^ (n + 1)
  letI : TopologicalSpace Λ := ⊥
  letI : DiscreteTopology Λ := ⟨rfl⟩
  let J := Etale.openImmersionLowerShriek (ModuleCat.{t + 1} Λ) j
  let L' := J.mapDerivedCategoryPlus.obj L
  let fU : ProEtale.comparisonUpperStar (ModuleCat.{t + 1} Λ) U ⋙
      etaleOriginRealization U Λ ≅ ProEtale.StrictTower.H Λ U Λ (RingHom.id Λ) :=
    Functor.isoWhiskerLeft _ (originToC U Λ)
  let fT : ProEtale.comparisonUpperStar (ModuleCat.{t + 1} Λ) T ⋙
      etaleOriginRealization T Λ ≅ ProEtale.StrictTower.H Λ T Λ (RingHom.id Λ) :=
    Functor.isoWhiskerLeft _ (originToC T Λ)
  let cU := (Functor.mapDerivedCategoryNatIso fU).app L.obj
  let cT := (Functor.mapDerivedCategoryNatIso fT).app L'.obj
  have hU : cbcFiniteReduction d U n =
      d.reduction U n ⋙ finiteOriginToConstant U Λ := by
    unfold cbcFiniteReduction
    rw [finiteComparison_eq]
    rfl
  have hT : cbcFiniteReduction d T n =
      d.reduction T n ⋙ finiteOriginToConstant T Λ := by
    unfold cbcFiniteReduction
    rw [finiteComparison_eq]
    rfl
  let β := cU.symm ≪≫ e ≪≫ (eqToIso (congrArg (fun F ↦ F.obj K) hU)).symm
  let α := cT ≪≫ (ProEtale.StrictTower.hJ Λ j Λ (RingHom.id Λ)).app L ≪≫
    ((ProEtale.StrictTower.moduleJ (cbcFiniteRing d n) j).mapDerivedCategory).mapIso β ≪≫
    (finiteReductionOpenIso d j n).symm.app K ≪≫
    eqToIso (congrArg (fun F ↦ F.obj ((cbcDerivedOpenShriek d j inferInstance).obj K)) hT)
  exact ⟨L', α⟩

end AlgebraicGeometry.Scheme
