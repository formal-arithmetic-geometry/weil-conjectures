/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorCoherenceData
public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletion
import WeilConjectures.SixFunctors.CompactSupportCoefficientTensor.ProjectionTensorCoefficientComparison
import WeilConjectures.AlgebraicGeometry.FiniteFieldPrimePowerUnit
import WeilConjectures.SixFunctors.OpenRoosRestriction.OpenRoosRestrictionDescent
import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorOrdinaryTransport
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Open-factor data in the fixed coefficient presentation

The completed projection and its restriction, realized on the fixed tensor models
(`openFactorProjectionRealization`).

## Implementation details

Quotient completion commutes with open restriction compatibly with its unit
(`completion_star_iso`, from the strict Roos descent `OpenRoosRestriction.restrictionDescent`
transported along `openFactorOrdinaryTransport`). Writing the completed tensor as the completion
of the ordinary one, this gives the restriction isomorphism and its `chi` compatibility on all
pairs. The `gamma` compatibility cancels the `chi` map, invertible on constructible pairs, and
reduces to the ordinary identity `star_openProjectionIso_hom`, a triangle identity of the open
adjunction.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, 3.4.10, 6.5.5, 6.5.8
* Stacks Project, Tags 099N, 09BN, 09BP, 0GL1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section CompletionRestriction

/-- Fixes the site universe ahead of imported instances with a free universe parameter. -/
private local instance (priority := 30000) proEtSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private local instance (priority := 30000) proEtSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  IntegralOpenReduction.openAbSheafify.{u, u}

private local instance (priority := 30000) proEtLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  IntegralOpenReduction.openAbLocallyBijective.{u, u}

/-- Exactness of the normalized open restriction, from the slice restriction and the
coefficient equivalence. -/
private theorem restrictionLimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations.{u, u} l E j) :
    PreservesFiniteLimits (IntegralOpenReduction.restriction.{u, u} l E j o) := by
  have := SheafOfModules.localizedSystemRestrictionLimits.{u + 1, u, u}
    (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j)
  exact comp_preservesFiniteLimits
    (SheafOfModules.localizedSystemRestriction.{u + 1, u, u}
      (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j))
    o.integral.inverse

private theorem restrictionColimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations.{u, u} l E j) :
    PreservesFiniteColimits (IntegralOpenReduction.restriction.{u, u} l E j o) := by
  have := SheafOfModules.localizedSystemRestrictionColimits.{u + 1, u, u}
    (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j)
  exact comp_preservesFiniteColimits
    (SheafOfModules.localizedSystemRestriction.{u + 1, u, u}
      (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j))
    o.integral.inverse

/-- Quotient completion commutes with restriction to an open, compatibly with the
completion units. -/
theorem completion_star_iso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations.{u, u} l E j) :
    ∃ ρ : C l E X ⋙ star l E j ≅ star l E j ⋙ C l E U,
      ∀ M : D l E X, (star l E j).map ((eta l E X).app M) ≫ ρ.hom.app M =
        (eta l E U).app ((star l E j).obj M) := by
  have := restrictionLimits l E j o
  have := restrictionColimits l E j o
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  obtain ⟨_, _, _, rho, _, hrho, _⟩ := OpenRoosRestriction.restrictionDescent l E j o d hd
  obtain ⟨_, ⟨σ₀⟩⟩ := openFactorOrdinaryTransport l E j o
  let σ : IntegralOpenReduction.star.{u, u} l E j o ≅ star l E j :=
    Functor.mapDerivedCategoryNatIso σ₀
  refine ⟨Functor.isoWhiskerLeft (C l E X) σ.symm ≪≫ rho ≪≫
    Functor.isoWhiskerRight σ (C l E U), fun M ↦ ?_⟩
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  erw [σ.inv.naturality_assoc]
  erw [reassoc_of% (hrho M)]
  erw [← (eta l E U).naturality (σ.hom.app M)]
  simp

end CompletionRestriction

/-- The ordinary open projection, restricted to the open and followed by the restriction
counit, is the canonical tensor-pullback comparison. -/
theorem star_openProjectionIso_hom {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    (od : Open l E j) (tU : Tensor l E U) (tX : Tensor l E X) (K : D l E U) (P : D l E X) :
    (star l E j).map (openProjectionIso (completed l E) j tU.ordinary tX.ordinary K P).hom ≫
        od.restrictionIso.hom.app (tU.ordinary.tensor.obj (K, (star l E j).obj P)) =
      (proEtaleCanonicalTensorComparison j ((completed l E).ring X) ((completed l E).ring U)
        ((completed l E).pull j) tX.ordinary tU.ordinary).hom.app ((J l E j).obj K, P) ≫
        tU.ordinary.tensor.map (Prod.mkHom (od.restrictionIso.hom.app K) (𝟙 _)) := by
  let adj := openDerivedAdjunction (completed l E) j
  have hu (K : D l E U) : adj.unit.app K = od.restrictionIso.inv.app K :=
    (Iso.comp_hom_eq_id (od.restrictionIso.app K)).1 (od.section_unit K)
  let can := proEtaleCanonicalTensorComparison j ((completed l E).ring X)
    ((completed l E).ring U) ((completed l E).pull j) tX.ordinary tU.ordinary
  let I := openProjectionInverse (completed l E) j tU.ordinary tX.ordinary K P
  have h1 : adj.unit.app (tU.ordinary.tensor.obj (K, (star l E j).obj P)) ≫
      (star l E j).map I = tU.ordinary.tensor.map (Prod.mkHom (adj.unit.app K) (𝟙 _)) ≫
        can.inv.app ((J l E j).obj K, P) := by
    have h := (adj.homEquiv _ _).apply_symm_apply (tU.ordinary.tensor.map
      (Prod.mkHom (adj.unit.app K) (𝟙 ((star l E j).obj P))) ≫ can.inv.app ((J l E j).obj K, P))
    rwa [Adjunction.homEquiv_unit] at h
  have : IsIso I := openProjectionInverse_isIso (completed l E) j tU.ordinary tX.ordinary K P
  have hp : (openProjectionIso (completed l E) j tU.ordinary tX.ordinary K P).hom = inv I := rfl
  rw [hp, Functor.map_inv, IsIso.inv_comp_eq,
    ← cancel_epi (od.restrictionIso.inv.app (tU.ordinary.tensor.obj (K, (star l E j).obj P))),
    Iso.inv_hom_id_app, ← hu, reassoc_of% h1, hu, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, prod_comp, Iso.inv_hom_id_app, Category.id_comp]
  exact (tU.ordinary.tensor.map_id _).symm

/-- The completed tensor unit followed by the completed open projection `gamma` is the
ordinary open projection followed by the extension of the completed tensor unit. -/
theorem chi_comp_gamma {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    (o : Open l E j) (tU : Tensor l E U) (tX : Tensor l E X) (K : D l E U) (P : D l E X) :
    (tX.chi l E).app ((J l E j).obj K, P) ≫ gamma l E o tU tX K P =
      (openProjectionIso (completed l E) j tU.ordinary tX.ordinary K P).hom ≫
        (J l E j).map ((tU.chi l E).app (K, (star l E j).obj P)) := by
  simp only [Tensor.chi, gamma, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← (eta l E X).naturality_assoc]
  simpa only [Functor.id_map, Functor.comp_obj, Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦
      (openProjectionIso (completed l E) j tU.ordinary tX.ordinary K P).hom ≫ f ≫
        (J l E j).map (tU.comparison.hom.app (K, (star l E j).obj P)))
      (o.unit_commutes (tU.ordinary.tensor.obj (K, (star l E j).obj P)))

/-- Restriction to the open commutes with the completed tensor product, compatibly with the
tensor completion units and, on constructible inputs, with the completed open projection. -/
theorem openFactorTensorRestriction
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (o : IntegralOpenReduction.Operations.{u, u} l E j) (tU : Tensor l E U) (tX : Tensor l E X)
    (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
    [U.Over (Spec (.of F.k))] [X.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    (od : Open l E j) :
    ∃ r : integralCompletedTensor.{u, u} l E X ⋙ star l E j ≅
        ((star l E j).prod (star l E j)) ⋙ integralCompletedTensor.{u, u} l E U,
      (∀ M N : D l E X, (star l E j).map ((tX.chi l E).app (M, N)) ≫ r.hom.app (M, N) =
          (proEtaleCanonicalTensorComparison j ((completed l E).ring X)
            ((completed l E).ring U) ((completed l E).pull j)
            tX.ordinary tU.ordinary).hom.app (M, N) ≫
              (tU.chi l E).app ((star l E j).obj M, (star l E j).obj N)) ∧
      (∀ (K : D l E U) (P : D l E X), sfIntegralConstructible l E U K →
        sfIntegralConstructible l E X P →
        (star l E j).map (gamma l E od tU tX K P) ≫
            od.restrictionIso.hom.app ((integralCompletedTensor.{u, u} l E U).obj
              (K, (star l E j).obj P)) =
          r.hom.app ((J l E j).obj K, P) ≫
            (integralCompletedTensor.{u, u} l E U).map
              (Prod.mkHom (od.restrictionIso.hom.app K) (𝟙 _))) := by
  obtain ⟨ρ, hρ⟩ := completion_star_iso l E j o
  let can := proEtaleCanonicalTensorComparison j ((completed l E).ring X)
    ((completed l E).ring U) ((completed l E).pull j) tX.ordinary tU.ordinary
  let r : integralCompletedTensor.{u, u} l E X ⋙ star l E j ≅
      ((star l E j).prod (star l E j)) ⋙ integralCompletedTensor.{u, u} l E U :=
    Functor.isoWhiskerRight tX.comparison.symm (star l E j) ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft tX.ordinary.tensor ρ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight can (C l E U) ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ tU.comparison
  have hr (M N : D l E X) : r.hom.app (M, N) =
      (star l E j).map (tX.comparison.inv.app (M, N)) ≫
        ρ.hom.app (tX.ordinary.tensor.obj (M, N)) ≫ (C l E U).map (can.hom.app (M, N)) ≫
        tU.comparison.hom.app ((star l E j).obj M, (star l E j).obj N) := by
    simp [r]
  have hunit (M N : D l E X) :
      (star l E j).map ((tX.chi l E).app (M, N)) ≫ r.hom.app (M, N) =
        can.hom.app (M, N) ≫ (tU.chi l E).app ((star l E j).obj M, (star l E j).obj N) := by
    rw [hr]
    simp only [Tensor.chi, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp,
      Category.assoc]
    rw [← Functor.map_comp_assoc (star l E j) (tX.comparison.hom.app (M, N)),
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      reassoc_of% (hρ (tX.ordinary.tensor.obj (M, N)))]
    erw [(eta l E U).naturality_assoc]
    rfl
  refine ⟨r, hunit, fun K P hK hP ↦ ?_⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of F.k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of F.k))
  have : IsNoetherian X := {}
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (AlgebraicGeometry.ProEtale.finiteFieldPrime_isUnit_residueField F l hl
      (X ↘ Spec (.of F.k)) x).invertible
  have : IsIso ((tX.chi l E).app ((J l E j).obj K, P)) :=
    ProjectionTensorCoefficient.completion_isIso l E X tX ⟨_, od.constructible K hK⟩ ⟨P, hP⟩
  rw [← cancel_epi ((star l E j).map ((tX.chi l E).app ((J l E j).obj K, P))),
    ← Functor.map_comp_assoc, chi_comp_gamma, reassoc_of% (hunit _ _), Functor.map_comp,
    Category.assoc]
  erw [od.restrictionIso.hom.naturality]
  rw [reassoc_of% (star_openProjectionIso_hom l E od tU tX K P)]
  erw [(tU.chi l E).naturality]
  exact (Category.assoc _ _ _).symm

/-- Realize the completed projection and restriction on the fixed tensor models. -/
theorem openFactorProjectionRealization
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (o : IntegralOpenReduction.Operations l E j)
    (st : IntegralOpenReduction.TensorComparison l E j o)
    (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
    (c : IntegralOpenReduction.Comparison l E j o SX SU st)
    (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)
    (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
    [U.Over (Spec (.of F.k))] [X.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [j.IsOver (Spec (.of F.k))]
    (od : Open l E j)
    (_hc : OpenProjectionRoos.Completion l E j o SX SU AX AU st m c q) :
    (∀ M N : D l E X, sfIntegralConstructible l E X M →
      sfIntegralConstructible l E X N → IsIso ((q.tensorX.chi l E).app (M, N))) ∧
    (∀ M N : D l E U, sfIntegralConstructible l E U M →
      sfIntegralConstructible l E U N → IsIso ((q.tensorU.chi l E).app (M, N))) ∧
    ∃ r : integralCompletedTensor.{u, u} l E X ⋙ star l E j ≅
        ((star l E j).prod (star l E j)) ⋙ integralCompletedTensor.{u, u} l E U,
      (∀ M N : D l E X, sfIntegralConstructible l E X M →
        sfIntegralConstructible l E X N →
        (star l E j).map ((q.tensorX.chi l E).app (M, N)) ≫ r.hom.app (M, N) =
          (proEtaleCanonicalTensorComparison j ((completed l E).ring X)
            ((completed l E).ring U) ((completed l E).pull j)
            q.tensorX.ordinary q.tensorU.ordinary).hom.app (M, N) ≫
              (q.tensorU.chi l E).app ((star l E j).obj M, (star l E j).obj N)) ∧
      (∀ (K : D l E U) (P : D l E X), sfIntegralConstructible l E U K →
        sfIntegralConstructible l E X P →
        (star l E j).map (gamma l E od q.tensorU q.tensorX K P) ≫
            od.restrictionIso.hom.app ((integralCompletedTensor.{u, u} l E U).obj
              (K, (star l E j).obj P)) =
          r.hom.app ((J l E j).obj K, P) ≫
            (integralCompletedTensor.{u, u} l E U).map
              (Prod.mkHom (od.restrictionIso.hom.app K) (𝟙 _))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of F.k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of F.k))
  have : IsNoetherian X := {}
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of F.k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of F.k))
  have : IsNoetherian U := {}
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (AlgebraicGeometry.ProEtale.finiteFieldPrime_isUnit_residueField F l hl
      (X ↘ Spec (.of F.k)) x).invertible
  let : ∀ x : U, Invertible (l : U.residueField x) := fun x ↦
    (AlgebraicGeometry.ProEtale.finiteFieldPrime_isUnit_residueField F l hl
      (U ↘ Spec (.of F.k)) x).invertible
  exact ⟨fun M N hM hN ↦
      ProjectionTensorCoefficient.completion_isIso l E X q.tensorX ⟨M, hM⟩ ⟨N, hN⟩,
    fun M N hM hN ↦
      ProjectionTensorCoefficient.completion_isIso l E U q.tensorU ⟨M, hM⟩ ⟨N, hN⟩,
    (openFactorTensorRestriction l E j o q.tensorU q.tensorX F hl od).imp
      fun _ h ↦ ⟨fun M N _ _ ↦ h.1 M N, h.2⟩⟩

end WeilConjectures.OpenFactorCoherence
