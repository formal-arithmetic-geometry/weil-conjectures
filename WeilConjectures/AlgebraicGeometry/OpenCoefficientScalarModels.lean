/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-! # Exact coefficient extension preserves finite constant models

Source: the rational paragraph of sk-prop-open-coefficients.proof.md in the latest
blueprint (blueprint: lem-sfb-open-rational-scalar-local-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

section
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

private def point_extend (X : Scheme.{u}) :
    Mod.extendScalars a ⋙ (upperStarFromPoint X).mapMod Λ' ≅
      (upperStarFromPoint X).mapMod Λ ⋙ Mod.extendScalars (coefficientMap a X) := by
  let F := upperStarFromPoint X
  let G := (ProEtale.lowerStar Ab.{u + 1} (toSpecZ X)) ⋙ pointLowerStar
  let adj := upperStarFromPointAdjunction X
  let b := (Mod.extendRestrictAdjunction a).comp (adj.mapModAdjunction Λ')
  let c := (adj.mapModAdjunction Λ).comp
    (Mod.extendRestrictAdjunction (F.map a))
  have e : Mod.comap (F.map a) ⋙
      (G.mapMod (F.obj Λ) ⋙ Mod.comap (adj.unitAlgHom Λ)) ≅
      (G.mapMod (F.obj Λ') ⋙ Mod.comap (adj.unitAlgHom Λ')) ⋙ Mod.comap a :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapModComapIso (F.map a)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapCongr (adj.unit.naturality a).symm) ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _) ≪≫
    (Functor.associator _ _ _).symm
  exact b.leftAdjointUniq (c.ofNatIsoRight e)

private theorem local_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (C.f i)).mapIso e).symm ≪≫ eP⟩⟩

private theorem local_extend (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ' X ((Mod.extendScalars (coefficientMap a X)).obj M) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  refine ⟨(Mod.extendScalars a).obj P,
    hP.map (Mod.extendScalars a) (Mod.extendScalarsObjRegularIso a), ⟨?_⟩⟩
  exact ((CondensedRing.pullIso a (C.f i)).app M).symm ≪≫
    (Mod.extendScalars (coefficientMap a (C.X i))).mapIso eP ≪≫
    (point_extend a (C.X i)).symm.app P

private theorem stratified_extend (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ' X ((Mod.extendScalars (coefficientMap a X)).obj M) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun i ↦ ?_⟩
  exact local_iso ((CondensedRing.pullIso a (S.immersion i)).app M)
    (local_extend a _ _ (hS i))

private theorem stratified_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun i ↦ local_iso
    ((CondensedRing.upperStar Λ (S.immersion i)).mapIso e) (hS i)⟩

private theorem constructible_extend (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ' X ((Mod.extendScalars (coefficientMap a X)).obj M) := by
  classical
  unfold IsConstantModelConstructible at h ⊢
  by_cases hX : CompactSpace X ∧ QuasiSeparatedSpace X
  · simp only [if_pos hX] at h ⊢
    exact stratified_extend a X M h
  · simp only [if_neg hX] at h ⊢
    intro V hV
    exact stratified_iso ((CondensedRing.pullIso a V.ι).app M)
      (stratified_extend a _ _ (h V hV))

/-- Exact coefficient extension preserves bounded constructibility in the finite constant
local-model convention. The same strata and covers work: a point presentation extends
by the coefficient map, finite presentations are preserved, and the point and geometric
pullback/scalar squares identify the chart models. Exactness identifies cohomology with
ordinary extension of scalars and preserves both cohomological bounds.
Source: latest blueprint, sk-prop-open-coefficients.proof.md, rational paragraph
(blueprint: lem-sfb-open-rational-scalar-local-models). -/
private theorem exact_scalar
    [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
    (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (hK : constantModelBoundedConstructible Λ X K) :
    constantModelBoundedConstructible Λ' X
      ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K) := by
  let F := Mod.extendScalars (coefficientMap a X)
  let := (constantModelConstructibleFiniteTor_wellDefined Λ' X).1
  have h : constantModelBoundedConstructible Λ' X (F.mapDerivedCategory.obj K) := by
    refine ⟨F.bounded_mapDerivedCategory_obj hK.1, fun n ↦ ?_⟩
    exact ObjectProperty.prop_of_iso (P := IsConstantModelConstructible Λ' X)
      ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
      (constructible_extend a X _ (hK.2 n))
  let := (constantModelConstructibleFiniteTor_wellDefined Λ' X).2.1
  exact (constantModelBoundedConstructible Λ' X).prop_of_iso
    (F.leftDerivedFunctorIsoMapDerivedCategory.app K).symm h

end

/-- The three rational coefficient inclusions preserve finite constant scalar models.
Their ordinary scalar extensions are exact by the localization, finite-free, and filtered
finite-subextension flatness theorems. Apply the preceding chartwise calculation, whose
cohomology comparison is `Functor.leftDerivedFunctorHomologyFunctorIso` and whose exact
model preserves every cohomological vanishing bound.
Source: latest blueprint, sk-prop-open-coefficients.proof.md, rational paragraph
(blueprint: lem-sfb-open-rational-scalar-local-models). -/
theorem open_rational_scalar_local_models
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) :
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
        ((Mod.extendScalars (coefficientMap
          (padicIntegersRingObjToContinuousMapRingObj ℓ E) X)).leftDerivedFunctor.obj
            K)) ∧
    (∀ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X))),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObj F) X
        ((Mod.extendScalars (coefficientMap (Profinite.padicSubfieldRingObjMap ℓ h) X)
          ).leftDerivedFunctor.obj K)) ∧
    (∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E) X)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X K →
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
        ((Mod.extendScalars (coefficientMap
          (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) X)).leftDerivedFunctor.obj K)) := by
  exact ⟨exact_scalar _ X,
    fun F h ↦ exact_scalar _ X,
    exact_scalar _ X⟩

end AlgebraicGeometry.ProEtale
