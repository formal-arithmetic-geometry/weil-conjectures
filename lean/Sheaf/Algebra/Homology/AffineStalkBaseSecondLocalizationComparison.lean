/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.Algebra.Homology.DerivedTensorBaseSecondLocalizationModels
import Sheaf.Algebra.Homology.BaseDerivedTensorUniverseIndependence

/-! # Base and second-factor localization after taking the affine input stalk

Source: Stacks Project, Tags 0DJ8 and 06Y6.
(blueprint: new-affine-stalk-base-second-localization-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

private theorem toStalk_stalkCongr (S : Type u) [CommRing S]
    (x y : PrimeSpectrum S) (h : x = y) :
    StructureSheaf.toStalk S x ≫
      ((Spec.structureSheaf S).presheaf.stalkCongr (.of_eq h)).hom =
        StructureSheaf.toStalk S y := by
  subst y
  simp only [TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl]
  exact Category.comp_id _

private def equalScalarComplexIso
    (S T : Type u) [CommRing S] [CommRing T] (a b : S →+* T) (h : a = b)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.extendScalars a).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((ModuleCat.extendScalars b).mapHomologicalComplex (.up ℤ)).obj Q :=
  eqToIso (congrArg
    (fun k : S →+* T ↦ ((ModuleCat.extendScalars k).mapHomologicalComplex (.up ℤ)).obj Q) h)

private theorem equalScalarComplexIso_tmul
    (S T : Type u) [CommRing S] [CommRing T] (a b : S →+* T) (h : a = b)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) (j : ℤ) (d : T) (x : Q.X j) :
    (equalScalarComplexIso S T a b h Q).hom.f j (d ⊗ₜ[S, a] x) =
      d ⊗ₜ[S, b] x := by
  subst b
  rfl

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option maxHeartbeats 800000 in
-- Comparing the two explicit stalk algebra structures requires this elaboration budget.
/-- Localize only the base and second factor of an already stalk-localized input.
Source: Stacks Project, Tag 0DJ8, base and second-factor part of the localization
identity; Tag 06Y6.
(blueprint: new-affine-stalk-base-second-localization-comparison).

Proof: the maps from R and R' to their spectrum stalks are prime localizations.
Their maps into the A-stalk and D agree by stalk-map naturality and the cartesian
square. The two restriction equations for psi identify its coefficient actions
with those of the actual tensor-to-stalk map. Apply base and second-factor
localization to Q, keeping the A-stalk unchanged. First compare m with a model
over R and R' in the standard universe using
exists_baseDerivedTensor_restricted_ring_comparison with identity ring equivalences.
Its scalar-action clause and tensor induction upgrade the second-ring-linear
isomorphism to Aq tensor_R R'-linearity. Its ordinary comparison clause,
localized_eq and scalar-extension adjunction give the localized square. Now
apply derivedTensor_base_second_localization_models in that standard universe.
These comparisons preserve the A-stalk action by cohomologyIso_smul.
Extend the resulting tensor-algebra-linear isomorphism to D. The augmentations
of the common resolutions yield a commuting localizedComparison square.
The ordinary targets have the same A-stalk-to-D map, so their canonical chain
isomorphism sends d tensor q to d tensor q. For a compatible tau, set sigma to beta inverse
followed by tau. The formula for beta and its inverse identity show that sigma
agrees with the canonical map on 1 tensor germs of M. These generate C1: beta is an isomorphism, and
1 tensor x generate C. ExtendScalars.hom_ext and D-linearity prove equality
of the chain maps. Taking homology gives the equation for every such sigma.
Zero complexes and identity localizations give the same comparison; a zero A'
has no prime p. No first-factor localization is asserted or used here. -/
theorem exists_affineStalkBaseSecondLocalizationComparison
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ)
    (p : PrimeSpectrum A') :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      let D : Type u := (Spec.structureSheaf A').presheaf.stalk p
      let κ := (StructureSheaf.toStalk A' p).hom
      let Aq : Type u := (Spec.structureSheaf A).presheaf.stalk (g' p)
      let κA := (StructureSheaf.toStalk A (g' p)).hom
      let α := (g'.stalkMap p).hom
      letI : Algebra R Aq := (κA.comp (algebraMap R A)).toAlgebra
      (ψ : Aq ⊗[R] R' →+* D) →
      ψ.comp (algebraMap Aq (Aq ⊗[R] R')) = α →
      ψ.comp Algebra.TensorProduct.includeRight.toRingHom = κ.comp φf' →
      letI := ψ.toAlgebra
      let Q := SingleComplexBaseChange.stalkComplex g' p P
      (m : ModuleCat.BaseDerivedTensorCohomologyModel R Aq R' Q D) →
      let C := ((ModuleCat.extendScalars (κ.comp φg')).mapHomologicalComplex (.up ℤ)).obj M
      let φ₁ := ψ.comp (algebraMap Aq (Aq ⊗[R] R'))
      let C₁ := ((ModuleCat.extendScalars φ₁).mapHomologicalComplex (.up ℤ)).obj Q
      (β : C ≅ C₁) →
      (∀ (j : ℤ) (x : M.X j),
        β.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
          (1 : D) ⊗ₜ[Aq, φ₁]
            (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
              (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      let l :=
        (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i
      ∃ e : (ModuleCat.extendScalars ψ).obj (m.cohomology i) ≅ (Arrow.mk l).left,
        ∀ τ : C ≅ SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
          (∀ (j : ℤ) (x : M.X j),
            τ.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
              (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
                (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                  (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
          m.localizedComparison i ≫ HomologicalComplex.homologyMap
            (β.inv ≫ τ.hom) i = e.hom ≫ l := by
  classical
  have _ := hφg'
  have _ := hφf'
  intro P f f' g g' D κ Aq κA α ψ hψA hψB Q m C φ₁ C₁ β hβ ρ l
  let : Algebra R Aq := (κA.comp (algebraMap R A)).toAlgebra
  let : Algebra (Aq ⊗[R] R') D := ψ.toAlgebra
  let : Algebra R' (Aq ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  let Rp : Type u := SingleComplexBaseChange.R f g' p
  let Bp : Type u := SingleComplexBaseChange.B f' p
  let := HasDerivedCategory.standard (ModuleCat.{u} Rp)
  let := HasDerivedCategory.standard (ModuleCat.{u} Bp)
  let : Algebra Rp Aq := SingleComplexBaseChange.leftAlgebra f g' p
  let : Algebra Rp Bp := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
  let : Algebra Bp (Aq ⊗[Rp] Bp) := Algebra.TensorProduct.rightAlgebra
  let : Algebra (Aq ⊗[Rp] Bp) D :=
    (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
  let κR : R →+* Rp := (StructureSheaf.toStalk R (f (g' p))).hom
  let κB : R' →+* Bp := (StructureSheaf.toStalk R' (f' p)).hom
  let : Algebra R Rp := κR.toAlgebra
  let : Algebra R' Bp := κB.toAlgebra
  let : Algebra R Bp := (κB.comp (algebraMap R R')).toAlgebra
  let : Algebra Aq D := α.toAlgebra
  let : Algebra R' D := (κ.comp φf').toAlgebra
  let : Algebra Bp D := (f'.stalkMap p).hom.toAlgebra
  have tRA : IsScalarTower R Rp Aq := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (AlgebraicGeometry.stalkMap_toStalk_apply
      (CommRingCat.ofHom (algebraMap R A)) (g' p) r).symm)
  have tRB : IsScalarTower R R' Bp := IsScalarTower.of_algebraMap_eq' rfl
  have tRpB : IsScalarTower R Rp Bp := IsScalarTower.of_algebraMap_eq' (by
    ext r
    have hc := toStalk_stalkCongr R (f (g' p)) (g (f' p))
      (congrArg (fun k : Spec (.of A') ⟶ Spec (.of R) ↦ k p) sq.w)
    have hn := AlgebraicGeometry.stalkMap_toStalk
      (CommRingCat.ofHom (algebraMap R R')) (f' p)
    have hh := congrArg CommRingCat.Hom.hom
      ((congrArg (fun k ↦ k ≫ g.stalkMap (f' p)) hc).trans hn)
    exact (RingHom.congr_fun hh r).symm)
  have tAD : IsScalarTower Aq (Aq ⊗[R] R') D :=
    IsScalarTower.of_algebraMap_eq' hψA.symm
  have tBD : IsScalarTower R' (Aq ⊗[R] R') D :=
    IsScalarTower.of_algebraMap_eq' hψB.symm
  have tApD : IsScalarTower Aq (Aq ⊗[Rp] Bp) D :=
    IsScalarTower.of_algebraMap_eq'
      (Classical.choose_spec
        (SingleComplexBaseChange.exists_tensorMap f f' g g' sq p)).1.symm
  have tBpD : IsScalarTower Bp (Aq ⊗[Rp] Bp) D :=
    IsScalarTower.of_algebraMap_eq'
      (Classical.choose_spec
        (SingleComplexBaseChange.exists_tensorMap f f' g g' sq p)).2.symm
  have tBBpD : IsScalarTower R' Bp D := IsScalarTower.of_algebraMap_eq' (by
    ext b
    exact (AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom φf') p b).symm)
  let : IsLocalization (f (g' p)).asIdeal.primeCompl Rp :=
    StructureSheaf.IsLocalization.to_stalk (R := R) (f (g' p))
  let : IsLocalization (f' p).asIdeal.primeCompl Bp :=
    StructureSheaf.IsLocalization.to_stalk (R := R') (f' p)
  let mc := m.localizedComparison i
  let dRold : HasDerivedCategory.{wM} (ModuleCat.{u} R) := inferInstance
  let dBold : HasDerivedCategory.{wM} (ModuleCat.{u} R') := inferInstance
  let dRstd := HasDerivedCategory.standard (ModuleCat.{u} R)
  let dBstd := HasDerivedCategory.standard (ModuleCat.{u} R')
  let n := ModuleCat.baseDerivedTensorCohomologyModel.{u, u, u, u, u, u + 1}
    R Aq R' Q D
  obtain ⟨s, hs⟩ :=
    @ModuleCat.baseDerivedTensorCohomologyModel_localized_universe_independence.{u, wM, u + 1}
      R Aq R' D _ _ _ _ (κA.comp (algebraMap R A)).toAlgebra _ ψ.toAlgebra
      dRold dBold Q m dRstd dBstd n i
  obtain ⟨e, he, _⟩ :=
    RingTensorCohomology.derivedTensor_base_second_localization_models
      R Aq R' Rp Bp D (f (g' p)).asIdeal.primeCompl (f' p).asIdeal.primeCompl i
  let k := SingleComplexBaseChange.cohomologyModel f f' g g' sq p P
  have hφ : φ₁ = ρ := hψA.trans
    (Classical.choose_spec
      (SingleComplexBaseChange.exists_tensorMap f f' g g' sq p)).1.symm
  let σ := equalScalarComplexIso Aq D φ₁ ρ hφ Q
  have hσsquare := he Q n k σ (equalScalarComplexIso_tmul Aq D φ₁ ρ hφ Q)
  refine ⟨s ≪≫ e Q n k, ?_⟩
  intro τ hτ
  have ht : β.inv ≫ τ.hom = σ.hom := by
    apply (cancel_epi β.hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change τ.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
      σ.hom.f j (β.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x))
    rw [hβ, hτ]
    exact (equalScalarComplexIso_tmul Aq D φ₁ ρ hφ Q j 1 _).symm
  change mc ≫ HomologicalComplex.homologyMap (β.inv ≫ τ.hom) i =
    s.hom ≫ (e Q n k).hom ≫ l
  rw [ht]
  exact (congrArg (fun a ↦ a ≫ HomologicalComplex.homologyMap σ.hom i) hs.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (fun a ↦ s.hom ≫ a) hσsquare))

end AlgebraicGeometry
