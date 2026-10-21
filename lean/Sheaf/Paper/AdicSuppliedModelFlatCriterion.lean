/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.LevelwiseAdicTruncations

import Sheaf.Paper.AdicSuppliedModelReconstruction
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import all Sheaf.Paper.PbcUniformLocalModelCohomology
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection

/-! # The supplied-model half of the Padic flatness criterion -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem model_flat_iso {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {M N : pbcModules X R} (e : M ≅ N)
    (h : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) N := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  open MonoidalCategory in
  have hM : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M) h
  open MonoidalCategory in
  have hN : exactFunctor _ _ (tensorRight N) :=
    (exactFunctor _ _).prop_of_iso ((curriedTensor _).flip.mapIso e) hM
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R N).symm hN

set_option backward.isDefEq.respectTransparency false in
private theorem model_flat_pullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (M : pbcModules Y R) (h : SheafOfModules.IsFlatOnSite (J := ProEt.topology Y) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
      (R := (adicTowerInverseImage g).obj R)
      ((proEtaleRingModulePullback g R _ (Iso.refl _)).obj M) := by
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists g R
  have : RepresentablyFlat (proEtaleBaseChange g) := flat_of_preservesFiniteLimits _
  have : PreservesFiniteLimits (proEtaleSheafInverseImage g (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage g (𝟙 Y)).2.2.2.1
  have hf := SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{u + 1, u, u + 1, u,
    u + 1, u + 1}
    (proEtaleSheafInverseImage g (Type (u + 1)))
    (proEtaleSheafDirectImage g (Type (u + 1)))
    (proEtaleSheafAdjunction g (Type (u + 1)))
    (SheafOfModules.inverseImageOfUniverses I) M h
  change SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
    (R := (adicTowerInverseImage g).obj R) (I.modules.obj M) at hf
  rw [hI] at hf
  let θ := (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (Iso.refl ((adicTowerInverseImage g).obj R))).choose
  exact model_flat_iso _ (θ _).symm hf

set_option backward.isDefEq.respectTransparency false in
private theorem model_zero_detect (T : Scheme.{u}) [IsNoetherian T]
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Stratification T)
    (V : ∀ α : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain α))
    (M : pbcModules T R)
    (h : ∀ α j, IsZero ((proEtaleRingModulePullback
      ((V α).f j ≫ S.immersion α) R _ (Iso.refl _)).obj M)) : IsZero M := by
  have hz : IsZero ((SheafOfModules.toSheaf _).obj M) := by
    apply proEtale_isZero_of_stratum_cover T S V
    intro α j
    let g := (V α).f j ≫ S.immersion α
    let R' := (adicTowerInverseImage g).obj R
    let F := proEtaleRingModulePullback g R R' (Iso.refl _)
    let adj := proEtaleRingModuleAdjunction g R R' (Iso.refl _)
    let a := ((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj M)
      ((SheafOfModules.toSheaf _).obj (F.obj M))).symm
        ((SheafOfModules.toSheaf _).map (adj.unit.app M))
    have : IsIso a := ringUnitComparison g R R' (Iso.refl _) adj M
    exact ((SheafOfModules.toSheaf _).map_isZero (h α j)).of_iso (asIso a)
  apply (IsZero.iff_id_eq_zero M).2
  apply (SheafOfModules.toSheaf _).map_injective
  simpa using hz.eq_of_src ((SheafOfModules.toSheaf _).map (𝟙 M))
    ((SheafOfModules.toSheaf _).map (0 : M ⟶ M))

set_option backward.isDefEq.respectTransparency false in
private theorem model_flat_descent (T : Scheme.{u}) [IsNoetherian T]
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Stratification T)
    (V : ∀ α : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain α))
    (M : pbcModules T R)
    (h : ∀ α j, SheafOfModules.IsFlatOnSite
      (J := ProEt.topology ((V α).X j))
      (R := (adicTowerInverseImage ((V α).f j ≫ S.immersion α)).obj R)
      ((proEtaleRingModulePullback ((V α).f j ≫ S.immersion α)
        R _ (Iso.refl _)).obj M)) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) M := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  open MonoidalCategory in
  have hflat : exactFunctor _ _ (tensorRight M) := by
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
      have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
      exact preservesColimitsOfSize_shrink (tensorLeft M)
    have : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
      preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
    have : (tensorRight M).Additive := by
      have := SheafOfModules.tensorLeft_additive_independent R M
      exact Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight M)
    have : (tensorRight M).PreservesMonomorphisms := ⟨by
      intro A B f hf
      apply Preadditive.mono_of_isZero_kernel
      apply model_zero_detect T R S V
      intro α j
      let g := (V α).f j ≫ S.immersion α
      let R' := (adicTowerInverseImage g).obj R
      let F := proEtaleRingModulePullback g R R' (Iso.refl _)
      let := SheafOfModules.isMonoidal_W_independentCoefficients R'
      let := SheafOfModules.monoidalCategory R'
      have hlocal : exactFunctor _ _ (tensorRight (F.obj M)) :=
        (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R' _) (h α j)
      have : PreservesFiniteLimits (tensorRight (F.obj M)) := hlocal.1
      let e : tensorRight M ⋙ F ≅ F ⋙ tensorRight (F.obj M) :=
        NatIso.ofComponents
          (fun N ↦ proEtaleOrdinaryTensorPullback g R R' (Iso.refl _) N M)
          (by
            intro N N' a
            simpa using proEtaleOrdinaryTensorPullback_naturality
              g R R' (Iso.refl _) N N' M M a (𝟙 M))
      have : Mono (F.map ((tensorRight M).map f)) := by
        change Mono ((tensorRight M ⋙ F).map f)
        have : Mono ((tensorRight M ⋙ F).map f ≫ e.hom.app B) := by
          rw [e.hom.naturality]
          infer_instance
        exact mono_of_mono ((tensorRight M ⋙ F).map f) (e.hom.app B)
      exact (isZero_kernel_of_mono (F.map ((tensorRight M).map f))).of_iso
        (PreservesKernel.iso F ((tensorRight M).map f))⟩
    have := Functor.preservesHomology_of_preservesMonos_and_cokernels (tensorRight M)
    have := Functor.preservesFiniteLimits_of_preservesHomology (tensorRight M)
    exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
  exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R M).symm
    hflat

/-- Ambient and supplied common-model cohomology flatness agree.
Source: blueprint integral truncations, hypothesis paragraph, steps 9--11 of
lem-weil-pbc-adic-tor-flat-cohomology
(blueprint: lem-weil-pbc-adic-flat-iff-supplied-model-flat).

Proof: each bounded adic-lisse supplied complex is complete by torsion-limit
completeness and the constant/completed coefficient equivalence. Exact stratum and
slice restrictions preserve completed coefficients, countable products and the Roos
completion triangle, so the restricted ambient complex is complete too. The supplied
normalization equations identify their quotient towers. Sequential evaluation
fullness lifts this to an isomorphism of strict derived towers. Derived limit and
Koszul reconstruction identify the model with the restricted ambient complex.
Exact inverse image therefore identifies all cohomology sheaves. It preserves
flatness by the tensor comparison. Conversely choose a supplied system from uniform
constructibility and detect the kernel of tensoring every injection on its stratum
covers. Noetherian stratum detection makes that kernel zero globally. Tensor is
right exact, giving ambient flatness. Zero objects and empty strata need no separate
nonzero hypothesis. -/
theorem pbc_adic_flat_iff_supplied_model_flat
    (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)) :
    (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := pbcAdicCompletion T (pbcPadicCoefficientDatum l E))
        ((DerivedCategory.homologyFunctor _ q).obj K.obj)) ↔
    ∀ (d₀ d₁ : ℤ), d₀ ≤ d₁ → ∀ (S : Stratification T)
        (V : ∀ α : Fin S.n, Sieve (⊤_ (S.domain α).ProEt)),
        (∀ α : Fin S.n, V α ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt)) →
        ∀ L : ∀ (α : Fin S.n) (U : (S.domain α).ProEt)
            (f : U ⟶ ⊤_ (S.domain α).ProEt),
            V α f → AdicTowerLocalModel (pbcPadicCoefficientDatum l E) (U.hom ≫ S.immersion α)
              (pbcReductionAdicTower T (pbcPadicCoefficientDatum l E) K.obj) d₀ d₁,
          ∀ (α : Fin S.n) (U : (S.domain α).ProEt)
            (f : U ⟶ ⊤_ (S.domain α).ProEt) (hf : V α f) (q : ℤ),
            SheafOfModules.IsFlatOnSite (J := ProEt.topology U.left)
              (R := (adicTowerInverseImage (U.hom ≫ S.immersion α)).obj
                (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)))
              ((DerivedCategory.homologyFunctor _ q).obj
                (DerivedCategory.Q.obj (L α U f hf).complex)) := by
  classical
  let d := pbcPadicCoefficientDatum l E
  let R := pbcAdicCompletion T d
  constructor
  · intro h a b hab S V hV L α U f hf q
    let g := U.hom ≫ S.immersion α
    let F := proEtaleRingModulePullback g R _ (Iso.refl _)
    obtain ⟨e⟩ := pbc_suppliedModel_reconstruction (S.immersion α) U d K.obj K.property.1
      a b (L α U f hf)
    exact model_flat_iso _
      ((F.mapDerivedCategoryHomologyFunctorIso q).app K.obj ≪≫
        ((DerivedCategory.homologyFunctor _ q).mapIso e).symm)
      (model_flat_pullback g R _ (h q))
  · intro h
    obtain ⟨M, e, ⟨a, b, hab, S, hS⟩, he⟩ := K.property.2.1
    choose W hW hL using hS
    let C := pbcReductionAdicTower T d K.obj
    have he' : ∀ j i hij,
        adicTowerSemilinearTransition T d M.level M.normalization j i hij ≫
            (pbcDerivedRestrict (pbcAdicQuotient T d j i hij)).map (e i).hom =
          (e j).hom ≫ adicTowerSemilinearTransition T d C.level C.normalization j i hij := by
      intro j i hij
      rw [he j i hij]
      congr 1
      dsimp only [C, pbcReductionAdicTower, adicTowerSemilinearTransition,
        pbcReductionNormalization, pbcReductionNormalizationHom]
      exact ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d j i hij)).homEquiv _ _
        |>.apply_symm_apply _).symm
    have hmodels : ∀ (α : Fin S.n) (U : (S.domain α).ProEt)
        (f : U ⟶ ⊤_ (S.domain α).ProEt), W α f →
        Nonempty (AdicTowerLocalModel d (U.hom ≫ S.immersion α) C a b) := by
      intro α U f hf
      obtain ⟨L⟩ := hL α U f hf
      exact local_model_transport _ d M C e he' a b L
    let L := fun α U f hf ↦ Classical.choice (hmodels α U f hf)
    have hlocal := h a b hab S W hW L
    choose I U f hU hf using (fun α ↦ cover_of_sieve (S.domain α) (W α) (hW α))
    let V (α : Fin S.n) : Cover.{u + 1} proetalePrecoverage (S.domain α) :=
      { I₀ := I α, X := fun j ↦ (U α j).left, f := fun j ↦ (U α j).hom, mem₀ := hU α }
    intro q
    apply model_flat_descent T R S V
    intro α j
    let g := (U α j).hom ≫ S.immersion α
    let F := proEtaleRingModulePullback g R _ (Iso.refl _)
    obtain ⟨eL⟩ := pbc_suppliedModel_reconstruction (S.immersion α) (U α j) d K.obj
      K.property.1 a b (L α (U α j) (f α j) (hf α j))
    exact model_flat_iso _
      ((DerivedCategory.homologyFunctor _ q).mapIso eL ≪≫
        ((F.mapDerivedCategoryHomologyFunctorIso q).app K.obj).symm)
      (hlocal α (U α j) (f α j) (hf α j) q)

end AlgebraicGeometry.Scheme
