/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.LevelwiseAdicTruncations
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

import Sheaf.Paper.AdicCohomologyTorsionNormalForm
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # The Padic Tor criterion for flat cohomology

This is the first independent half of the criterion in
`Sheaf.Paper.AdicTorFlatCohomology`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem flat_of_iso (X : Scheme.{u})
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {M N : pbcModules X R} (e : M ≅ N)
    (h : SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) N := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let tensor : MonoidalCategory (pbcModules X R) := SheafOfModules.monoidalCategory R
  let e₁ := SheafOfModules.siteSheafTensorRightIso R M
  let e₂ := SheafOfModules.siteSheafTensorRightIso R N
  let e₃ := (@MonoidalCategory.curriedTensor (pbcModules X R) _ tensor).flip.mapIso e
  exact (exactFunctor _ _).prop_of_iso (e₁ ≪≫ e₃ ≪≫ e₂.symm) h

private theorem flat_of_sectionwise_flat (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (F : pbcModules X R) (hF : ∀ U : X.ProEtᵒᵖ, Module.Flat (R.obj.obj U) (F.val.obj U)) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) F := by
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion R F
  intro U n a s hs
  refine ⟨⊤, (ProEt.topology X).top_mem U, ?_⟩
  intro V f _
  have : Module.Flat (R.obj.obj (op V)) (F.val.obj (op V)) := hF (op V)
  have he := congrArg (fun x ↦ (show F.val.obj (op V) from F.val.map f.op x)) hs
  rw [map_sum, map_zero] at he
  have he' : (∑ p : Fin n, (show F.val.obj (op V) from
      F.val.map f.op (a p • s p))) = 0 := he
  have hr : (∑ p : Fin n, R.obj.map f.op (a p) •
      (show F.val.obj (op V) from F.val.map f.op (s p))) = 0 := by
    calc
      _ = ∑ p : Fin n, (show F.val.obj (op V) from
          F.val.map f.op (a p • s p)) := by
        apply Finset.sum_congr rfl
        intro p _
        exact (F.val.map_smul f.op (a p) (s p)).symm
      _ = 0 := he'
  obtain ⟨k, b, t, hb, ht⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hr
  exact ⟨k, b, t, hb, ht⟩

private theorem isZero_of_nilpotent_cokernel
    {C : Type*} [Category* C] [Abelian C] {N : C} (f : End N)
    (hnil : IsNilpotent f) (hc : IsZero (cokernel f)) : IsZero N := by
  have : Epi f := Abelian.epi_of_cokernel_π_eq_zero f (hc.eq_of_tgt _ _)
  have hp : ∀ n : ℕ, Epi (f ^ n) := by
    intro n
    induction n with
    | zero => change Epi (𝟙 N); infer_instance
    | succ n ih =>
      rw [pow_succ]
      change Epi (f ≫ f ^ n)
      infer_instance
  obtain ⟨n, hn⟩ := hnil
  have := hp n
  exact IsZero.of_epi_eq_zero (f ^ n) hn

private theorem module_zero_of_stratum_cover
    (T : Scheme.{u}) [IsNoetherian T] (S : Stratification T)
    (V : ∀ a : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain a))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (F : proEtaleRingModules T R)
    (hF : ∀ a j, IsZero ((proEtaleRingModulePullback
      ((V a).f j ≫ S.immersion a) R
      ((adicTowerInverseImage ((V a).f j ≫ S.immersion a)).obj R)
      (Iso.refl _)).obj F)) : IsZero F := by
  have hz : IsZero ((SheafOfModules.toSheaf _).obj F) := by
    apply proEtale_isZero_of_stratum_cover T S V
    intro a j
    let g := (V a).f j ≫ S.immersion a
    let R' := (adicTowerInverseImage g).obj R
    let P := proEtaleRingModulePullback g R R' (Iso.refl _)
    let adj := proEtaleRingModuleAdjunction g R R' (Iso.refl _)
    let c := ((proEtaleSheafAdjunction g AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj F)
      ((SheafOfModules.toSheaf _).obj (P.obj F))).symm
        ((SheafOfModules.toSheaf _).map (adj.unit.app F))
    have : IsIso c := ringUnitComparison g R R' (Iso.refl _) adj F
    exact ((SheafOfModules.toSheaf _).map_isZero (hF a j)).of_iso (asIso c)
  apply (IsZero.iff_id_eq_zero F).2
  apply (SheafOfModules.toSheaf _).map_injective
  simpa using hz.eq_of_src ((SheafOfModules.toSheaf _).map (𝟙 F))
    ((SheafOfModules.toSheaf _).map (0 : F ⟶ F))

set_option backward.isDefEq.respectTransparency false in
private theorem flat_of_stratum_cover
    (T : Scheme.{u}) [IsNoetherian T] (S : Stratification T)
    (V : ∀ a : Fin S.n, Cover.{u + 1} proetalePrecoverage (S.domain a))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (F : proEtaleRingModules T R)
    (hF : ∀ a j, SheafOfModules.IsFlatOnSite (J := ProEt.topology ((V a).X j))
      (R := (adicTowerInverseImage ((V a).f j ≫ S.immersion a)).obj R)
      ((proEtaleRingModulePullback ((V a).f j ≫ S.immersion a) R
        ((adicTowerInverseImage ((V a).f j ≫ S.immersion a)).obj R)
        (Iso.refl _)).obj F)) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology T) (R := R) F := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  have hl := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R F
  have : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft F) :=
    preservesColimitsOfSize_shrink _
  have : PreservesFiniteColimits (MonoidalCategory.tensorLeft F) := inferInstance
  have hc : PreservesFiniteColimits (MonoidalCategory.tensorRight F) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)
  have : (MonoidalCategory.tensorRight F).Additive :=
    (rightExactFunctor_le_additiveFunctor _ _) _ hc
  have hm {M N : proEtaleRingModules T R} (f : M ⟶ N) [Mono f] :
      Mono ((MonoidalCategory.tensorRight F).map f) := by
    let t := (MonoidalCategory.tensorRight F).map f
    have hz : IsZero (kernel t) := by
      apply module_zero_of_stratum_cover T S V R
      intro a j
      let g := (V a).f j ≫ S.immersion a
      let R' := (adicTowerInverseImage g).obj R
      let P := proEtaleRingModulePullback g R R' (Iso.refl _)
      let := SheafOfModules.isMonoidal_W_independentCoefficients R'
      let := SheafOfModules.monoidalCategory R'
      have hf : exactFunctor _ _ (MonoidalCategory.tensorRight (P.obj F)) :=
        (exactFunctor _ _).prop_of_iso
          (SheafOfModules.siteSheafTensorRightIso R' (P.obj F)) (hF a j)
      have : PreservesFiniteLimits (MonoidalCategory.tensorRight (P.obj F)) := hf.1
      have he := proEtaleOrdinaryTensorPullback_naturality g R R' (Iso.refl _)
        M N F F f (𝟙 F)
      rw [((proEtaleOrdinaryTensor T R).obj N).map_id, Category.comp_id,
        (proEtaleRingModulePullback g R R' (Iso.refl _)).map_id,
        ((proEtaleOrdinaryTensor ((V a).X j) R').obj (P.obj N)).map_id,
        Category.comp_id] at he
      change P.map t ≫ (proEtaleOrdinaryTensorPullback g R R' (Iso.refl _) N F).hom =
        (proEtaleOrdinaryTensorPullback g R R' (Iso.refl _) M F).hom ≫
          (MonoidalCategory.tensorRight (P.obj F)).map (P.map f) at he
      have : Mono (P.map t ≫
          (proEtaleOrdinaryTensorPullback g R R' (Iso.refl _) N F).hom) := by
        rw [he]
        infer_instance
      have : Mono (P.map t) := mono_of_mono (P.map t)
        (proEtaleOrdinaryTensorPullback g R R' (Iso.refl _) N F).hom
      exact (isZero_kernel_of_mono (P.map t)).of_iso (PreservesKernel.iso P t)
    exact Abelian.mono_of_kernel_ι_eq_zero t (hz.eq_of_src _ _)
  have : (MonoidalCategory.tensorRight F).PreservesMonomorphisms := ⟨fun f _ ↦ hm f⟩
  have hleft : PreservesFiniteLimits (MonoidalCategory.tensorRight F) := by
    apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2
    intro C hC
    have := hC.mono_f
    exact ⟨hC.exact.map_of_epi_of_preservesCokernel _ hC.epi_g inferInstance,
      inferInstance⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R F).symm ⟨hleft, hc⟩

/-- Higher Tor vanishing at all cutoffs implies flatness of every ambient
cohomology sheaf. This is the Tor half of the blueprint criterion; its proof is the
uniformizer resolution, finite-stratum descent, and Smith-normal-form argument in
steps 1--8 of `lem-weil-pbc-adic-tor-flat-cohomology`.

Source: blueprint integral truncations, hypothesis paragraph
(blueprint: lem-weil-pbc-adic-tor-implies-flat-cohomology).

Proof: the independent local DVR normal form splits each restricted cohomology
sheaf into a finite free part F and a torsion part N with a nilpotent endomorphism f.
The assumed vanishing at cutoff q-1 and Tor degree one makes the supplied epimorphism
to cokernel f have zero source. Thus f is epic; a zero power of f is epic, forcing
N to vanish. The equational criterion makes F flat, since each of its section
modules is finite free. For an ambient injection, exact inverse image and the
ordinary tensor comparison make its tensor kernel zero on all these charts.
Noetherian stratum detection makes that kernel zero globally. Tensor is right
exact and additive, so preservation of injections gives exactness and hence
flatness. Empty charts are included by the same zero-object arguments. -/
theorem pbc_adic_tor_implies_flat_cohomology
    (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)) :
    (∀ m : ℤ, PbcLevelwiseTorVanishing T (pbcPadicCoefficientDatum l E)
        (pbcReductionAdicTower T (pbcPadicCoefficientDatum l E) K.obj) m) →
      ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := pbcAdicCompletion T (pbcPadicCoefficientDatum l E))
        ((DerivedCategory.homologyFunctor _ q).obj K.obj) := by
  intro hTor q
  obtain ⟨S, V, h⟩ := pbc_adic_cohomology_torsion_normal_form T _hdim l E _hl K q
  apply flat_of_stratum_cover T S V
  intro a j
  obtain ⟨r, F, N, hfree, ⟨e⟩, f, hf, n, t, ht⟩ := h a j
  have hz := hTor (q - 1) n q (by omega) 1 (by omega)
  have : Epi t := ht
  have hc : IsZero (cokernel f) := by
    apply IsZero.of_epi t
    apply Functor.map_isZero
    apply Functor.map_isZero
    exact hz
  have hN := isZero_of_nilpotent_cokernel f hf hc
  have hF : SheafOfModules.IsFlatOnSite (J := ProEt.topology ((V a).X j))
      (R := (adicTowerInverseImage ((V a).f j ≫ S.immersion a)).obj
        (pbcAdicCompletion T (pbcPadicCoefficientDatum l E))) F := by
    apply flat_of_sectionwise_flat
    intro U
    have : Module.Free _ (F.val.obj U) := Module.Free.of_basis (Classical.choice (hfree U))
    infer_instance
  exact flat_of_iso _ ((e ≪≫ (isoBiprodZero hN).symm).symm) hF

end AlgebraicGeometry.Scheme
