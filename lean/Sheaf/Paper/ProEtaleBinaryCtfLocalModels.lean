/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.SixFunctors.FiniteCoverCTFLocality
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.ProEtaleConstantModulePullbackEncoding
import Sheaf.Paper.ProEtaleFiniteModelLocalConstancy
import Sheaf.Paper.ProEtaleFiniteModelStalks
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover

/-! # Finite-coefficient bounds from binary open local models

Source: blueprint det-sp-tower-gluing, Uniformity paragraph; Stacks Project,
Tags 08FZ (Tor amplitude) and 09AJ (intrinsic constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem fixed_constructible_iff (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :
    IsConstructibleProEtaleFixedModuleSheaf T A F ↔ ProEtale.IsConstructible A F := by
  have hlocal (S : Scheme.{u})
      (G : Sheaf (ProEt.topology S) (ModuleCat.{u + 1} A))
      (hG : ProEtale.IsFiniteLocallyConstant A G) :
      IsLocallyConstantProEtaleFixedModuleSheaf S A G ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
          Finite (proEtaleGeometricFixedModuleStalk x A G) := by
    obtain ⟨I, U, f, hf, he⟩ := ProEtale.finiteModels_over A G hG
    refine ⟨⟨I, U, f, hf, fun i ↦ ?_⟩,
      fun Ω _ _ x ↦ ProEtale.finite_geometricStalk_of_finite_models A G hG Ω x⟩
    obtain ⟨M, _, hM⟩ := he i
    exact ⟨M, hM⟩
  constructor
  · rintro ⟨S, _, _, hS⟩
    exact ⟨S, fun i ↦ finite_models_of_fixed_lisse (S.domain i) A _ (hS i)⟩
  · rintro ⟨S, hS⟩
    by_cases hn : 0 < S.n
    · exact ⟨S, hn, S.isConstructible_stratum, fun i ↦ hlocal _ _ (hS i)⟩
    have hz : S.n = 0 := Nat.eq_zero_of_not_pos hn
    have : IsEmpty T := ⟨fun x ↦ by
      have hx : x ∈ ⋃ i, S.stratum i := S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x
      obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
      exact Fin.elim0 (hz ▸ i)⟩
    let S' : Stratification T := {
      n := 1
      stratum _ := Set.univ
      isLocallyClosed_stratum _ := isOpen_univ.isLocallyClosed
      isConstructible_stratum _ := Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := by
        apply Set.eq_univ_of_forall
        intro x
        exact isEmptyElim x
      pairwise_disjoint_stratum i j hij := (hij (Subsingleton.elim _ _)).elim
      domain _ := T
      immersion _ := 𝟙 T
      range_immersion _ := Set.range_id }
    refine ⟨S', Nat.zero_lt_one, S'.isConstructible_stratum, fun i ↦ hlocal _ _ ?_⟩
    refine ⟨ULift.{u + 1} Empty, fun i ↦ i.down.elim, fun i ↦ i.down.elim, ?_,
      fun i ↦ i.down.elim⟩
    have he : Presieve.ofArrows (fun i : ULift.{u + 1} Empty ↦ i.down.elim)
        (fun i ↦ i.down.elim) = (⊥ : Presieve T) := by
      funext U f
      apply propext
      constructor
      · rintro ⟨i⟩
        exact i.down.elim
      · exact False.elim
    rw [he]
    exact bot_mem_propQCPrecoverage T

private noncomputable def realization_restriction_iso
    (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    F ≅ (proEtaleModuleRestriction T A).obj ((sfIntrinsicModuleEquivalence T A).functor.obj F) := by
  let P := (ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} A)).obj F.obj
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
  let η : F ⟶ (proEtaleModuleRestriction T A).obj
      ((sfIntrinsicModuleEquivalence T A).functor.obj F) :=
    ⟨{ app U := (adj.unit.app P).app U
       naturality _ _ f := by
         ext x
         exact ConcreteCategory.congr_hom ((adj.unit.app P).naturality f) x }⟩
  have : IsIso η := by
    have : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify (ProEt.topology T) P.presheaf)
      exact isIso_toSheafify (ProEt.topology T)
        ((sheafCompose (ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A))
            AddCommGrpCat.{u + 1})).obj F).property
    have hη (U : T.ProEtᵒᵖ) : IsIso (η.hom.app U) := by
      have : IsIso ((PresheafOfModules.toPresheaf _).map (adj.unit.app P)) := inferInstance
      have : IsIso (((PresheafOfModules.toPresheaf _).map (adj.unit.app P)).app U) :=
        inferInstance
      rw [← isIso_iff_of_reflects_iso _
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) AddCommGrpCat.{u + 1})]
      change IsIso (((PresheafOfModules.toPresheaf _).map (adj.unit.app P)).app U)
      infer_instance
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
    change IsIso η.hom
    rw [NatTrans.isIso_iff_isIso_app]
    exact hη
  exact asIso η

private noncomputable def inverse_homology_iso (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory T A) (i : ℤ) :
    (DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2} _ i).obj
        ((Functor.mapDerivedCategory.{u + 2, u + 1}
          (sfIntrinsicModuleEquivalence T A).inverse).obj K) ≅
      (proEtaleModuleRestriction T A).obj
        ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ i).obj K) :=
  (((sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategoryHomologyFunctorIso i).app
    K).symm ≪≫
  realization_restriction_iso T A _ ≪≫
  (proEtaleModuleRestriction T A).mapIso ((sfIntrinsicModuleEquivalence T A).counitIso.app _)

private theorem constructible_homology_iff (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    (K : proEtaleDerivedCategory T A) (i : ℤ) :
    IsConstructibleProEtaleFixedModuleSheaf T (ULift.{u + 1} A)
      ((DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2} _ i).obj
        ((Functor.mapDerivedCategory.{u + 2, u + 1}
          (sfIntrinsicModuleEquivalence T A).inverse).obj K)) ↔
    IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ i).obj K) := by
  rw [fixed_constructible_iff, proEtaleModuleRestriction_constructible_iff]
  exact ⟨ProEtale.isConstructible_of_iso (inverse_homology_iso T A K i),
    ProEtale.isConstructible_of_iso (inverse_homology_iso T A K i).symm⟩

private noncomputable def native_tensor (T : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleDerivedCategory T A × proEtaleDerivedCategory T A ⥤
      proEtaleDerivedCategory T A :=
  @MonoidalCategory.tensor (proEtaleDerivedCategory T A) _
    (RingedDerivedNative.monoidal.{u + 1, u, 0} (ProEt.topology T) (proEtaleConstantRing T A))

private noncomputable def tensor_representative_iso (T : Scheme.{u})
    (A : Type u) [CommRing A]
    (L M P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (f : P ⟶ L) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := proEtaleConstantRing T A) P) :
    derivedTensor T A L M P f hf hP ≅
      (native_tensor T A).obj (DerivedCategory.Q.obj L, DerivedCategory.Q.obj M) := by
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).mpr hf
  exact RingedDerivedNative.tensorIso.{u + 1, u, 0} (ProEt.topology T)
    (proEtaleConstantRing T A) P M (Or.inl hP) ≪≫
    (native_tensor T A).mapIso ((asIso (DerivedCategory.Q.map f)).prod (Iso.refl _))

private theorem tensor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    (K L : proEtaleDerivedCategory T A) :
    Nonempty (proEtaleDerivedTensor T A K L ≅ (native_tensor T A).obj (K, L)) := by
  let K₀ : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ :=
    DerivedCategory.Q.objPreimage K
  let L₀ : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ :=
    DerivedCategory.Q.objPreimage L
  let ex := CochainComplex.exists_isKFlatResolutionGeneral K₀
  let P := Classical.choose ex
  let f := Classical.choose (Classical.choose_spec ex)
  have hf := (Classical.choose_spec (Classical.choose_spec ex)).2.2.1
  have hP := (Classical.choose_spec (Classical.choose_spec ex)).1
  exact ⟨tensor_representative_iso T A K₀ L₀ P f hf hP ≪≫
    (native_tensor T A).mapIso
      ((DerivedCategory.Q.objObjPreimageIso K).prod (DerivedCategory.Q.objObjPreimageIso L))⟩

private theorem tor_iff_tensor_vanishing (T : Scheme.{u})
    (A : Type u) [CommRing A] (K : proEtaleDerivedCategory T A) (a b : ℤ) :
    HasProEtaleTorAmplitude T A K a b ↔ a ≤ b ∧
      ∀ (M : proEtaleRingModules T (proEtaleConstantRing T A)) (i : ℤ),
        i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (proEtaleDerivedTensor T A K ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  constructor
  · intro h
    refine ⟨h.1, fun M i hi ↦ ?_⟩
    let L : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ :=
      DerivedCategory.Q.objPreimage K
    obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
    have hz := h.2 L P ⟨DerivedCategory.Q.objObjPreimageIso K⟩ f hf hP M i hi
    let e := tensor_representative_iso T A L
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) P f hf hP ≪≫
      (native_tensor T A).mapIso ((DerivedCategory.Q.objObjPreimageIso K).prod
        (((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm))
    obtain ⟨e'⟩ := tensor_iso T A K ((DerivedCategory.singleFunctor _ 0).obj M)
    exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (e' ≪≫ e.symm))
  · rintro ⟨hab, h⟩
    refine ⟨hab, ?_⟩
    rintro L P ⟨eL⟩ f hf hP M i hi
    obtain ⟨e⟩ := tensor_iso T A K ((DerivedCategory.singleFunctor _ 0).obj M)
    let e' := tensor_representative_iso T A L
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) P f hf hP ≪≫
      (native_tensor T A).mapIso (eL.prod
        (((DerivedCategory.singleFunctorIsoCompQ _ 0).app M).symm))
    exact (h M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso (e' ≪≫ e.symm))


private theorem constructible_of_iso (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A]
    {F G : proEtaleRingModules T (proEtaleConstantRing T A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf T A F) :
    IsConstructibleProEtaleModuleSheaf T A G := by
  apply (proEtaleModuleRestriction_constructible_iff T A G).mpr
  exact ProEtale.isConstructible_of_iso ((proEtaleModuleRestriction T A).mapIso e)
    ((proEtaleModuleRestriction_constructible_iff T A F).mp hF)

private theorem tor_of_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a b : ℤ)
    (hL : HasProEtaleTorAmplitude T A L a b) : HasProEtaleTorAmplitude T A K a b := by
  refine ⟨hL.1, ?_⟩
  rintro C P ⟨eC⟩ f hf hP M i hi
  exact hL.2 C P ⟨eC ≪≫ e⟩ f hf hP M i hi

private theorem open_cover_isZero (Z : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] (W : Fin 2 → Z.Opens)
    (hcover : ∀ x : Z, ∃ k, x ∈ W k)
    (M : proEtaleRingModules Z (proEtaleConstantRing Z A))
    (hM : ∀ k, IsZero ((proEtaleConstantRingPullback A (W k).ι).obj M)) :
    IsZero M := by
  have : (proEtaleModuleRestriction Z A).IsEquivalence :=
    proEtaleModuleRestriction_isEquivalence Z A
  apply IsZero.of_full_of_faithful_of_isZero (proEtaleModuleRestriction Z A) M
  apply ProEtale.isZero_of_forall_isZero_upperStar_obj
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) W hcover
  intro k
  obtain ⟨e⟩ := proEtaleModuleRestriction_pullback (W k).ι A M
  have : (proEtaleModuleRestriction (W k).toScheme A).IsEquivalence :=
    proEtaleModuleRestriction_isEquivalence (W k).toScheme A
  exact ((proEtaleModuleRestriction (W k).toScheme A).map_isZero (hM k)).of_iso e.symm

/-- At one finite coefficient ring, cohomological bounds, Tor bounds and intrinsic
constructibility descend from specified models on a binary open cover. The input
is any global derived object, with no tower or distinguished triangle required.

Source: the retained proof of lem-sp-tower-binary-ctf-fibre, steps 3--6;
Stacks Project, Tags 07A4, 08FZ and 09AJ
(blueprint: lem-sp-proetale-binary-ctf-local-models).

Proof: open inverse image is exact restriction under the pro-etale slice
identification and the constant-section ring comparison. It commutes with
cohomology and with the inverse intrinsic realization, since both are exact
and the scalar identifications act identically on constant sections. The two
selected isomorphisms therefore identify the restricted cohomology sheaves
with those of P and Q. A sheaf vanishing on U and V is zero: every test object
is covered by its two pullbacks, so separatedness detects zero sections. This
proves vanishing outside [a,b]. For each degree-zero module M, derived tensor
pullback identifies the two restrictions of K tensor^L M with P tensor^L M|U
and Q tensor^L M|V. Apply their Tor bounds and the same sheaf zero test, for
every M, to prove the global Tor bound with the unchanged interval [s,t].
For constructibility take the finite immersed strata for each local homology
sheaf. Keep the U-strata, and intersect the V-strata with the reduced closed
complement of U. The resulting finite family is disjoint and covers Z; each
stratum is locally closed and constructible because Z is Noetherian. Pull back
the local trivializing covers; constants and finite geometric stalks are
preserved by this base change. These strata witness exactly the fixed-module
intrinsic constructibility predicate. If Z is empty use its one empty stratum
with the zero constant module. No nonempty-open or nonzero-ring assumption is
used, and the intervals may have equal endpoints. -/
theorem proEtale_binary_ctf_of_local_models
    (Z : Scheme.{u}) [IsNoetherian Z] (U V : Z.Opens) (_hcover : U ⊔ V = ⊤)
    (A : Type u) [CommRing A] [Finite A] (a b s t : ℤ)
    (K : proEtaleDerivedCategory Z A)
    (P : proEtaleDerivedCategory U.toScheme A)
    (Q : proEtaleDerivedCategory V.toScheme A)
    (_aU : (proEtaleConstantRingDerivedPullback.{u} A U.ι).obj K ≅ P)
    (_aV : (proEtaleConstantRingDerivedPullback.{u} A V.ι).obj K ≅ Q)
    (_hP : (∀ i : ℤ, IsConstructibleProEtaleFixedModuleSheaf U.toScheme
      (ULift.{u + 1} A) ((DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2} _ i).obj
        ((Functor.mapDerivedCategory.{u + 2, u + 1}
          (sfIntrinsicModuleEquivalence.{u} U.toScheme A).inverse).obj P))) ∧
      (∀ i : ℤ, i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ i).obj P)) ∧
      HasProEtaleTorAmplitude U.toScheme A P s t)
    (_hQ : (∀ i : ℤ, IsConstructibleProEtaleFixedModuleSheaf V.toScheme
      (ULift.{u + 1} A) ((DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2} _ i).obj
        ((Functor.mapDerivedCategory.{u + 2, u + 1}
          (sfIntrinsicModuleEquivalence.{u} V.toScheme A).inverse).obj Q))) ∧
      (∀ i : ℤ, i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ i).obj Q)) ∧
      HasProEtaleTorAmplitude V.toScheme A Q s t) :
    (∀ i : ℤ, IsConstructibleProEtaleFixedModuleSheaf Z (ULift.{u + 1} A)
      ((DerivedCategory.homologyFunctor.{u + 1, u + 1, u + 2} _ i).obj
        ((Functor.mapDerivedCategory.{u + 2, u + 1}
          (sfIntrinsicModuleEquivalence.{u} Z A).inverse).obj K))) ∧
      (∀ i : ℤ, i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2} _ i).obj K)) ∧
      HasProEtaleTorAmplitude Z A K s t := by
  classical
  let W : Fin 2 → Z.Opens := ![U, V]
  have hW : ∀ x : Z, ∃ k : Fin 2, x ∈ W k := by
    intro x
    have hx : x ∈ U ⊔ V := _hcover.symm ▸ (show x ∈ (⊤ : Z.Opens) from trivial)
    rcases hx with hx | hx
    · exact ⟨0, hx⟩
    · exact ⟨1, hx⟩
  have hmodel (k : Fin 2) :
      (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf (W k).toScheme A
        ((DerivedCategory.homologyFunctor _ i).obj
          ((proEtaleConstantRingDerivedPullback A (W k).ι).obj K))) ∧
      (∀ i : ℤ, i < a ∨ b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((proEtaleConstantRingDerivedPullback A (W k).ι).obj K))) ∧
      HasProEtaleTorAmplitude (W k).toScheme A
        ((proEtaleConstantRingDerivedPullback A (W k).ι).obj K) s t := by
    fin_cases k
    · exact ⟨fun i ↦ constructible_of_iso U.toScheme A
        ((DerivedCategory.homologyFunctor _ i).mapIso _aU.symm)
        ((constructible_homology_iff U.toScheme A P i).mp (_hP.1 i)),
        fun i hi ↦ (_hP.2.1 i hi).of_iso
          ((DerivedCategory.homologyFunctor _ i).mapIso _aU),
        tor_of_iso U.toScheme A _aU s t _hP.2.2⟩
    · exact ⟨fun i ↦ constructible_of_iso V.toScheme A
        ((DerivedCategory.homologyFunctor _ i).mapIso _aV.symm)
        ((constructible_homology_iff V.toScheme A Q i).mp (_hQ.1 i)),
        fun i hi ↦ (_hQ.2.1 i hi).of_iso
          ((DerivedCategory.homologyFunctor _ i).mapIso _aV),
        tor_of_iso V.toScheme A _aV s t _hQ.2.2⟩
  have hfinite (k : Fin 2) : Set.Finite {i : ℤ |
      ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((proEtaleConstantRingDerivedPullback A (W k).ι).obj K))} := by
    apply (Set.finite_Icc a b).subset
    intro i hi
    constructor
    · by_contra h
      exact hi ((hmodel k).2.1 i (Or.inl (lt_of_not_ge h)))
    · by_contra h
      exact hi ((hmodel k).2.1 i (Or.inr (lt_of_not_ge h)))
  have hcover : ∀ x : Z, ∃ k : Fin 2, ∃ y : (W k).toScheme, (W k).ι.base y = x := by
    intro x
    obtain ⟨k, hk⟩ := hW x
    exact ⟨k, ⟨x, hk⟩, rfl⟩
  obtain ⟨_, hc, ht⟩ := finiteCoverCTFLocality Z inferInstance A 2
    (fun k ↦ (W k).toScheme) (fun k ↦ (W k).ι) (fun _ ↦ inferInstance)
    hcover K s t _hP.2.2.1 hfinite (fun k ↦ (hmodel k).1)
    (fun k ↦ ((tor_iff_tensor_vanishing (W k).toScheme A _ s t).mp (hmodel k).2.2).2)
  refine ⟨fun i ↦ (constructible_homology_iff Z A K i).mpr (hc i), ?_,
    (tor_iff_tensor_vanishing Z A K s t).mpr ⟨_hP.2.2.1, ht⟩⟩
  intro i hi
  apply open_cover_isZero Z A W hW
  intro k
  exact ((hmodel k).2.1 i hi).of_iso
    (((proEtaleConstantRingPullback A (W k).ι).mapDerivedCategoryHomologyFunctorIso i).app K)


end AlgebraicGeometry.Scheme

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
