/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q25, D5
-/
module

public import Sheaf.Paper.ContinuousConstructibleModule
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import Sheaf.Paper.ContinuousCoefficientPullbackIso
import all Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import all WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.Topology.StratificationDense
import Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent
import Sheaf.Paper.ContinuousModuleEncodingLocalFreeness
import Sheaf.Paper.ContinuousModuleEncodingScalarExtension
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Algebra.TransferInstance
import all Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import all Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import all Sheaf.Paper.ContinuousModuleEncodingRestriction
import Sheaf.Paper.ContinuousLocallyFreePullback
import Sheaf.Paper.ContinuousEtaleLocalLattices
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.RingTheory.Finiteness.Small

/-!
# An integral lattice on a nonempty reduced open

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.13,
first paragraph, and Stacks Tag 03S0.
(blueprint: lem-weil-pbc-lisse-lattice-reduced-open)
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction
  CondensedRing.pullIso CondensedRing.upperStarComp
  CondensedRing.integralScalarMap

private theorem baseChange_cont {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.proEtaleBaseChange f).IsContinuous (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Y) := AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback f

attribute [local instance] baseChange_cont

set_option backward.isDefEq.respectTransparency false in
private def continuous_restriction_adjunction {X Y : Scheme.{u}}
    (f : Y ⟶ X) [WeaklyEtale f] (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)
    let : F.IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
      Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)
    letI : (Scheme.proEtaleBaseChange f).IsContinuous
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) := baseChange_cont f
    let R := latticeModuleRing X T
    let S := latticeModuleRing Y T
    let a : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj R :=
      ⟨{ app := fun _ ↦ 𝟙 _
         naturality := fun _ _ _ ↦ rfl }⟩
    let b : R ⟶ ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
        RingCat.{u + 1} (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)).obj S :=
      ⟨Functor.whiskerRight (continuousCoefficientDirectImageMap f T).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    SheafOfModules.pushforward a ⊣ SheafOfModules.pushforward b := by
  dsimp only
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) trivial
  apply SheafOfModules.pushforwardPushforwardAdj.{u + 1} adj
  · apply NatTrans.ext
    funext V
    apply RingCat.hom_ext
    ext s : 1
    apply ULift.ext
    ext x
    rfl
  · apply NatTrans.ext
    funext V
    apply RingCat.hom_ext
    ext s : 1
    apply ULift.ext
    ext x
    change s.down _ = s.down x
    congr 1
    change ((pullback.fst (V.unop.hom ≫ f) f).base
      ((pullback.lift (𝟙 V.unop.left) V.unop.hom (by simp)).base x)) = x
    simp only [← Scheme.Hom.comp_apply, pullback.lift_fst]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem continuous_restriction_iso {X Y : Scheme.{u}}
    (f : Y ⟶ X) [WeaklyEtale f] (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T]
    (M : SheafOfModules.{u + 1} (latticeModuleRing X T)) :
    let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)
    let : F.IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
      Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)
    let a : latticeModuleRing Y T ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (latticeModuleRing X T) :=
      ⟨{ app := fun _ ↦ 𝟙 _
         naturality := fun _ _ _ ↦ rfl }⟩
    Nonempty (continuousModulePullback f T M ≅ (SheafOfModules.pushforward a).obj M) := by
  let := LatticePullbackProof.continuousCoefficientInverseImageMap_isIso f T
  let c := asIso (continuousCoefficientInverseImageMap f T)
  let a := continuous_restriction_adjunction f T
  let b := Scheme.proEtaleRingModuleAdjunction f
    (latticeCoefficientSheaf X T) (latticeCoefficientSheaf Y T) c
  have hd : Scheme.proEtaleRingDirectImageMap f
      (latticeCoefficientSheaf X T) (latticeCoefficientSheaf Y T) c =
      continuousCoefficientDirectImageMap f T := by
    exact ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
      (continuousCoefficientDirectImageMap f T)
  unfold Scheme.proEtaleRingModuleDirectImage at b
  rw [hd] at b
  exact ⟨(b.leftAdjointUniq a).app M⟩

attribute [local irreducible] continuous_restriction_adjunction

private theorem exists_small_coefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[l] K)
      (_ : FiniteDimensional ℚ_[l] K), Nonempty (E ≃ₐ[ℚ_[l]] K) := by
  have : Small.{0} E := Module.Finite.small ℚ_[l] E
  let K := Shrink.{0} E
  let : Algebra ℚ_[l] K := (equivShrink E).symm.algebra ℚ_[l]
  let e : K ≃ₐ[ℚ_[l]] E := (equivShrink E).symm.algEquiv ℚ_[l]
  let : FiniteDimensional ℚ_[l] K := e.symm.toLinearEquiv.finiteDimensional
  exact ⟨K, inferInstance, inferInstance, inferInstance, ⟨e.symm⟩⟩

private theorem finite_cover_on_open (X : Scheme.{u}) [IsNoetherian X]
    [Nonempty X] [IsReduced X] {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (p : Y ⟶ X) [Etale p] [Surjective p] :
    ∃ U : X.Opens, Nonempty U ∧
      IsFinite (pullback.snd p U.ι) := by
  classical
  obtain ⟨S, _, hS⟩ := Scheme.exists_etale_stratified_finite p
  obtain ⟨x, hx⟩ := S.toStratification.dense_iUnion_interior_stratum.nonempty
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  let U : X.Opens := ⟨interior (S.stratum a), isOpen_interior⟩
  let i := S.immersion a
  let q := pullback.snd i U.ι
  have hq : Surjective q := by
    constructor
    intro u
    have hu : U.ι u ∈ Set.range i := by
      rw [S.range_immersion]
      exact interior_subset u.property
    obtain ⟨z, hz⟩ := hu
    obtain ⟨v, _, hv⟩ := Scheme.Pullback.exists_preimage_pullback z u hz
    exact ⟨v, hv⟩
  have : IsClosedImmersion q := IsClosedImmersion.of_isPreimmersion q (by
    rw [Set.range_eq_univ.mpr q.surjective]
    exact isClosed_univ)
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  let f : U.toScheme ⟶ S.domain a := inv q ≫ pullback.fst i U.ι
  have hf : f ≫ i = U.ι := by
    dsimp only [f]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simp [q]
  have := (hS a).1
  have := (hS a).2
  have : IsFinite (pullback.snd (pullback.snd p i) f) := inferInstance
  have : Etale (pullback.snd (pullback.snd p i) f) := inferInstance
  have h := (Scheme.finite_etale_pullback_comp p i f).1
  rw [hf] at h
  exact ⟨U, ⟨⟨x, ha⟩⟩, h⟩

open scoped CategoryTheory.Obj CategoryTheory.Functor
open CondensedRing in
private theorem scalar_square
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    {X Y V W : Scheme.{u}} (p : Y ⟶ X) (j : W ⟶ X)
    (r : V ⟶ Y) (q : V ⟶ W) (h : r ≫ p = q ≫ j)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y))
    (e : (Mod.extendScalars (coefficientMap φ Y)).obj M ≅
      (CondensedRing.upperStar B p).obj P) :
    Nonempty ((Mod.extendScalars (coefficientMap φ V)).obj
      ((CondensedRing.upperStar A r).obj M) ≅
      (CondensedRing.upperStar B q).obj ((CondensedRing.upperStar B j).obj P)) := by
  exact ⟨(pullIso φ r).app M ≪≫ (CondensedRing.upperStar B r).mapIso e ≪≫
    ((CondensedRing.upperStarComp B r p).app P).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar B f).obj P) h) ≪≫
    (CondensedRing.upperStarComp B q j).app P⟩

open CondensedRing in
private theorem internal_open_lattice (l : ℕ) [Fact l.Prime] (K : Type)
    [NormedField K] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (X : Scheme.{u}) [IsNoetherian X] [Nonempty X] [IsReduced X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj K) X))
    (hP : CondensedRing.LocallyFree _ P) :
    ∃ U : X.Opens, Nonempty U ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology U.toScheme) Ab.{u + 1})
          (condensedRingObj (integralCoeff l K) U.toScheme),
        CondensedRing.LocallyFree _ M ∧
        Nonempty ((Mod.extendScalars
          (coefficientMap (integralScalarMap l K) U.toScheme)).obj M ≅
            (CondensedRing.upperStar (Profinite.continuousMapRingObj K) U.ι).obj P) := by
  classical
  obtain ⟨Y, p, hp, hs, hc, hqs, M, hM, ⟨e⟩⟩ :=
    continuousLisse_etale_lattice l K X P hP
  have : Etale p := hp
  have : Surjective p := hs
  have : CompactSpace Y := hc
  have : QuasiSeparatedSpace Y := hqs
  obtain ⟨U, hU, hf⟩ := finite_cover_on_open X p
  let r := pullback.fst p U.ι
  let q := pullback.snd p U.ι
  have : IsFinite q := hf
  let M' := (CondensedRing.upperStar (integralCoeff l K) r).obj M
  let P' := (CondensedRing.upperStar (Profinite.continuousMapRingObj K) U.ι).obj P
  have hM' : CondensedRing.LocallyFree _ M' := locallyFree_upperStar _ r hM
  have hP' : CondensedRing.LocallyFree _ P' := locallyFree_upperStar _ U.ι hP
  obtain ⟨e'⟩ := scalar_square _ _ (integralScalarMap l K) p U.ι r q
    (pullback.condition (f := p) (g := U.ι)) P M e
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨N, hN, eN⟩ := continuousLisse_finiteEtale_lattice l K U.toScheme P' hP' q M' hM' ⟨e'⟩
  exact ⟨U, hU, N, hN, eN⟩

open CondensedRing in
private theorem field_inverse_locallyFree (l : ℕ) [Fact l.Prime] (K : Type)
    [NormedField K] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (X : Scheme.{u})
    (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l K X)))
    [M.IsFiniteLocallyFree] :
    CondensedRing.LocallyFree _ ((continuousFieldModuleEquivalence l K X).inverse.obj M) := by
  let : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : TotallyDisconnectedSpace K := inferInstance
  let F := continuousRingModuleEquivalence X K
  let e := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseFieldSheaf_eq l K X))
  let H := ringModuleEquivalenceOfIso X e
  let : (H.inverse.obj M).IsFiniteLocallyFree :=
    finiteLocallyFree_restrict (Scheme.ProEt.topology X) _ _ e.symm M
  let e' : H.inverse.obj M ≅ F.functor.obj (F.inverse.obj (H.inverse.obj M)) :=
    (F.counitIso.app _).symm
  let : (F.functor.obj (F.inverse.obj (H.inverse.obj M))).IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} e'
  exact (continuousRing_locallyFree_iff X K
    (F.inverse.obj (H.inverse.obj M))).mpr inferInstance

open CondensedRing in
private theorem integer_forward_locallyFree (l : ℕ) [Fact l.Prime] (K : Type)
    [NormedField K] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff l K) X))
    (hM : CondensedRing.LocallyFree _ M) :
    ((continuousIntegerModuleEquivalence l K X).functor.obj M).IsFiniteLocallyFree := by
  let : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : TotallyDisconnectedSpace K := inferInstance
  let : ((continuousRingModuleEquivalence X (continuousIntegers l K)).functor.obj
      M).IsFiniteLocallyFree :=
    (continuousRing_locallyFree_iff X (continuousIntegers l K) M).mp hM
  exact finiteLocallyFree_restrict (Scheme.ProEt.topology X) _ _
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (eqToIso (lisseIntegerSheaf_eq l K X))) _

section CoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K : Type) [Field K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
  (e : E ≃ₐ[ℚ_[l]] K)

private theorem coefficient_absolute (x : E) :
    Padic.coefficientExtensionAbsoluteValue l E x =
      Padic.coefficientExtensionAbsoluteValue l K (e x) := by
  change spectralNorm ℚ_[l] E x = spectralNorm ℚ_[l] K (e x)
  unfold spectralNorm
  rw [← minpoly.algEquiv_eq e x]

private def nativeFieldRingEquiv :
    WithAbs (Padic.coefficientExtensionAbsoluteValue l E) ≃+* K :=
  (WithAbs.equiv _).trans e.toRingEquiv

private theorem nativeField_isometry :
    letI := spectralNorm.normedField ℚ_[l] K
    Isometry (nativeFieldRingEquiv l E K e) := by
  let := spectralNorm.normedField ℚ_[l] K
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  exact (coefficient_absolute l E K e x.ofAbs).symm

private def nativeIntegerRingEquiv :
    latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l K :=
  (nativeFieldRingEquiv l E K e).restrict _ _ (by
    intro x
    change x.ofAbs ∈ Padic.coefficientExtensionIntegers l E ↔ _
    rw [coefficientIntegers_mem, coefficientIntegers_mem, coefficient_absolute l E K e]
    rfl)

private def nativeFieldIso (X : Scheme.{u}) :
    latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
      lisseFieldSheaf l K X := by
  letI := spectralNorm.normedField ℚ_[l] K
  let h : WithAbs (Padic.coefficientExtensionAbsoluteValue l E) ≃ᵢ K :=
    { (nativeFieldRingEquiv l E K e).toEquiv with
      isometry_toFun := nativeField_isometry l E K e }
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun V ↦
    (ULift.ringEquiv.trans ((continuousMapRingEquiv (nativeFieldRingEquiv l E K e)
      h.continuous h.symm.continuous V.unop.left).trans ULift.ringEquiv.symm)).toCommRingCatIso) ?_
  intro V W f
  rfl

private def nativeIntegerIso (X : Scheme.{u}) :
    latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      lisseIntegerSheaf l K X := by
  letI := spectralNorm.normedField ℚ_[l] K
  have hi : Isometry (nativeIntegerRingEquiv l E K e) := by
    intro x y
    exact nativeField_isometry l E K e x.val y.val
  let h : latticeCoefficientIntegers l E ≃ᵢ Padic.coefficientExtensionIntegers l K :=
    { (nativeIntegerRingEquiv l E K e).toEquiv with isometry_toFun := hi }
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun V ↦
    (ULift.ringEquiv.trans ((continuousMapRingEquiv (nativeIntegerRingEquiv l E K e)
      h.continuous h.symm.continuous V.unop.left).trans ULift.ringEquiv.symm)).toCommRingCatIso) ?_
  intro V W f
  rfl

private theorem native_coefficient_square (X : Scheme.{u}) :
    integralLatticeCoefficientMap X l E ≫ (nativeFieldIso l E K e X).hom =
      (nativeIntegerIso l E K e X).hom ≫ lisseIntegerToField l K X := by
  apply Sheaf.hom_ext
  ext V s
  rfl

end CoefficientTransport

attribute [local irreducible] CondensedRing.continuousFieldModuleEquivalence
  CondensedRing.ringModuleEquivalenceOfIso CondensedRing.upperStar

private theorem encoded_pullback_iso
    (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] (X : Scheme.{u}) {Y : Scheme.{u}}
    (f : Y ⟶ X) [Etale f]
    (eX : latticeModuleRing X T ≅ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l K X))
    (eY : latticeModuleRing Y T ≅ (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l K Y))
    (hsquare : eY.hom.hom ≫ lisseEtaleCoefficientIdentification l K f =
      ({ app := fun _ ↦ 𝟙 _
         naturality := fun _ _ _ ↦ rfl } : (latticeModuleRing Y T).obj ⟶
          (lisseEtaleSiteInclusion f).op ⋙ (latticeModuleRing X T).obj) ≫
        (lisseEtaleSiteInclusion f).op.whiskerLeft eX.hom.hom)
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X T)) :
    let FE := CondensedRing.continuousFieldModuleEquivalence l K
    let GX := CondensedRing.ringModuleEquivalenceOfIso X eX
    let GY := CondensedRing.ringModuleEquivalenceOfIso Y eY
    Nonempty (GY.functor.obj ((FE Y).functor.obj
      ((CondensedRing.upperStar (Profinite.continuousMapRingObj K) f).obj
        ((FE X).inverse.obj (GX.inverse.obj L)))) ≅
      continuousModulePullback f T L) := by
  let FE := CondensedRing.continuousFieldModuleEquivalence l K
  let GX := CondensedRing.ringModuleEquivalenceOfIso X eX
  let GY := CondensedRing.ringModuleEquivalenceOfIso Y eY
  let P := (FE X).inverse.obj (GX.inverse.obj L)
  obtain ⟨er⟩ := CondensedRing.continuousField_module_restriction l K X Y f P
  let F := lisseEtaleSiteInclusion f
  let : F.IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)
  let j := lisseEtaleCoefficientIdentification l K f
  let j' : (latticeModuleRing Y
      T).obj ⟶
      F.op ⋙ (latticeModuleRing X
        T).obj :=
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ _ ↦ rfl }
  let er' := er ≪≫ (PresheafOfModules.pushforward j).mapIso
    ((SheafOfModules.forget _).mapIso ((FE X).counitIso.app (GX.inverse.obj L)))
  obtain ⟨en⟩ := CondensedRing.ringModule_restrictionOfIso X Y F eX eY j j'
    hsquare (GX.inverse.obj L) _ er'
  let a : latticeModuleRing Y T ⟶
      (F.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          (latticeModuleRing X T) := ⟨j'⟩
  let ec := GX.counitIso.app L
  let en' := en ≪≫ (PresheafOfModules.pushforward j').mapIso
    ((SheafOfModules.forget _).mapIso ec)
  obtain ⟨ei⟩ := continuous_restriction_iso f
    T L
  let e0 := (SheafOfModules.fullyFaithfulForget _).preimageIso
    (Y := (SheafOfModules.pushforward a).obj L) en'
  exact ⟨e0 ≪≫ ei.symm⟩


section CoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
  (e : E ≃ₐ[ℚ_[l]] K)

private theorem native_restriction_square (X : Scheme.{u}) {Y : Scheme.{u}}
    (f : Y ⟶ X) [Etale f] :
    let eX := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X)
    let eY := (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e Y)
    eY.hom.hom ≫ lisseEtaleCoefficientIdentification l K f =
      ({ app := fun _ ↦ 𝟙 _
         naturality := fun _ _ _ ↦ rfl } : (latticeModuleRing Y
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj ⟶
        (lisseEtaleSiteInclusion f).op ⋙ (latticeModuleRing X
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj) ≫
        (lisseEtaleSiteInclusion f).op.whiskerLeft eX.hom.hom := by
  ext V s
  rfl

attribute [local irreducible] nativeFieldIso nativeIntegerIso

private theorem native_pullback_iso (X : Scheme.{u}) {Y : Scheme.{u}}
    (f : Y ⟶ X) [Etale f]
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))) :
    let FE := CondensedRing.continuousFieldModuleEquivalence l K
    let GX := CondensedRing.ringModuleEquivalenceOfIso X
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X))
    let GY := CondensedRing.ringModuleEquivalenceOfIso Y
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e Y))
    Nonempty (GY.functor.obj ((FE Y).functor.obj
      ((CondensedRing.upperStar (Profinite.continuousMapRingObj K) f).obj
        ((FE X).inverse.obj (GX.inverse.obj L)))) ≅
      continuousModulePullback f (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L) := by
  let T := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let : IsUltrametricDist T :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (by
      intro x y
      exact isNonarchimedean_spectralNorm (K := ℚ_[l]) (L := E) x.ofAbs y.ofAbs)
  let : TotallyDisconnectedSpace T := inferInstance
  exact encoded_pullback_iso l K T X f
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X))
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e Y))
    (native_restriction_square l E K e X f) L

attribute [local semireducible] CondensedRing.ringModuleEquivalenceOfIso

attribute [local semireducible] CondensedRing.upperStar

private theorem native_scalar_iso (X : Scheme.{u})
    (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l K X))) :
    let GI := CondensedRing.ringModuleEquivalenceOfIso X
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeIntegerIso l E K e X))
    let GE := CondensedRing.ringModuleEquivalenceOfIso X
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X))
    Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (integralLatticeCoefficientMap X l E)
        (GI.functor.obj M) ≅
      GE.functor.obj (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (lisseIntegerToField l K X) M)) := by
  let J := Scheme.ProEt.topology X
  let R := latticeCoefficientSheaf X (latticeCoefficientIntegers l E)
  let S := latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
  let R' := lisseIntegerSheaf l K X
  let S' := lisseFieldSheaf l K X
  let er := (nativeIntegerIso l E K e X).symm
  let es := (nativeFieldIso l E K e X).symm
  let a := integralLatticeCoefficientMap X l E
  let a' := lisseIntegerToField l K X
  have hs : a' ≫ es.hom = er.hom ≫ a := by
    dsimp only [a, a', er, es]
    apply (cancel_mono (nativeFieldIso l E K e X).hom).mp
    simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
    rw [native_coefficient_square l E K e X]
    simp
  let t := coefficientTensorPresheafIso.{u} J a a' er es hs M
  let forgetRing := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  exact ⟨(PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1}
    (R := forgetRing.obj S) (𝟙 _)).mapIso t ≪≫
    pushforwardSheafificationIso.{u} J J (𝟭 X.ProEt)
      (forgetRing.obj S') (forgetRing.obj S) (forgetRing.map es.inv)
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a' M)⟩

end CoefficientTransport

attribute [local semireducible] CondensedRing.ringModuleEquivalenceOfIso
  CondensedRing.continuousFieldModuleEquivalence CondensedRing.upperStar

/-- A lisse rational coefficient module has a lisse integral lattice on a nonempty
quasi-compact open of a nonempty reduced noetherian finite-dimensional scheme.
The coefficient type `WithAbs` equips the field with its canonical extended p-adic
absolute value; `latticeCoefficientIntegers` is its ring of integers. The ringed
pullback along the open immersion is `j⁻¹ L`, with its coefficient action identified
by the canonical continuous-function comparison. No constant or positive rank is required.

Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph; Stacks Tags 03S0 and 0356.
(blueprint: lem-weil-pbc-lisse-lattice-reduced-open)

Proof:
1. Finite dimensionality gives an algebra-isomorphic small coefficient field. The
   equivalence preserves minimal polynomials and the spectral absolute value, hence
   identifies both continuous coefficient sheaves and their integral scalar maps.
2. The continuous etale-local lattice theorem gives a qcqs etale surjection Y to X
   and a locally finite free integral lattice on Y.
3. Apply finite-etale stratification to Y to X. The interiors of the finitely many
   locally closed strata have dense union, so one interior U is nonempty.
4. The pullback of the chosen stratum to U is a surjective immersion, hence a closed
   immersion. As U is reduced, this morphism is an isomorphism. Its inverse gives
   an actual map from U to the stratum; pullback pasting makes Y_U to U finite etale.
5. Pull back the lattice to Y_U and compose scalar and inverse-image comparison
   isomorphisms. Finite-etale lattice descent gives a locally finite free lattice on U.
6. Transport its continuous-module encoding to the original coefficients. The tensor
   comparison identifies rationalization. Composition of site objects is left adjoint
   to base change, and their coefficient maps satisfy the adjunction equations
   pointwise. Uniqueness of left adjoints identifies restriction with the canonical
   ringed pullback in the conclusion.
7. The noetherian space U makes its open immersion quasi-compact. The construction
   allows varying ranks and rank zero. -/
theorem exists_lisse_lattice_reduced_open
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X] [Nonempty X] [IsReduced X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (L : ringedSiteModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (_hL : L.IsFiniteLocallyFree) :
    ∃ U : X.Opens, Nonempty U ∧ QuasiCompact U.ι ∧
      ∃ M : ringedSiteModules.{u + 1}
          (latticeModuleRing U.toScheme (latticeCoefficientIntegers l E)),
        M.IsFiniteLocallyFree ∧
        Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (integralLatticeCoefficientMap U.toScheme l E) M ≅
          continuousModulePullback U.ι
            (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L) := by
  classical
  have := _hL
  obtain ⟨K, hK, hAK, hFK, ⟨e⟩⟩ := exists_small_coefficient l E
  let := hK
  let := hAK
  let := hFK
  let := spectralNorm.normedField ℚ_[l] K
  let := spectralNorm.normedAlgebra ℚ_[l] K
  let FE := CondensedRing.continuousFieldModuleEquivalence l K
  let FI := CondensedRing.continuousIntegerModuleEquivalence l K
  let er X := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X)
  let ea X := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeIntegerIso l E K e X)
  let GX := CondensedRing.ringModuleEquivalenceOfIso X (er X)
  let L' := GX.inverse.obj L
  have : L'.IsFiniteLocallyFree :=
    finiteLocallyFree_restrict (Scheme.ProEt.topology X) _ _ (er X).symm L
  let P := (FE X).inverse.obj L'
  have hP : CondensedRing.LocallyFree _ P := field_inverse_locallyFree l K X L'
  obtain ⟨U, hU, N, hN, ⟨eN⟩⟩ := internal_open_lattice l K X P hP
  let M := (FI U.toScheme).functor.obj N
  have : M.IsFiniteLocallyFree := integer_forward_locallyFree l K U.toScheme N hN
  let GI := CondensedRing.ringModuleEquivalenceOfIso U.toScheme (ea U.toScheme)
  let GE := CondensedRing.ringModuleEquivalenceOfIso U.toScheme (er U.toScheme)
  have hM : (GI.functor.obj M).IsFiniteLocallyFree :=
    finiteLocallyFree_restrict (Scheme.ProEt.topology U.toScheme) _ _ (ea U.toScheme) M
  obtain ⟨eS⟩ := CondensedRing.continuousModuleEncoding_scalar_extension l K U.toScheme M
  let eS' := (FE U.toScheme).functor.mapIso
    ((Mod.extendScalars (coefficientMap
      (CondensedRing.integralScalarMap l K) U.toScheme)).mapIso
        ((FI U.toScheme).unitIso.app N)) ≪≫ eS
  have hqc : QuasiCompact U.ι := inferInstance
  obtain ⟨es⟩ := native_scalar_iso l E K e U.toScheme M
  obtain ⟨ep⟩ := native_pullback_iso l E K e X U.ι L
  refine ⟨U, hU, hqc, GI.functor.obj M, hM, ⟨?_⟩⟩
  exact es ≪≫
    GE.functor.mapIso (eS'.symm ≪≫ (FE U.toScheme).functor.mapIso eN) ≪≫
      ep

end AlgebraicGeometry.ProEtale

#print axioms AlgebraicGeometry.ProEtale.exists_lisse_lattice_reduced_open
