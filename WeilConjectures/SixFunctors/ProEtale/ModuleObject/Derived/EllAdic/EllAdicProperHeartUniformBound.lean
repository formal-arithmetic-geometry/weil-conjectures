/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperConstructibleHeartBound
import WeilConjectures.AlgebraicGeometry.Proper.Heart.ProperHeartBoundRational
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralIndConstructibleHeartClosure
import all WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartCanonicalPresentation
import all WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartKernelsCokernels
import all WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleFilteredColimits
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleExtensions
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartFullFaithfulness
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
import all WeilConjectures.AlgebraicGeometry.NormedCoefficientRealization.NormedCoefficientRealization
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Uniform proper heart amplitude over a Noetherian base

The finite-amplitude part of the proper heart theorem, independently of coproduct
continuity. Source: Bhatt--Scholze, Section 6.8, and blueprint proper heart bound.
(blueprint: lem-sfb-noetherian-proper-heart-uniform-bound)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Sectionwise postcomposition, with the multiplication fixed as part of the ring object.
private noncomputable def continuousIso
    {A B : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} B) := by
  let eR : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := Profinite.continuousMapRingSheafMap e.toRingHom he
      inv := Profinite.continuousMapRingSheafMap e.symm.toRingHom hei
      hom_inv_id := by
        ext S f
        apply ULift.ext
        ext x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        ext x
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom eAb.hom
      inv := Mon.ofHom eAb.inv
      hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
      inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

-- A small-universe specialization of the normed coefficient realization construction.
private theorem field_model (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      ∃ σ : E ≃ₐ[ℚ_[ℓ]] F, Isometry σ := by
  let i : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let F := i.fieldRange
  let σ := i.equivFieldRange
  have : FiniteDimensional ℚ_[ℓ] F := σ.toLinearEquiv.finiteDimensional
  refine ⟨⟨F, inferInstance⟩, σ, ?_⟩
  exact NormedCoefficientRealization.embedding_isometry ℓ
    (fun x ↦ norm_algebraMap' E x) (fun x ↦ norm_algebraMap' F x) σ.toAlgHom

private theorem unitBall_realization (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (O : Subring E) (hO : ∀ x : E, x ∈ O ↔ ‖x‖ ≤ 1) :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} O) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ F)) := by
  obtain ⟨F, σ, hiso⟩ := field_model ℓ E
  have hmem (x : E) : x ∈ O ↔ σ x ∈ PadicAlgCl.integers ℓ F := by
    rw [hO, PadicAlgCl.mem_integers_iff]
    change ‖x‖ ≤ 1 ↔ ‖σ x‖₊ ≤ 1
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]
    rw [(AddMonoidHomClass.isometry_iff_norm σ).mp hiso x]
  let ei := σ.toRingEquiv.restrict O (PadicAlgCl.integers ℓ F) hmem
  have hi : Isometry ei := fun x y ↦ hiso x.val y.val
  have hii : Isometry ei.symm := fun x y ↦ by
    simpa only [ei.apply_symm_apply] using (hi (ei.symm x) (ei.symm y)).symm
  exact ⟨F, ⟨continuousIso ei hi.continuous hii.continuous⟩⟩

-- Minimality transports all closure operations at once along the exact equivalence.
private theorem coproductClosure_comap {Z : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}} [MonObj R] [MonObj S]
    [IsCommMonObj R] [IsCommMonObj S] (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R}
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstructibleModuleObject R) M) :
    ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstructibleModuleObject S) ((Mod.comap φ).obj M) := by
  let F : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) S := Mod.comap φ
  let Q := ObjectProperty.weakSerreCoproductClosure.{u + 1}
    (IsConstructibleModuleObject S)
  have : F.IsEquivalence := (Mod.comapEquivalenceOfIsIso φ).isEquivalence_functor
  exact hM (Q.inverseImage F)
    (fun N hN ↦ ObjectProperty.le_weakSerreCoproductClosure _ _
      (_root_.constructible_comap φ hN))
    inferInstance inferInstance inferInstance inferInstance
    (fun _ ↦ inferInstance)

private theorem bound_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (h : ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ' Z M →
      (R((p)_*⟦Λ'⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d) :
    ∃ d : ℤ, ∀ M, constructibleCoproductClosure Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, fun M hM ↦ ?_⟩
  let φ := coefficientMap e.inv.hom Z
  let ψ := coefficientMap e.inv.hom Y
  have : IsIso φ := by dsimp [φ, coefficientMap]; infer_instance
  have : IsIso ψ := by dsimp [ψ, coefficientMap]; infer_instance
  have hb : (R((p)_*⟦Λ'⟧).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((Mod.comap φ).obj M))).IsLE d :=
    hd ((Mod.comap φ).obj M) (coproductClosure_comap φ hM)
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  let es := ((Mod.comap φ).mapDerivedCategorySingleFunctor 0).app M
  have hflat (T : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom T)) := by
    have : IsIso (coefficientMap e.inv.hom T) := by
      dsimp [coefficientMap]
      infer_instance
    exact preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoComapInv (coefficientMap e.inv.hom T)).symm
  let ep := (derivedComapLowerStarIso e.inv.hom p).app K
  have ht : ((Mod.comap ψ).mapDerivedCategory.obj (R((p)_*⟦Λ⟧).obj K)).IsLE d := by
    rw [DerivedCategory.isLE_iff] at hb ⊢
    intro i hi
    exact (hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      (ep ≪≫ (R((p)_*⟦Λ'⟧)).mapIso es))
  exact (NormedCoefficientRealization.bounds_comap ψ _ d).1.mp ht

private theorem qbar_closure_le_ind (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [IsNoetherian X] :
    constructibleCoproductClosure (Profinite.padicAlgClRingObj ℓ) X ≤
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X) := by
  let Λ := Profinite.padicAlgClRingObj.{u} ℓ
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X
  let Q := ObjectProperty.ind.{u + 1} P
  have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} _ :=
    fun M hM ↦ (indHeart_fullFaithfulness ℓ X).2.1 ⟨M, hM⟩
  have hcoeff := (coefficientHeart_closure ℓ
    (Profinite.padicAlgClCondensedRing ℓ) (Or.inr rfl)).2 X
  let : Abelian (ConstantModelConstructible Λ X) := hcoeff.2.2.2.1.some
  let : PreservesFiniteColimits P.ι := hcoeff.2.2.2.2.2.1
  have hsmall := coefficientHeart_essentiallySmall ℓ
    (Profinite.padicAlgClCondensedRing.{u} ℓ) (Or.inr rfl) X
  have hpres := canonicalPresentation_of_finitePresentation Λ X hsmall
    (fun A ↦ hfp A.obj A.property)
  have hker := assertions_of_ring ℓ (Profinite.padicAlgClCondensedRing ℓ)
    (Or.inr rfl) X hpres
  have : Q.IsClosedUnderKernels := ⟨by
    rintro _ ⟨S, c, hc, hS⟩
    exact Q.prop_of_iso (hc.conePointUniqueUpToIso (kernelIsKernel S)).symm
      ((hker _ _ S hS.1 hS.2).2.2.2.2.2.2.2.1)⟩
  have : Q.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨S, c, hc, hS⟩
    exact Q.prop_of_iso (hc.coconePointUniqueUpToIso (cokernelIsCokernel S)).symm
      ((hker _ _ S hS.1 hS.2).2.2.2.2.2.2.2.2)⟩
  have : Q.IsClosedUnderExtensions := ⟨fun hS h₁ h₃ ↦
    indConstructible_of_shortExact_padicAlgCl ℓ X _ hS h₁ h₃⟩
  have hsum (J : Type (u + 1)) : Q.IsClosedUnderColimitsOfShape (Discrete J) := by
    constructor
    rintro M ⟨h⟩
    let B : J → _ := fun j ↦ h.diag.obj ⟨j⟩
    let e : h.diag ≅ Discrete.functor B := Discrete.natIsoFunctor
    let c : Cofan B := (Cocone.precompose e.inv).obj h.cocone
    have hc : IsColimit c := (IsColimit.precomposeInvEquiv e _).symm h.isColimit
    exact _root_.ind_coproduct P hfp (constructible_finite_coproduct Λ X)
      J B c hc (fun j ↦ h.prop_diag_obj ⟨j⟩)
  intro M hM
  exact hM Q (fun N hN ↦ ObjectProperty.le_ind P N
    (((adicConstructibilityPredicateComparison ℓ X Λ .algebraicClosure).1 N).mp hN))
    inferInstance inferInstance inferInstance inferInstance hsum

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference in the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
private theorem higherDirectImage_filtered
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p] (q : ℤ) :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1}
      (DerivedCategory.singleFunctor _ 0 ⋙ R((p)_*⟦Λ⟧) ⋙
        DerivedCategory.homologyFunctor _ q) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  have : HasColimitsOfSize.{u + 1, u + 1} A := inferInstance
  let S := CochainComplex.singleFunctor A 0
  let T := DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ p).rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor _ q
  constructor
  intro I _ _
  have : HasColimitsOfShape I (CochainComplex A ℤ) := inferInstance
  constructor
  intro M
  have : PreservesColimit M S := by
    change PreservesColimit M (HomologicalComplex.single A (.up ℤ) 0)
    infer_instance
  let D := M ⋙ S
  let π := Functor.whiskerLeft D ((ComplexShape.embeddingUpIntGE 0).πTruncGENatTrans A)
  have hπ (i : I) : IsIso (π.app i) := by
    change IsIso (((S.obj (M.obj i))).πTruncGE 0)
    infer_instance
  have : IsIso π := NatIso.isIso_of_isIso_app π
  have hc : IsColimit (condensedContinuityCocone D 0) :=
    (IsColimit.precomposeHomEquiv (asIso π) _).symm (colimit.isColimit _)
  have ht : IsIso (condensedContinuityComparison D 0 T) :=
    condensed_qcqs_pushforward_continuity Λ p D 0
      (fun i n hn ↦ (S.obj (M.obj i)).isZero_of_isGE 0 n hn) q
  have hcT : IsColimit (T.mapCocone (condensedContinuityCocone D 0)) :=
    IsColimit.ofPointIso (colimit.isColimit (D ⋙ T)) (i := ht)
  have : PreservesColimit D T := preservesColimit_of_preserves_colimit_cocone hc hcT
  change PreservesColimit M (S ⋙ T)
  infer_instance

-- A finite bound for the geometric fibres of a proper morphism to a Noetherian scheme.
private theorem exists_geometricFibre_bound {Z Y : Scheme.{u}} [IsNoetherian Y]
    (p : Z ⟶ Y) [IsProper p] :
    ∃ d : ℕ, ∀ y : Y, topologicalKrullDim
      (pullback p (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y) : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_fibre_dimension_bound p
  refine ⟨d, fun y ↦ ?_⟩
  have he := topologicalKrullDim_pullback_eq_of_field
    (k := Y.residueField y) (pullback.snd p (Y.fromSpecResidueField y))
    (Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))))
  have hi := IsHomeomorph.topologicalKrullDim_eq _
    (pullbackLeftPullbackSndIso p (Y.fromSpecResidueField y)
      (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y)
          (AlgebraicClosure (Y.residueField y)))))).hom.homeomorph.isHomeomorph
  exact (hi.symm.trans he).le.trans (hd y)

-- Filtered colimits of constructibles keep a uniform bound, by qcqs continuity.
private theorem bound_of_ind
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) [QuasiCompact p] [QuasiSeparated p] (d : ℤ)
    (hb : ∀ M, IsConstantModelConstructible Λ Z M →
      (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hM : ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Z) M) :
    (R((p)_*⟦Λ⟧).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE d := by
  obtain ⟨I, hI, hfI, pres, hpres⟩ := hM
  rw [DerivedCategory.isLE_iff]
  intro r hr
  let H := DerivedCategory.singleFunctor _ 0 ⋙ R((p)_*⟦Λ⟧) ⋙
    DerivedCategory.homologyFunctor _ r
  have hH : PreservesFilteredColimitsOfSize.{u + 1, u + 1} H :=
    higherDirectImage_filtered Λ p r
  have : PreservesColimitsOfShape I H := hH.preserves_filtered_colimits I
  exact (pres.map H).isColimit.isZero_pt
    (Functor.isZero _ fun i ↦ (DerivedCategory.isLE_iff _ _).mp (hb _ (hpres i)) r hr)

-- The filtered-colimit closure of finite-field constructibles contains the Serre closure.
private theorem continuous_closure_le_ind (ℓ : ℕ) [Fact ℓ.Prime]
    (F : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) [IsNoetherian X] :
    constructibleCoproductClosure (Profinite.continuousMapRingObj F) X ≤
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.continuousMapRingObj F) X) := by
  let Λ := Profinite.continuousMapRingObj.{u} F
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X
  let Q := ObjectProperty.ind.{u + 1} P
  have hR : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), FiniteDimensional ℚ_[ℓ] E ∧
      Profinite.padicSubfieldCondensedRing ℓ F.1 = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Profinite.padicSubfieldCondensedRing ℓ F.1 = Profinite.padicAlgClCondensedRing ℓ :=
    Or.inl ⟨F.1, F.2, rfl⟩
  have hfp : P ≤ ObjectProperty.isFinitelyPresentable.{u + 1} _ :=
    fun M hM ↦ ((indHeart_fullFaithfulness ℓ X).1 F).1 ⟨M, hM⟩
  have hcoeff := (coefficientHeart_closure ℓ (Profinite.padicSubfieldCondensedRing ℓ F.1) hR).2 X
  let : Abelian (ConstantModelConstructible Λ X) := hcoeff.2.2.2.1.some
  let : PreservesFiniteColimits P.ι := hcoeff.2.2.2.2.2.1
  have hsmall := coefficientHeart_essentiallySmall ℓ
    (Profinite.padicSubfieldCondensedRing.{u} ℓ F.1) hR X
  have hpres := canonicalPresentation_of_finitePresentation Λ X hsmall
    (fun A ↦ hfp A.obj A.property)
  have hker := assertions_of_ring ℓ (Profinite.padicSubfieldCondensedRing ℓ F.1) hR X hpres
  have : Q.IsClosedUnderKernels := ⟨by
    rintro _ ⟨S, c, hc, hS⟩
    exact Q.prop_of_iso (hc.conePointUniqueUpToIso (kernelIsKernel S)).symm
      ((hker _ _ S hS.1 hS.2).2.2.2.2.2.2.2.1)⟩
  have : Q.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨S, c, hc, hS⟩
    exact Q.prop_of_iso (hc.coconePointUniqueUpToIso (cokernelIsCokernel S)).symm
      ((hker _ _ S hS.1 hS.2).2.2.2.2.2.2.2.2)⟩
  have : Q.IsClosedUnderExtensions := ⟨fun hS h₁ h₃ ↦
    indConstructible_of_shortExact ℓ F X _ hS h₁ h₃⟩
  have hsum (J : Type (u + 1)) : Q.IsClosedUnderColimitsOfShape (Discrete J) := by
    constructor
    rintro M ⟨h⟩
    let B : J → _ := fun j ↦ h.diag.obj ⟨j⟩
    let e : h.diag ≅ Discrete.functor B := Discrete.natIsoFunctor
    let c : Cofan B := (Cocone.precompose e.inv).obj h.cocone
    have hc : IsColimit c := (IsColimit.precomposeInvEquiv e _).symm h.isColimit
    exact _root_.ind_coproduct P hfp (constructible_finite_coproduct Λ X)
      J B c hc (fun j ↦ h.prop_diag_obj ⟨j⟩)
  intro M hM
  exact hM Q (fun N hN ↦ ObjectProperty.le_ind P N
    (((adicConstructibilityPredicateComparison ℓ X Λ (.continuous F)).1 N).mp hN))
    inferInstance inferInstance inferInstance inferInstance hsum

-- The filtered-colimit closure of integral constructibles contains the Serre closure.
private theorem integral_closure_le_ind (ℓ : ℕ) [Fact ℓ.Prime]
    (F : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) [IsNoetherian X] :
    constructibleCoproductClosure (Profinite.padicIntegersRingObj ℓ F) X ≤
      ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ F) X) := by
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ F
  let P : ObjectProperty _ := IsConstantModelConstructible Λ X
  let Q := ObjectProperty.ind.{u + 1} P
  obtain ⟨_, hker, hcoker, hext, hsum⟩ :=
    integralIndConstructibleHeartClosure_of_isNoetherian ℓ F X
  have hsum' (J : Type (u + 1)) : Q.IsClosedUnderColimitsOfShape (Discrete J) := by
    constructor
    rintro M ⟨h⟩
    let B : J → _ := fun j ↦ h.diag.obj ⟨j⟩
    let e : h.diag ≅ Discrete.functor B := Discrete.natIsoFunctor
    let c : Cofan B := (Cocone.precompose e.inv).obj h.cocone
    have hc : IsColimit c := (IsColimit.precomposeInvEquiv e _).symm h.isColimit
    exact hsum J B c hc (fun j ↦ h.prop_diag_obj ⟨j⟩)
  intro M hM
  exact hM Q (fun N hN ↦ ObjectProperty.le_ind P N
    (((adicConstructibilityPredicateComparison ℓ X Λ (.integral F)).1 N).mp hN))
    inferInstance hker hcoker hext hsum'

set_option linter.unusedVariables false in
/-- The uniform proper heart bound of `properLowerStar_uniformBound_continuousMapRingObj`, for the
coefficient ring `𝒪_E` of a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`.
(blueprint: lem-sfb-noetherian-proper-heart-uniform-bound) -/

set_option linter.unusedVariables false in
end AlgebraicGeometry.ProEtale.CondensedRing
