/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.SixFunctors.OpenClosedWeilMateData
import Sheaf.Paper.IntegralSupportFunctorNormalization
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.AutomorphismConstructibleStageEquivalence
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.SixFunctors.OpenClosedWeilMateCompletion

/-! # Integral restriction and normalized completion transport -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v uX vX uU vU uZ vZ
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport
private theorem fiber_complement (D : FiniteFieldDatum.{u})
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))} (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    (h : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ) :
    Set.range (zlFiberMap D j₀) = (Set.range (zlFiberMap D i₀))ᶜ := by
  have h' : Set.range j₀.left = (Set.range i₀.left)ᶜ := by
    change Set.range i₀.left = (Set.range j₀.left)ᶜ at h
    rw [h, compl_compl]
  simp only [zlFiberMap, Over.pullback_map_left]
  let t := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have hm {V₀ : Over (Spec (.of D.k₀))} (f₀ : V₀ ⟶ X₀) :
      pullback.lift (pullback.fst V₀.hom t ≫ f₀.left) (pullback.snd V₀.hom t)
          (by simp [pullback.condition]) =
        pullback.map V₀.hom t X₀.hom t f₀.left (𝟙 _) (𝟙 _)
          (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp
  rw [hm j₀, hm i₀]
  erw [Scheme.Pullback.range_map, Scheme.Pullback.range_map]
  have hid : (⇑(𝟙 (Spec (.of D.k))) : Spec (.of D.k) → Spec (.of D.k)) = id := rfl
  simp only [hid, Set.range_id, Set.preimage_univ, Set.inter_univ, h', Set.preimage_compl]

private def completedPush_iso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PurCompactSupport.push (PurCompactSupport.completed l E) f ≅
      sfCompletedDerivedDirectImage l E f := by
  have hc : proEtaleRingDirectImageMap f
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (completedIntegralCommRingSheafUnrestricted l E X)
      (asIso (PurCompactSupport.completedPullMap l E f)) = sfCompletedCoefficientMap l E f := by
    change (proEtaleSheafAdjunction f CommRingCat).homEquiv _ _
      (((proEtaleSheafAdjunction f CommRingCat).homEquiv _ _).symm
        (sfCompletedCoefficientMap l E f)) = _
    exact Equiv.apply_symm_apply _ _
  change (proEtaleRingModuleDirectImage f
    ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring X)
    ((PurCompactSupport.completed l E).pull f)).rightDerivedFunctor ≅ _
  have hm : proEtaleRingModuleDirectImage f
      ((PurCompactSupport.completed l E).ring Y)
      ((PurCompactSupport.completed l E).ring X)
      ((PurCompactSupport.completed l E).pull f) = sfCompletedModuleDirectImage l E f := by
    unfold proEtaleRingModuleDirectImage sfCompletedModuleDirectImage
    erw [hc]
  have : (sfCompletedModuleDirectImage l E f).Additive := by
    rw [← hm]
    infer_instance
  exact Functor.rightDerivedFunctorNatIso (eqToIso hm)

private theorem restricted_of_preservation
    {X : Type uX} [Category.{vX} X] {U : Type uU} [Category.{vU} U]
    {Z : Type uZ} [Category.{vZ} Z]
    (PX : ObjectProperty X) (PU : ObjectProperty U) (PZ : ObjectProperty Z)
    {jL : U ⥤ X} {jR : X ⥤ U} {iL : X ⥤ Z} {iR : Z ⥤ X}
    (adjJ : jL ⊣ jR) (adjI : iL ⊣ iR)
    {FX : X ⥤ X} {FU : U ⥤ U} {FZ : Z ⥤ Z}
    (b : jR ⋙ FU ≅ FX ⋙ jR) (d : iL ⋙ FZ ≅ FX ⋙ iL)
    (hAlpha : ∀ N, PU N → IsIso ((openClosedAlpha adjJ b).app N))
    (hc : ∀ M, PZ M → IsIso ((openClosedC adjI d).app M))
    (hpres : ∀ K, PX K → PU (jR.obj K) ∧ PZ (iL.obj K) ∧
      PX (jL.obj (jR.obj K)) ∧ PX (iR.obj (iL.obj K))) :
    RestrictedOpenClosedWeilMateAssertions PX PU PZ jL jR iL iR
      adjJ adjI FX FU FZ b d := by
  refine ⟨hAlpha, hc, ?_, ?_, ?_⟩
  · intro N _
    simp [openClosedAlpha, mateEquiv]
  · intro M _
    simp [openClosedC, mateEquiv]
  · intro K hK
    obtain ⟨hU, hZ, hA, hC⟩ := hpres K hK
    have := hAlpha _ hU
    have := hc _ hZ
    let a := (asIso ((openClosedAlpha adjJ b).app (jR.obj K))).symm
    let c := asIso ((openClosedC adjI d).app (iL.obj K))
    refine ⟨hU, hZ, hA, hC, a, c, rfl, rfl, ?_, ?_⟩
    · have h := mateEquiv_counit_symm adjJ adjJ b.hom K
      change jL.map (b.hom.app K) ≫ adjJ.counit.app (FX.obj K) =
        a.inv ≫ FX.map (adjJ.counit.app K) at h
      rw [h, ← Category.assoc]
      simp
    · have h := unit_mateEquiv adjI adjI d.inv K
      change FX.map (adjI.unit.app K) ≫ c.hom =
        adjI.unit.app (FX.obj K) ≫ iR.map (d.inv.app K) at h
      rw [← Category.assoc, h, Category.assoc, ← iR.map_comp]
      simp

private theorem pushforward_of_ringIso_isEquivalence
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R) :
    (SheafOfModules.pushforward.{u + 1} (F := e.inverse) c.hom).IsEquivalence := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact inferInstanceAs
    (SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂).functor.IsEquivalence


private theorem geometricPull_isEquivalence {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : PurCompactSupport.Coefficients.{u}) : (PurCompactSupport.pull R g).IsEquivalence := by
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  let : (proEtaleBaseChange g).IsEquivalence :=
    adj.isEquivalence_right_of_isEquivalence_left
  let e : X.ProEt ≌ Y.ProEt :=
    { functor := proEtaleIsoPostcompose g
      inverse := proEtaleBaseChange g
      unitIso := asIso adj.unit
      counitIso := asIso adj.counit
      functor_unitIso_comp := adj.left_triangle_components }
  let : e.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  let : e.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) := by
    change (proEtaleBaseChange g).IsContinuous _ _
    infer_instance
  let a := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  let : IsIso a.unit :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g CommRingCat.{u + 1}).2.1
  let : IsIso (proEtaleRingDirectImageMap g (R.ring Y) (R.ring X) (R.pull g)) := by
    unfold proEtaleRingDirectImageMap
    infer_instance
  let d : R.ring Y ≅ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj (R.ring X) :=
    asIso (proEtaleRingDirectImageMap g (R.ring Y) (R.ring X) (R.pull g))
  let RX := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.ring X)
  let RY := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.ring Y)
  let c : RY ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X)).obj RX :=
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso d
  let : (proEtaleRingModuleDirectImage g (R.ring Y) (R.ring X)
      (R.pull g)).IsEquivalence :=
    show (SheafOfModules.pushforward.{u + 1} (F := e.inverse) c.hom).IsEquivalence from
      pushforward_of_ringIso_isEquivalence _ _ e RX RY c
  let : (proEtaleRingModulePullback g (R.ring Y) (R.ring X)
      (R.pull g)).IsEquivalence :=
    (proEtaleRingModuleAdjunction g (R.ring Y) (R.ring X)
      (R.pull g)).isEquivalence_left_of_isEquivalence_right
  exact Functor.isEquivalence_mapDerivedCategory _


private theorem fiber_separated
    (D : FiniteFieldDatum.{u}) (T₀ : Over (Spec (.of D.k₀))) [IsSeparated T₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    IsSeparated (D.geometricFiber T₀).hom := by
  exact inferInstanceAs (IsSeparated (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

private theorem integral_from_normalization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left]
    (hij : Set.range (zlFiberMap D j₀) = (Set.range (zlFiberMap D i₀))ᶜ)
    : sfIntegralOpenClosedWeilMateAssertions D l E j₀ i₀ := by
  have : Fact (l ≠ D.p) := ⟨hl⟩
  have : IsOpenImmersion (zlFiberMap D j₀) :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) j₀ inferInstance
  have : IsClosedImmersion (zlFiberMap D i₀) :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion)
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) i₀ inferInstance
  have : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact (D.geometricFiber X₀).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsSeparated (D.geometricFiber X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let xOver : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    OverClass.fromOver (D.geometricFiber X₀)
  have hsep : IsSeparated ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
    change IsSeparated (D.geometricFiber X₀).hom
    infer_instance
  have hft : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType (D.geometricFiber X₀).hom
    infer_instance
  have hqc : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
    change QuasiCompact (D.geometricFiber X₀).hom
    infer_instance
  obtain ⟨N⟩ := @IntegralSupportNormalization.integralSupportFunctorNormalization l _ E _ _ _ D hl
    (D.geometricFiber Z₀).left (D.geometricFiber U₀).left (D.geometricFiber X₀).left
    xOver hft hqc hsep (zlFiberMap D i₀) (zlFiberMap D j₀)
    inferInstance inferInstance hij
  let R := PurCompactSupport.completed l E
  let sj := N.openPull
  let ei : sfOrdinaryDerivedPull l E (zlFiberMap D i₀) ≅
      PurCompactSupport.pull R (zlFiberMap D i₀) :=
    Adjunction.leftAdjointUniq (sfOrdinaryDerivedAdjunction l E (zlFiberMap D i₀))
      ((proEtaleRingDerivedAdjunction (zlFiberMap D i₀) (R.ring _) (R.ring _)
        (R.pull (zlFiberMap D i₀))).ofNatIsoRight
          (completedPush_iso l E (zlFiberMap D i₀)))
  let si := N.closedPull ≪≫ Functor.isoWhiskerLeft
    (sfIntegralConstructible l E (D.geometricFiber X₀).left).ι ei
  have := geometricPull_isEquivalence (D.geometricFrobenius X₀).hom R
  have := geometricPull_isEquivalence (D.geometricFrobenius U₀).hom R
  have := geometricPull_isEquivalence (D.geometricFrobenius Z₀).hom R
  apply restricted_of_preservation _ _ _ _ _ _ _
  · intro M _
    have : IsIso (openClosedAlpha (PurCompactSupport.openDerivedAdjunction R
        (zlFiberMap D j₀)) (zlAmbientFrobeniusSquare D j₀ l E)) :=
      isIso_inverseMate_of_equivalences _ _ _
    infer_instance
  · intro M _
    let adj := proEtaleRingDerivedAdjunction (zlFiberMap D i₀) (R.ring _) (R.ring _)
      (R.pull (zlFiberMap D i₀))
    have : IsIso (openClosedC adj (zlAmbientFrobeniusSquare D i₀ l E)) :=
      isIso_mateEquiv_of_isEquivalence_of_fullyFaithful adj adj _ _
        (zlAmbientFrobeniusSquare D i₀ l E).symm
    infer_instance
  · intro K hK
    let K' : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left := ⟨K, hK⟩
    have hU := (sfIntegralConstructible l E (D.geometricFiber U₀).left).prop_of_iso
      (sj.app K') ((constructibleIntegralPullback l E (zlFiberMap D j₀)).obj K').property
    have hZ := (sfIntegralConstructible l E (D.geometricFiber Z₀).left).prop_of_iso
      (si.app K') ((constructibleIntegralPullback l E (zlFiberMap D i₀)).obj K').property
    refine ⟨hU, hZ, ?_, ?_⟩
    · exact N.openConstructible ⟨_, hU⟩
    · exact (sfIntegralConstructible l E _).prop_of_iso
        ((completedPush_iso l E (zlFiberMap D i₀)).app _).symm
        (N.closedConstructible ⟨_, hZ⟩)

/-- Integral restriction and normalized completion transport.
Source: main-20261015, open/closed localization, coefficient and Weil paragraphs.
(blueprint: lem-sf-open-closed-weil-mate-integral-stage).

Proof: The ordinary completed-coefficient pullbacks along Frobenius are equivalences.
Immersion pullback and open extension preserve the complete constructible
subcategory. Closed direct image is its whole-system derived limit and preserves
this subcategory. Restrict the ordinary adjunctions to obtain the integral mate
assertions. The immersion completed-pullback comparison identifies ordinary
pullback with the strict quotient tower, retaining its augmentation unit and
computation counit. Combine its coefficient transport with the unit-normalized
tower/reflector isomorphism and inverse gamma. The finite normalized projections
and finite-Hom Mittag-Leffler uniqueness make this independent of every supplied
Comparison record and every complete representative. The normalized open Roos
adjunction and closed derived adjunction give the fixed adjoint mates. Their
unit/counit formulas and mate pasting prove OpenClosedScalarMateLift. -/
theorem sf_openClosed_weil_integral_stage
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (_ιE : E →ₐ[Padic l] Ω)
    {X₀ U₀ Z₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (j₀ : U₀ ⟶ X₀) (i₀ : Z₀ ⟶ X₀)
    [IsOpenImmersion j₀.left] [IsClosedImmersion i₀.left]
    (_hij : Set.range i₀.left.base = (Set.range j₀.left.base)ᶜ) :
    sfIntegralOpenClosedWeilMateAssertions D l E j₀ i₀ ∧
    sfCompletionOpenClosedWeilMateAssertions D l hl E j₀ i₀ := by
  exact ⟨integral_from_normalization D l hl E j₀ i₀
    (fiber_complement D j₀ i₀ _hij),
    sf_openClosed_weil_completion_stage D l hl E Ω _ιE j₀ i₀ _hij⟩

end WeilConjectures
