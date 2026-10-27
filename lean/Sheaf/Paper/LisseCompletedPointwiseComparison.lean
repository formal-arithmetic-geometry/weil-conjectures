/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.LisseCompletedSystemData
import Sheaf.Paper.LisseNormalizedTowerSiteComparison
import Sheaf.Paper.LisseCompletedRationalHom
import all Sheaf.Paper.CompletedAdicCoefficientDatum
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreePullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
import Sheaf.SixFunctors.IntegralLisseReductionConstruction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # The comparison at one coefficient field and one scheme. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option profiler true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompletedLisse
variable (l : ℕ) [Fact l.Prime]

private def restrictionRoundTrip
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private def restrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp M := by ext U x; rfl

private def restrictionUnitIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.unit R ≅ (SheafOfModules.restrictScalars c.hom).obj
      (SheafOfModules.unit S) where
  hom := ⟨PresheafOfModules.homMk
    (Functor.whiskerRight c.hom.hom (forget₂ RingCat AddCommGrpCat))
    (fun U r x ↦ (c.hom.hom.app U).hom.map_mul r x)⟩
  inv := ⟨PresheafOfModules.homMk
    (Functor.whiskerRight c.inv.hom (forget₂ RingCat AddCommGrpCat)) (by
      intro U r x
      change S.obj.obj U at x
      change c.inv.hom.app U (c.hom.hom.app U r * x) = r * c.inv.hom.app U x
      rw [map_mul]
      have h := ConcreteCategory.congr_hom
        (congr_app (congrArg (fun f : R ⟶ R ↦ f.hom) c.hom_inv_id) U) r
      change c.inv.hom.app U (c.hom.hom.app U r) = r at h
      rw [h])⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f : R ⟶ R ↦ f.hom) c.hom_inv_id) U) x
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U) x

private theorem restriction_finiteLocallyFree
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u + 1}]
    [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S)
    (M : SheafOfModules.{u + 1} S) [hM : M.IsFiniteLocallyFree] :
    ((SheafOfModules.restrictScalars c.hom).obj M).IsFiniteLocallyFree := by
  obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
  let := hq
  let := hf
  let κ (i : q.I) := (q.generators i).I
  let (i : q.I) : Finite (κ i) := by
    have := hf.isFiniteType i
    infer_instance
  apply SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free q.X q.coversTop κ
  intro i
  let ci : R.over (q.X i) ≅ S.over (q.X i) :=
    (J.overPullback RingCat (q.X i)).mapIso c
  let E := restrictionEquivalence ci
  exact ⟨E.functor.mapIso (asIso (q.generators i).π).symm ≪≫
    (SheafOfModules.mapFreeIso E.functor (κ i) (restrictionUnitIso ci)).symm⟩

private def integralCoefficientEquivalence (P : Base.{u} l)
    (e : lisseIntegerSheafSized l P.E P.X ≅ completedRing l P) :
    Integral l P ≌ IntegralLisseModule l P.E P.X := by
  let c := (adicLisseForget P.X).mapIso e
  let E := restrictionEquivalence c
  refine {
    functor := ObjectProperty.lift _
      (ObjectProperty.ι _ ⋙ E.functor) (fun M ↦ ?_)
    inverse := ObjectProperty.lift _
      (ObjectProperty.ι _ ⋙ E.inverse) (fun M ↦ ?_)
    unitIso := NatIso.ofComponents
      (fun M ↦ ObjectProperty.isoMk _ (E.unitIso.app M.obj))
      (fun f ↦ ObjectProperty.hom_ext _ (E.unitIso.hom.naturality f.hom))
    counitIso := NatIso.ofComponents
      (fun M ↦ ObjectProperty.isoMk _ (E.counitIso.app M.obj))
      (fun f ↦ ObjectProperty.hom_ext _ (E.counitIso.hom.naturality f.hom))
    functor_unitIso_comp M := ObjectProperty.hom_ext _ (E.functor_unitIso_comp M.obj) }
  · have := M.property
    exact restriction_finiteLocallyFree c M.obj
  · have := M.property
    exact restriction_finiteLocallyFree c.symm M.obj


private def integralComparisonOfTower (P : Base.{u} l)
    (c : IntegralLisseReductionEquivalence l P.E P.X)
    (e : lisseIntegerSheafSized l P.E P.X ≅ completedRing l P)
    (he : ∀ n : ℕ, e.hom ≫ limit.π _ (op n) =
      integralLisseReduction l P.E P.X n ≫ (c.finiteConstant n).inv)
    (T : NormalizedTowerSiteComparison l P) : IntegralComparison l P := by
  let A := integralCoefficientEquivalence l P e
  let B := (A.trans c.equivalence).trans T.equivalence
  let V := SheafOfModules.toSheaf (integralLisseRing l P.E P.X)
  letI : PreservesLimitsOfShape ℕᵒᵖ V := by
    have : PreservesLimitsOfShape ℕᵒᵖ
        (V ⋙ sheafToPresheaf (ProEt.topology P.X) AddCommGrpCat.{u + 1}) :=
      inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
        (SheafOfModules.forget (integralLisseRing l P.E P.X) ⋙
          PresheafOfModules.toPresheaf (integralLisseRing l P.E P.X).obj))
    exact preservesLimitsOfShape_of_reflects_of_preserves V
      (sheafToPresheaf (ProEt.topology P.X) AddCommGrpCat.{u + 1})
  letI : PreservesFiniteColimits V :=
    (moduleSheaves_colimits_forgetful (integralLisseRing l P.E P.X)).2.2.1
  let q (M : Integral l P) :
      (Functor.const ℕᵒᵖ).obj ((integralForget l P).obj M.obj) ⟶
        proEtaleDiagram l P (B.functor.obj M) :=
    Functor.whiskerRight (c.reduction (A.functor.obj M)) V ≫
      T.diagramIso.inv.app (c.equivalence.functor.obj (A.functor.obj M))
  have qnat {M N : Integral l P} (f : M ⟶ N) (n : ℕ) :
      (integralForget l P).map f.hom ≫ (q N).app (op n) =
        (q M).app (op n) ≫ ((systemAbFunctor l P).map (B.functor.map f)).app (op n) := by
    dsimp only [q, NatTrans.comp_app, Functor.whiskerRight_app]
    change V.map (A.functor.map f).hom ≫
        (V.map ((c.reduction (A.functor.obj N)).app (op n)) ≫ _) = _
    rw [← Category.assoc, ← V.map_comp, c.reduction_natural,
      V.map_comp, Category.assoc]
    have ht := congr_app (T.diagramIso.inv.naturality
      (c.equivalence.functor.map (A.functor.map f))) (op n)
    change V.map ((c.equivalence.functor.map (A.functor.map f)).hom.app (op n)) ≫
        (T.diagramIso.inv.app (c.equivalence.functor.obj (A.functor.obj N))).app (op n) =
      (T.diagramIso.inv.app (c.equivalence.functor.obj (A.functor.obj M))).app (op n) ≫
        ((systemAbFunctor l P).map (B.functor.map f)).app (op n) at ht
    erw [ht, Category.assoc]
  have qlim (M : Integral l P) : IsLimit (Cone.mk _ (q M)) := by
    have hlim : IsLimit (Cone.mk (A.functor.obj M).obj
        (c.reduction (A.functor.obj M))) := by
      apply (c.completionLimit (c.equivalence.functor.obj (A.functor.obj M))).ofIsoLimit
      refine Cone.ext
        ((ObjectProperty.ι _).mapIso (c.equivalence.unitIso.app (A.functor.obj M))).symm ?_
      intro n
      dsimp
      apply (cancel_epi (c.equivalence.unitIso.hom.app (A.functor.obj M)).hom).1
      have hh := congrArg (fun f ↦ f.hom)
        (c.equivalence.unitIso.hom_inv_id_app (A.functor.obj M))
      change (c.equivalence.unitIso.hom.app (A.functor.obj M)).hom ≫
        (c.equivalence.unitIso.inv.app (A.functor.obj M)).hom = 𝟙 _ at hh
      rw [← Category.assoc, hh, Category.id_comp]
      exact c.unit_projection (A.functor.obj M) n.unop
    exact (IsLimit.postcomposeHomEquiv
      (T.diagramIso.app (c.equivalence.functor.obj (A.functor.obj M))))
        (Cone.mk _ (q M)) <| by
          apply (isLimitOfPreserves V hlim).ofIsoLimit
          refine Cone.ext (Iso.refl _) ?_
          intro n
          change V.map ((c.reduction (A.functor.obj M)).app n) =
            (V.map ((c.reduction (A.functor.obj M)).app n) ≫ _) ≫ _
          rw [Category.assoc]
          have hi := congr_app
            (T.diagramIso.inv_hom_id_app
              (c.equivalence.functor.obj (A.functor.obj M))) n
          change _ ≫ _ = 𝟙 _ at hi
          erw [hi, Category.comp_id]
  let k (F : Systems l P) :=
    q (B.inverse.obj F) ≫ (systemAbFunctor l P).map (B.counitIso.hom.app F)
  refine {
    integralComparison := c
    coefficientIso := e
    coefficient_projection := he
    equivalence := B
    reduction := q
    reduction_quotient := ?_
    reduction_scalar := ?_
    reduction_natural := qnat
    completion := k
    completion_limit := ?_
    completion_natural := ?_
    unit_projection := ?_
    counit_projection := fun _ _ ↦ rfl }
  · intro M n
    obtain ⟨hz, hc⟩ := c.reductionQuotient (A.functor.obj M) n
    change integralLisseScalar l P.E P.X (A.functor.obj M).obj _ ≫ _ = 0 at hz
    have hq : integralScalar l P e M
        (Padic.coefficientExtensionUniformizer l P.E ^ (n + 1)) ≫
          (q M).app (op n) = 0 := by
      change V.map _ ≫ (V.map _ ≫ _) = 0
      erw [← Category.assoc, ← V.map_comp, hz, V.map_zero, zero_comp]
    refine ⟨hq, ⟨?_⟩⟩
    let hc' := isColimitCoforkMapOfIsColimit' V hz hc.some
    apply hc'.ofIsoColimit
    refine Cofork.ext
      ((T.diagramIso.app (c.equivalence.functor.obj (A.functor.obj M))).app (op n)).symm ?_
    simp only [q, NatTrans.comp_app, Functor.whiskerRight_app]
    rfl
  · intro M n a
    change V.map (integralLisseScalar l P.E P.X (A.functor.obj M).obj a) ≫
        (V.map ((c.reduction (A.functor.obj M)).app (op n)) ≫ _) = _
    rw [← Category.assoc, ← V.map_comp, integralLisseScalar_natural,
      V.map_comp, Category.assoc, T.scalar]
    rfl
  · intro F
    exact (IsLimit.postcomposeHomEquiv
      ((systemAbFunctor l P).mapIso (B.counitIso.app F))
      (Cone.mk _ (q (B.inverse.obj F)))).symm (qlim (B.inverse.obj F))
  · intro F G f n
    change (integralForget l P).map (B.inverse.map f).hom ≫
        ((q (B.inverse.obj G)).app (op n) ≫ _) = _
    dsimp only [k, NatTrans.comp_app]
    erw [← Category.assoc, qnat, Category.assoc]
    rw [Category.assoc]
    congr 1
    have ht := congrArg ((systemAbFunctor l P).map)
      (B.counitIso.hom.naturality f)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at ht
    exact congr_app ht (op n)
  · intro M n
    change (integralForget l P).map (B.unitIso.hom.app M).hom ≫
        ((q (B.inverse.obj (B.functor.obj M))).app (op n) ≫ _) = _
    erw [← Category.assoc, qnat, Category.assoc]
    have ht := congrArg ((systemAbFunctor l P).map) (B.functor_unitIso_comp M)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at ht
    have hn := congr_app ht (op n)
    change _ ≫ _ = 𝟙 _ at hn
    rw [hn]
    change (q M).app (op n) ≫ 𝟙 _ = (q M).app (op n)
    exact Category.comp_id _

@[reassoc]
private theorem rationalScalar_natural (P : Base.{u} l)
    {M N : ringedSiteModules.{u + 1} ((adicLisseForget P.X).obj (rationalRing l P))}
    (f : M ⟶ N) (a : P.E) :
    rationalScalar l P M a ≫ f = f ≫ rationalScalar l P N a := by
  ext U x
  exact (f.val.app U).hom.map_smul _ x

private theorem rationalScalar_mul (P : Base.{u} l)
    (M : ringedSiteModules.{u + 1} ((adicLisseForget P.X).obj (rationalRing l P)))
    (a b : P.E) :
    rationalScalar l P M a ≫ rationalScalar l P M b = rationalScalar l P M (a * b) := by
  let := spectralNorm.normedField ℚ_[l] P.E
  ext U x
  change lisseFieldConstantSized l P.E P.X U b •
      (lisseFieldConstantSized l P.E P.X U a • x) =
    lisseFieldConstantSized l P.E P.X U (a * b) • x
  rw [smul_smul]
  congr 1
  change ULift.up (ContinuousMap.const _ b * ContinuousMap.const _ a) =
    ULift.up (ContinuousMap.const _ (a * b))
  congr 1
  ext
  exact mul_comm b a

private theorem scalarExtension_finiteLocallyFree (P : Base.{u} l)
    (I : IntegralComparison l P) (F : RawRational l P) :
    (rationalizedLattice l P I F).IsFiniteLocallyFree := by
  let φ := I.coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X
  let a : (adicLisseForget P.X).obj (completedRing l P) ⟶
      ((𝟭 P.X.ProEt).sheafPushforwardContinuous RingCat (ProEt.topology P.X)
        (ProEt.topology P.X)).obj ((adicLisseForget P.X).obj (rationalRing l P)) :=
    (adicLisseForget P.X).map φ
  let := SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
    (U := 𝟭 P.X.ProEt) (J := ProEt.topology P.X) (K := ProEt.topology P.X) a
  obtain ⟨adj, _⟩ := completedAdjunction P.X φ
  let rightIso : SheafOfModules.pushforward (F := 𝟭 P.X.ProEt) a ≅
      SheafOfModules.restrictScalars a := Iso.refl _
  let adj' := adj.ofNatIsoRight rightIso.symm
  let ei := Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction (F := 𝟭 P.X.ProEt) a) adj'
  let M := (I.equivalence.inverse.obj ⟨F.obj.integral, F.property⟩).obj
  have : M.IsFiniteLocallyFree :=
    (I.equivalence.inverse.obj ⟨F.obj.integral, F.property⟩).property
  have := SheafOfModules.finiteLocallyFree_pullback.{u + 1, u, u + 1} (F := 𝟭 P.X.ProEt) a
    (idCoverPreserving (ProEt.topology P.X)) M
  exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} (ei.app M)

private def comparisonOfIntegral (P : Base.{u} l) (I : IntegralComparison l P) :
    Comparison l P := by
  letI : Preadditive (LisseRationalSheaf l P.E P.X) := {
    homGroup := lisseRationalHomAddCommGroup l P.E P.X
    add_comp := fun F G H f f' g ↦ congrArg
      (fun t : lisseRationalHom l P.E P.X G H →ₗ[P.E]
        lisseRationalHom l P.E P.X F H ↦ t g)
      (((lisseRationalComposition l P.E P.X).comp F G H).map_add f f')
    comp_add := fun F G H f g g' ↦
      ((lisseRationalComposition l P.E P.X).comp F G H f).map_add g g' }
  let h := completed_lisse_rational_hom l P I
  let m (F G : RawRational l P) := (h F G).choose
  have hm (F G : RawRational l P) := (h F G).choose_spec.1
  let S := completedAdicChange P.X
    (I.coefficientIso.inv ≫ lisseIntegerToFieldSized l P.E P.X)
  let R : RawRational l P ⥤ Rational l P := {
    obj F := ⟨rationalizedLattice l P I F, scalarExtension_finiteLocallyFree l P I F⟩
    map {F G} f := ⟨m F G f.hom⟩
    map_id F := by
      apply ObjectProperty.hom_ext
      change m F F (TensorProduct.tmul (Integers l P) 1 (𝟙 F.obj.integral)) = 𝟙 _
      rw [(hm F F).2]
      have hi := I.equivalence.inverse.map_id ⟨F.obj.integral, F.property⟩
      change S.map (I.equivalence.inverse.map (𝟙 _)).hom ≫ _ = _
      rw [hi]
      change S.map (𝟙 _) ≫ _ = _
      rw [S.map_id, Category.id_comp]
      ext U x
      exact one_smul _ x
    map_comp {F G H} f g := by
      apply ObjectProperty.hom_ext
      change m F H (f.hom ≫ g.hom) = m F G f.hom ≫ m G H g.hom
      induction f.hom using TensorProduct.induction_on with
      | zero => simp only [zero_comp, map_zero]
      | add f f' hf hf' =>
        erw [Preadditive.add_comp, map_add, hf, hf']
        rw [(m F G).map_add, Preadditive.add_comp]
      | tmul a f =>
        induction g.hom using TensorProduct.induction_on with
        | zero => simp only [comp_zero, map_zero]
        | add g g' hg hg' =>
          erw [Preadditive.comp_add, map_add, hg, hg']
          rw [(m G H).map_add, Preadditive.comp_add]
        | tmul b g =>
          rw [lisseCoherence_rational_tmul_comp, (hm F H).2,
            (hm F G).2, (hm G H).2]
          let f' : (⟨F.obj.integral, F.property⟩ : Systems l P) ⟶
              ⟨G.obj.integral, G.property⟩ := ⟨f⟩
          let g' : (⟨G.obj.integral, G.property⟩ : Systems l P) ⟶
              ⟨H.obj.integral, H.property⟩ := ⟨g⟩
          change S.map (I.equivalence.inverse.map (f' ≫ g')).hom ≫ _ = _
          rw [I.equivalence.inverse.map_comp]
          change S.map (_ ≫ _) ≫ _ = _
          rw [S.map_comp]
          symm
          rw [Category.assoc, rationalScalar_natural_assoc]
          simp only [← Category.assoc]
          rw [Category.assoc (S.map (I.equivalence.inverse.map f').hom ≫
            S.map (I.equivalence.inverse.map g').hom), rationalScalar_mul]
  }
  exact {
    toIntegralComparison := I
    rationalRealization := R
    rationalObject := fun _ ↦ Iso.refl _
    rational_map := fun F G a f ↦ by
      change m F G (TensorProduct.tmul (Integers l P) a f) ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      exact (hm F G).2 a f
    rational_add := fun F G f g ↦ ObjectProperty.hom_ext _ ((m F G).map_add _ _)
    rationalFullyFaithful := {
      preimage {F G} f := ⟨((hm F G).1.surjective f.hom).choose⟩
      map_preimage {F G} f := ObjectProperty.hom_ext _
        (((hm F G).1.surjective f.hom).choose_spec)
      preimage_map {F G} f := by
        apply ObjectProperty.hom_ext
        exact (hm F G).1.injective
          (((hm F G).1.surjective (m F G f.hom)).choose_spec) } }


/-- At a fixed base, the completed integral comparison and rational realization exist
with the prescribed continuous-coefficient datum and residue-normalized coefficient isomorphism.
Source: Bhatt--Scholze, Corollary 5.1.5, Lemma 6.8.2 and Proposition 6.8.4(1),(4),
pp.35,58--59 (blueprint: lem-per-lisse-completed-pointwise-comparison).

Proof: For each positive exponent, apply finite-local-systems-twist to the finite quotient
ring. Restrict the equivalence to finite free models by taking a geometric stalk on every
nonempty common trivializing object; the stalk of the constant module is that module.
Inverse image preserves tensor quotients, so the equivalences descend the normalized
transition maps and their equations, uniquely by full faithfulness. This identifies the
etale tower category in Systems with IntegralReductionTower. Transport the given integral
reduction equivalence across the prescribed coefficient isomorphism and compose with this
tower equivalence. Transport its quotient and limit cones as well. The residue equations
for the coefficient isomorphism identify the transported scalar maps with integralScalar;
full faithfulness and the original projection equations give naturality, unit and counit.
These constructions allow rank zero and locally varying rank.
For rational realization, apply the actual scalar-extension functor to the reconstructed
integral modules. The DVR identity l = u * varpi^e, with u a unit and e positive, identifies
localization at l with localization at varpi and with the coefficient field E. Extend the
map on integral Hom A-linearly to E tensor_A Hom; the balancing
relation is the scalar-compatibility equation just obtained. Functoriality and additivity
follow on pure tensors. On a common finite-free chart internal Hom is a finite matrix
module, and its localization is the rational internal Hom. Globally, X is qcqs; degree-zero
bounded-continuity-sections applied to the multiplication-by-uniformizer diagram of these
internal Homs identifies localized sections with rational Hom. Thus the displayed tensor
map is bijective, giving full faithfulness. The zero and empty charts satisfy the same
calculation. All constructions retain the supplied coefficient datum and isomorphism. -/
theorem completed_pointwise_comparison (P : Base.{u} l)
    (c : IntegralLisseReductionEquivalence l P.E P.X)
    (e : lisseIntegerSheafSized l P.E P.X ≅ completedRing l P)
    (he : ∀ n : ℕ, e.hom ≫ limit.π _ (op n) = integralLisseReduction l P.E P.X n ≫
      (c.finiteConstant n).inv) :
    ∃ d : Comparison l P, d.integralComparison = c ∧ d.coefficientIso = e := by
  obtain ⟨T⟩ := normalized_tower_site_comparison l P
  let I := integralComparisonOfTower l P c e he T
  exact ⟨comparisonOfIntegral l P I, rfl, rfl⟩

end AlgebraicGeometry.ProEtale.CompletedLisse
