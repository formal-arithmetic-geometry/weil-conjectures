/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.IntegralPullbackResolutionMatching
import Sheaf.Paper.IntegralPullbackReductionCounit
import Sheaf.CategoryTheory.ExactDerivedTransformationPasting

/-!
# Composition of the integral inverse-image comparison

Source: blueprint `sec-trace-formula/sk-thm-trace-transport/`
`thm-trf-l-function-euler-product.proof.md`, Step 1, Global powers; Stacks Project,
Tags 03D6, 0D6D and 0941
(blueprint: lem-trf-integral-inverse-image-comparison-composition).

The auxiliary compositor is fixed on sections, then applied termwise and localized.
The pullback compositor is exactly the recorded normalized realization, and kappa
is the recorded cone comparison evaluated on a derived object.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u a b c
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance postcomposeCompContinuous
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    (proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose k).IsContinuous
      (ProEt.topology Z) (ProEt.topology V) :=
  Functor.isContinuous_comp (proEtaleIsoPostcompose h) (proEtaleIsoPostcompose k)
    _ (ProEt.topology W) _

private instance mapCompContinuous
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale h) ⋙
      MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale k)).IsContinuous
      (ProEt.topology Z) (ProEt.topology V) :=
  postcomposeCompContinuous h k

private theorem constantComposition
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (A : CommRingCat.{u + 1}) :
    (isoSectionwiseInverseImage h RingCat.{u + 1}).map
        (isoSectionwiseConstantMap.{u, u} k A) ≫ isoSectionwiseConstantMap.{u, u} h A =
      (Functor.sheafPushforwardContinuousNatTrans
        (MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom
        RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology V)).app
          ((sheafCompose (ProEt.topology V) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj A)) ≫
        isoSectionwiseConstantMap.{u, u} (h ≫ k) A := by
  let d := MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)
  let R := (sheafCompose (ProEt.topology V) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj A)
  let a := (Functor.sheafPushforwardContinuousNatTrans d.inv RingCat.{u + 1}
    (ProEt.topology Z) (ProEt.topology V)).app R ≫
    (isoSectionwiseInverseImage h RingCat.{u + 1}).map
      (isoSectionwiseConstantMap.{u, u} k A) ≫ isoSectionwiseConstantMap.{u, u} h A
  have ha : a = isoSectionwiseConstantMap.{u, u} (h ≫ k) A := by
    apply (isoSectionwiseConstantMap_existsUnique.{u, u} (h ≫ k) A).unique
    · intro U x
      change (isoSectionwiseConstantMap.{u, u} h A).hom.app (op U)
        ((isoSectionwiseConstantMap.{u, u} k A).hom.app (op ((proEtaleIsoPostcompose h).obj U))
          (R.obj.map (d.inv.app U).op
            ((toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj A)).app
              (op ((proEtaleIsoPostcompose (h ≫ k)).obj U)) x))) = _
      have hn := congrArg (fun f ↦ f x)
        ((toSheafify (ProEt.topology V)
          ((Functor.const V.ProEtᵒᵖ).obj A)).naturality (d.inv.app U).op)
      dsimp at hn
      erw [← hn]
      exact (congrArg ((isoSectionwiseConstantMap.{u, u} h A).hom.app (op U))
          ((isoSectionwiseConstantMap_existsUnique.{u, u} k A).exists.choose_spec
            ((proEtaleIsoPostcompose h).obj U) x)).trans
        ((isoSectionwiseConstantMap_existsUnique.{u, u} h A).exists.choose_spec U x)
    · exact (isoSectionwiseConstantMap_existsUnique.{u, u} (h ≫ k) A).exists.choose_spec
  rw [← ha]
  ext U x
  change _ = (isoSectionwiseConstantMap.{u, u} h A).hom.app U
    ((isoSectionwiseConstantMap.{u, u} k A).hom.app _
      (R.obj.map (d.inv.app U.unop).op (R.obj.map (d.hom.app U.unop).op x)))
  rw [← RingCat.comp_apply, ← R.obj.map_comp, ← op_comp, d.inv_hom_id_app]
  rw [op_id, R.obj.map_id]
  rfl

private theorem completedComposition
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    (isoSectionwiseInverseImage h RingCat.{u + 1}).map
        (inverseImageCompletedCoefficientMap l E k) ≫
      inverseImageCompletedCoefficientMap l E h =
      (Functor.sheafPushforwardContinuousNatTrans
        (MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom
        RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology V)).app
          (completedIntegralCoefficientSheafUnrestricted l E V) ≫
        inverseImageCompletedCoefficientMap l E (h ≫ k) := by
  let F := isoSectionwiseInverseImage h RingCat.{u + 1}
  let T := Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom
    RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology V)
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, inverseImageCompletedCoefficientMap, limit.lift_π]
  change F.map (inverseImageCompletedCoefficientMap l E k) ≫
    (F.map (limit.π (integralCoefficientSheafSystem l E W) n) ≫
      inverseImageFiniteCoefficientMap l E h n.unop) = _
  rw [← Category.assoc, ← F.map_comp]
  simp only [inverseImageCompletedCoefficientMap, limit.lift_π]
  dsimp only [inverseImageCompletedCoefficientComponent]
  rw [F.map_comp, Category.assoc, constantComposition]
  have hn := T.naturality (limit.π (integralCoefficientSheafSystem l E V) n)
  change F.map ((isoSectionwiseInverseImage k RingCat.{u + 1}).map
      (limit.π (integralCoefficientSheafSystem l E V) n)) ≫ _ = _ at hn
  rw [← Category.assoc]
  simpa only [Category.assoc, completedIntegralCoefficientSheafUnrestricted,
    integralCoefficientSheafSystem, Functor.ofOpSequence, Functor.ofSequence,
    Functor.leftOp, integralCoefficientSheaf, isoSectionwiseInverseImage,
    proEtaleIsoPostcompose, T] using
    congrArg (fun f ↦ f ≫ inverseImageFiniteCoefficientMap l E (h ≫ k) n.unop) hn

/-- The canonical inverse-image compositor is linear for the transported completed
coefficient actions and is uniquely determined by the canonical restriction on sections.
Source: Stacks 03D6; blueprint Global powers
(blueprint: lem-trf-integral-inverse-image-comparison-composition).
Proof: the site compositor is identity on the underlying schemes. Constant-section
maps respect it at every finite quotient. The limit projection equations then give
compatibility for the completed coefficient maps. Transporting actions through their
inverses makes the displayed section map linear. Its inverse comes from the inverse
site compositor. Restriction and module maps commute with both maps, giving a natural
isomorphism. Evaluation on every section determines its hom, hence the isomorphism,
uniquely. This is the linearity assertion for d in the node's statement. -/
theorem integralInverseImageComposition_existsUnique
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    ∃! d : inverseImageIntegralModules l E k ⋙ inverseImageIntegralModules l E h ≅
        inverseImageIntegralModules l E (h ≫ k),
      ∀ (M : integralTowerModules l E V) (U : Z.ProEt)
        (x : M.val.obj (op ((proEtaleIsoPostcompose k).obj
          ((proEtaleIsoPostcompose h).obj U)))),
        (d.hom.app M).val.app (op U) x =
          M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
            (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U).op x := by
  let F := isoSectionwiseInverseImage h RingCat.{u + 1}
  let d := MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)
  let a := SheafOfModules.pushforwardComp
    (inv (inverseImageCompletedCoefficientMap l E h))
    (inv (inverseImageCompletedCoefficientMap l E k)) ≪≫
      SheafOfModules.pushforwardCongr₂
        (ψ := inv (inverseImageCompletedCoefficientMap l E (h ≫ k)))
        (G := proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose k)
        (F := proEtaleIsoPostcompose (h ≫ k))
        (S := completedIntegralCoefficientSheafUnrestricted l E V)
        (inv (inverseImageCompletedCoefficientMap l E h) ≫
          F.map (inv (inverseImageCompletedCoefficientMap l E k))) d (by
        apply (cancel_mono (inverseImageCompletedCoefficientMap l E (h ≫ k))).1
        rw [Category.assoc, ← completedComposition l E h k]
        change (inv (inverseImageCompletedCoefficientMap l E h) ≫
          F.map (inv (inverseImageCompletedCoefficientMap l E k))) ≫
          F.map (inverseImageCompletedCoefficientMap l E k) ≫
          inverseImageCompletedCoefficientMap l E h = _
        rw [Category.assoc, ← Category.assoc (F.map _) (F.map _), ← F.map_comp,
          IsIso.inv_hom_id, F.map_id, Category.id_comp, IsIso.inv_hom_id, IsIso.inv_hom_id])
  have ha : ∀ (M : integralTowerModules l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose k).obj
        ((proEtaleIsoPostcompose h).obj U)))),
      (a.hom.app M).val.app (op U) x = M.val.map (d.hom.app U).op x := by
    intro M U x
    rfl
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (hb M U.unop x).trans (ha M U.unop x).symm

/-- The section-normalized linear compositor on completed-coefficient module sheaves.
Source: Stacks 03D6; blueprint Global powers
(blueprint: lem-trf-integral-inverse-image-comparison-composition). -/
def integralInverseImageComposition
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :=
  (integralInverseImageComposition_existsUnique l E h k).exists.choose

/-- The same canonical compositor, applied termwise and localized at quasi-isomorphisms.
Source: Stacks 03D6 and 05RU; blueprint Global powers
(blueprint: lem-trf-integral-inverse-image-comparison-composition). -/
def integralInverseImageDerivedComposition
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    inverseImageIntegralDerived l E k ⋙ inverseImageIntegralDerived l E h ≅
      inverseImageIntegralDerived l E (h ≫ k) :=
  (Functor.mapDerivedCategoryCompIso (inverseImageIntegralModules l E k)
    (inverseImageIntegralModules l E h)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (integralInverseImageComposition l E h k)

private theorem counitIdentity_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (H F : A ⥤ B) (L : B ⥤ C) (T : A ⥤ C)
    (γ : F ⋙ L ⟶ T) (β : H ⋙ L ⟶ T)
    {X Y : A} (r : X ≅ Y) (aX : H.obj X ⟶ F.obj X) (aY : H.obj Y ⟶ F.obj Y)
    (ha : H.map r.hom ≫ aY = aX ≫ F.map r.hom)
    (hX : L.map aX ≫ γ.app X = β.app X) :
    L.map aY ≫ γ.app Y = β.app Y := by
  apply (cancel_epi (L.map (H.map r.hom))).1
  calc
    _ = L.map (H.map r.hom ≫ aY) ≫ γ.app Y := by
      rw [Functor.map_comp, Category.assoc]
    _ = L.map (aX ≫ F.map r.hom) ≫ γ.app Y := by rw [ha]
    _ = L.map aX ≫ γ.app X ≫ T.map r.hom := by
      rw [Functor.map_comp, Category.assoc, ← γ.naturality]
      rfl
    _ = (H ⋙ L).map r.hom ≫ β.app Y := by
      rw [← Category.assoc, hX, β.naturality]
    _ = _ := rfl

private theorem chosenResolution_formula
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (M : DerivedCategory (integralTowerModules l E W)) :
    ∃ (K : CochainComplex (integralTowerModules l E W) ℤ)
      (eK : DerivedCategory.Q.obj K ≅ M)
      (P : (integralOperationsGoodComplex l E W).FullSubcategory)
      (q : P.obj ⟶ K) (hq : QuasiIso q),
      let := hq
      inverseImagePullbackComparisonDerived l E h hZ hW M =
        (inverseImageIntegralDerived l E h).map eK.inv ≫
        (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
        inv (DerivedCategory.Q.map
          (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q)) ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
        (integralDerivedPullbackComparison l E h).inv.app P ≫
        (integralDerivedPullback l E h).map (DerivedCategory.Q.map q) ≫
        (integralDerivedPullback l E h).map eK.hom := by
  unfold inverseImagePullbackComparisonDerived
  extract_lets K e hp P q hq
  let P' : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory :=
    ⟨P, hq.1, fun i ↦ (exactFunctor _ _).prop_of_iso
      (@SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
        (ProEt.topology W) (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
        (P.X i)).symm (hq.2.1 i)⟩
  refine ⟨K, e, P', q, hq.2.2.1, ?_⟩
  simp only [inverseImagePullbackComparison, Category.assoc]
  rfl

private theorem heq_apply {A A' : Type a} {B B' : Type b} {f : A → B} {g : A' → B'}
    (hB : B = B') (hf : HEq f g) {x : A} {x' : A'} (hx : HEq x x') :
    HEq (f x) (g x') := by
  cases hB
  exact heq_of_eq (congr_heq hf hx)

private theorem restrictedSection_map
    (X : Scheme.{u}) {M N : coefficientSequenceModules l E X} (f : M ⟶ N)
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l E X).map f).app (op n)).val.app U
        (integralComparisonRestrictedSection l E X M n U x) =
      integralComparisonRestrictedSection l E X N n U
        (f.val.app (op (n, U.unop)) x) := by
  have h := (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.2 f n U
  apply eq_of_heq
  exact (heq_apply (integralComparisonRestrictedSectionType l E X N n U) h
    (cast_heq _ x)).trans (cast_heq _ _).symm

private theorem cast_map
    {A : Type*} [Category A] {P Q : A ⥤ AddCommGrpCat.{u + 1}} (e : P = Q)
    {U V : A} (f : U ⟶ V) (x : Q.obj U) :
    P.map f (cast (congrArg (fun (P : A ⥤ AddCommGrpCat.{u + 1}) ↦ ↥(P.obj U)) e).symm x) =
      cast (congrArg (fun (P : A ⥤ AddCommGrpCat.{u + 1}) ↦ ↥(P.obj V)) e).symm (Q.map f x) := by
  subst e
  rfl

private theorem restrictedSection_naturality
    (X : Scheme.{u}) (M : coefficientSequenceModules l E X) (n : ℕ)
    {U V : X.ProEtᵒᵖ} (f : U ⟶ V) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.map f
        (integralComparisonRestrictedSection l E X M n U x) =
      integralComparisonRestrictedSection l E X M n V
        (M.val.map (Prod.mkHom (𝟙 n) f.unop).op x) := by
  have e : (((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.presheaf =
      (Prod.sectR n X.ProEt).op ⋙ M.val.presheaf := by
    change (((coefficientSequenceRestriction_exists l E X).exists.choose.obj M).obj
      (op n)).val.presheaf = _
    rw [(coefficientSequenceRestriction_exists l E X).exists.choose_spec.1 M n]
    rfl
  exact cast_map e f x

private def towerCompositor {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (d : inverseImageIntegralModules l E k ⋙ inverseImageIntegralModules l E h ≅
      inverseImageIntegralModules l E (h ≫ k))
    (T : ℕᵒᵖ ⥤ integralTowerModules l E V) :
    (integralTowerInverseImage l E h).obj ((integralTowerInverseImage l E k).obj T) ≅
      (integralTowerInverseImage l E (h ≫ k)).obj T :=
  NatIso.ofComponents (fun n ↦ d.app (T.obj n)) (fun f ↦ d.hom.naturality (T.map f))

private def towerCompositorNat {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    integralTowerInverseImage l E k ⋙ integralTowerInverseImage l E h ≅
      integralTowerInverseImage l E (h ≫ k) :=
  NatIso.ofComponents
    (towerCompositor l E h k (integralInverseImageComposition l E h k))
    (by
      intro A B f
      apply NatTrans.ext
      funext n
      exact (integralInverseImageComposition l E h k).hom.naturality (f.app n))

private def towerDerivedCompositor {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    integralDerivedTowerInverseImage l E k ⋙ integralDerivedTowerInverseImage l E h ≅
      integralDerivedTowerInverseImage l E (h ≫ k) :=
  (Functor.mapDerivedCategoryCompIso
    (integralTowerInverseImage l E k) (integralTowerInverseImage l E h)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (towerCompositorNat l E h k)

private theorem sequenceGenerator_composition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (M : coefficientSequenceModules l E V) (n : ℕ) (U : V.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequenceComposition l E h k).hom.app M).val.app
        (op (n, (proEtaleBaseChange (h ≫ k)).obj U))
        (integralComparisonSequenceGenerator l E (h ≫ k) M n U x) =
      ((integralComparisonSequencePullback l E h).obj
          ((integralComparisonSequencePullback l E k).obj M)).val.map
        (Prod.mkHom (𝟙 n) ((MorphismProperty.Over.pullbackComp h k).hom.app U)).op
        (integralComparisonSequenceGenerator l E h
          ((integralComparisonSequencePullback l E k).obj M) n
          ((proEtaleBaseChange k).obj U)
          (integralComparisonSequenceGenerator l E k M n U x)) := by
  let Ak := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)
  let Ah := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)
  let Aj := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k))
  obtain ⟨c, hc, hs⟩ :=
    (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose_spec
  have ht := unit_conjugateEquiv (Ak.comp Ah) Aj
    (integralComparisonSequenceComposition l E h k).hom M
  have hh : conjugateEquiv (Ak.comp Ah) Aj
      (integralComparisonSequenceComposition l E h k).hom = c.hom :=
    congrArg Iso.hom hc
  rw [hh] at ht
  have hh := congrArg (fun f ↦ f.val.app (op (n, U)) x) ht
  change (c.hom.app _).val.app (op (n, U))
      (integralComparisonSequenceGenerator l E h
        ((integralComparisonSequencePullback l E k).obj M) n
        ((proEtaleBaseChange k).obj U)
        (integralComparisonSequenceGenerator l E k M n U x)) =
    ((integralComparisonSequenceComposition l E h k).hom.app M).val.app
      (op (n, (proEtaleBaseChange (h ≫ k)).obj U))
      (integralComparisonSequenceGenerator l E (h ≫ k) M n U x) at hh
  rw [hs] at hh
  exact hh.symm

private theorem sequenceGenerator_naturality
    {Y X : Scheme.{u}} (g : X ⟶ Y)
    (M : coefficientSequenceModules l E Y) (n : ℕ)
    {U V : Y.ProEt} (f : U ⟶ V) (x : M.val.obj (op (n, V))) :
    integralComparisonSequenceGenerator l E g M n U
        (M.val.map (Prod.mkHom (𝟙 n) f).op x) =
      ((integralComparisonSequencePullback l E g).obj M).val.map
        (Prod.mkHom (𝟙 n) ((proEtaleBaseChange g).map f)).op
        (integralComparisonSequenceGenerator l E g M n V x) := by
  exact congrArg (fun z ↦ z x)
    (((Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E g)).unit.app M).val.naturality
      (Prod.mkHom (𝟙 n) f).op)

private theorem comma_composition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (U : Z.ProEt) :
    proEtaleIsoCommaArrow (h ≫ k) U ≫
        (proEtaleBaseChange (h ≫ k)).map
          ((MorphismProperty.Over.mapComp (Q := ⊤)
            (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U) ≫
        (MorphismProperty.Over.pullbackComp h k).hom.app
          ((proEtaleIsoPostcompose k).obj ((proEtaleIsoPostcompose h).obj U)) =
      proEtaleIsoCommaArrow h U ≫
        (proEtaleBaseChange h).map
          (proEtaleIsoCommaArrow k ((proEtaleIsoPostcompose h).obj U)) := by
  let A := (proEtaleIsoPostcompose k).obj ((proEtaleIsoPostcompose h).obj U)
  have hc : ((MorphismProperty.Over.pullbackComp h k).hom.app A).left ≫
      pullback.fst (pullback.snd A.hom k) h ≫ pullback.fst A.hom k =
      pullback.fst A.hom (h ≫ k) := by
    change (pullback.congrHom _ _ ≪≫ (pullbackLeftPullbackSndIso A.hom k h).symm).hom ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = _
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst]
    simp
  apply MorphismProperty.Over.Hom.ext
  change (proEtaleIsoCommaArrow (h ≫ k) U).left ≫
      ((proEtaleBaseChange (h ≫ k)).map _).left ≫
      ((MorphismProperty.Over.pullbackComp h k).hom.app A).left =
    (proEtaleIsoCommaArrow h U).left ≫
      ((proEtaleBaseChange h).map _).left
  apply (cancel_mono (pullback.fst (pullback.snd A.hom k) h)).1
  apply (cancel_mono (pullback.fst A.hom k)).1
  simp only [Category.assoc]
  erw [hc]
  have hm : ((proEtaleBaseChange (h ≫ k)).map
      ((MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U)).left ≫
        pullback.fst A.hom (h ≫ k) =
      pullback.fst ((proEtaleIsoPostcompose (h ≫ k)).obj U).hom (h ≫ k) := by
    dsimp only [proEtaleBaseChange]
    rw [MorphismProperty.Over.pullback_map_left]
    erw [pullback.lift_fst]
    simp only [MorphismProperty.Over.mapComp_hom_app_left]
    exact Category.comp_id _
  rw [hm]
  have hf {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (T : X.ProEt) :
      (proEtaleIsoCommaArrow f T).left ≫
        pullback.fst ((proEtaleIsoPostcompose f).obj T).hom f = 𝟙 T.left := by
    dsimp only [proEtaleIsoCommaArrow, MorphismProperty.Over.mapPullbackAdj]
    change pullback.lift (𝟙 T.left) T.hom _ ≫ pullback.fst (T.hom ≫ f) f = _
    exact pullback.lift_fst _ _ _
  rw [hf]
  dsimp only [proEtaleBaseChange]
  rw [MorphismProperty.Over.pullback_map_left]
  erw [pullback.lift_fst_assoc]
  rw [Category.assoc, hf, Category.comp_id, hf]


private theorem towerUnit_composition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (d : inverseImageIntegralModules l E k ⋙ inverseImageIntegralModules l E h ≅
      inverseImageIntegralModules l E (h ≫ k))
    (hd : ∀ (M : integralTowerModules l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose k).obj
        ((proEtaleIsoPostcompose h).obj U)))),
      (d.hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U).op x)
    (M : coefficientSequenceModules l E V) :
    (towerCompositor l E h k d ((coefficientSequenceRestriction l E V).obj M)).hom ≫
        (integralTowerInverseImageUnit l E (h ≫ k)).hom.app M ≫
        (coefficientSequenceRestriction l E Z).map
          ((integralComparisonSequenceComposition l E h k).hom.app M) =
      (integralTowerInverseImage l E h).map
          ((integralTowerInverseImageUnit l E k).hom.app M) ≫
        (integralTowerInverseImageUnit l E h).hom.app
          ((integralComparisonSequencePullback l E k).obj M) := by
  have hm := (integralTowerInverseImageUnit_existsUnique l E (h ≫ k)).exists.choose_spec
  have hk := (integralTowerInverseImageUnit_existsUnique l E k).exists.choose_spec
  have hh := (integralTowerInverseImageUnit_existsUnique l E h).exists.choose_spec
  ext n U x
  change _ =
    (((integralTowerInverseImageUnit l E h).hom.app
      ((integralComparisonSequencePullback l E k).obj M)).app n).val.app U
      ((((integralTowerInverseImageUnit l E k).hom.app M).app n).val.app
        (op ((proEtaleIsoPostcompose h).obj U.unop)) x)
  obtain ⟨x, rfl⟩ := (Equiv.cast
    (integralComparisonRestrictedSectionType l E V M n.unop
      (op ((proEtaleIsoPostcompose k).obj
        ((proEtaleIsoPostcompose h).obj U.unop)))).symm).surjective x
  change (((coefficientSequenceRestriction l E Z).map
      ((integralComparisonSequenceComposition l E h k).hom.app M)).app n).val.app U
    ((((integralTowerInverseImageUnit l E (h ≫ k)).hom.app M).app n).val.app U
      ((d.hom.app (((coefficientSequenceRestriction l E V).obj M).obj n)).val.app U
        (integralComparisonRestrictedSection l E V M n.unop
          (op ((proEtaleIsoPostcompose k).obj
            ((proEtaleIsoPostcompose h).obj U.unop))) x))) = _
  rw [hd]
  erw [restrictedSection_naturality]
  erw [hm M n.unop U.unop, restrictedSection_map]
  erw [hk M n.unop ((proEtaleIsoPostcompose h).obj U.unop)]
  erw [hh ((integralComparisonSequencePullback l E k).obj M) n.unop U.unop]
  congr 1
  let B := (integralComparisonSequencePullback l E h).obj
    ((integralComparisonSequencePullback l E k).obj M)
  let v := (MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U.unop
  have hs := PresheafOfModules.naturality_apply
    ((integralComparisonSequenceComposition l E h k).hom.app M).val
    (Prod.mkHom (𝟙 n.unop) (proEtaleIsoCommaArrow (h ≫ k) U.unop)).op
    (integralComparisonSequenceGenerator l E (h ≫ k) M n.unop
      ((proEtaleIsoPostcompose (h ≫ k)).obj U.unop)
      (M.val.map (Prod.mkHom (𝟙 n.unop) v).op x))
  erw [hs]
  erw [sequenceGenerator_composition]
  erw [sequenceGenerator_naturality l E k M n.unop v x]
  erw [sequenceGenerator_naturality l E h
    ((integralComparisonSequencePullback l E k).obj M) n.unop
    ((proEtaleBaseChange k).map v)]
  erw [sequenceGenerator_naturality l E h
    ((integralComparisonSequencePullback l E k).obj M) n.unop
    (proEtaleIsoCommaArrow k ((proEtaleIsoPostcompose h).obj U.unop))]
  change B.val.presheaf.map _ (B.val.presheaf.map _ (B.val.presheaf.map _ _)) =
    B.val.presheaf.map _ (B.val.presheaf.map _ _)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  apply congrArg (fun f ↦ B.val.presheaf.map f
    (integralComparisonSequenceGenerator l E h
      ((integralComparisonSequencePullback l E k).obj M) n.unop
      ((proEtaleBaseChange k).obj
        ((proEtaleIsoPostcompose k).obj ((proEtaleIsoPostcompose h).obj U.unop)))
      (integralComparisonSequenceGenerator l E k M n.unop
        ((proEtaleIsoPostcompose k).obj ((proEtaleIsoPostcompose h).obj U.unop)) x)))
  apply congrArg Quiver.Hom.op
  apply Prod.hom_ext
  · simp
  · change proEtaleIsoCommaArrow (h ≫ k) U.unop ≫
        (MorphismProperty.Over.pullbackComp h k).hom.app _ ≫
        (proEtaleBaseChange h).map ((proEtaleBaseChange k).map v) = _
    erw [← (MorphismProperty.Over.pullbackComp h k).hom.naturality v]
    exact comma_composition h k U.unop

private theorem comparison_counit
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (S : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E Z)
    (F : IntegralComparisonPullbackModel l E h S ρ)
    (M : DerivedCategory (integralTowerModules l E W)) :
    (integralComparisonConstantTower l E Z).map
        (inverseImagePullbackComparisonDerived l E h hZ hW M ≫
          F.realization.hom.app M) ≫
        (integralComparisonTowerCounit l E Z).app
          ((coefficientSequenceDerivedRestriction l E Z).obj
            ((integralComparisonDerivedSequencePullback l E h).obj (S.reduction.obj M))) =
      (integralTowerInverseImageDiagonal l E h).hom.app M ≫
        (integralDerivedTowerInverseImage l E h).map
          ((integralComparisonConstantTower l E W).map (S.adjunction.unit.app M) ≫
            (integralComparisonTowerCounit l E W).app
              ((coefficientSequenceDerivedRestriction l E W).obj (S.reduction.obj M))) ≫
        (integralDerivedTowerInverseImageUnit l E h).hom.app (S.reduction.obj M) := by
  let a := inverseImagePullbackComparisonDerived l E h hZ hW M
  let e := F.realization.hom.app M
  let δ := (integralComparisonConstantTower l E W).map (S.adjunction.unit.app M) ≫
    (integralComparisonTowerCounit l E W).app
      ((coefficientSequenceDerivedRestriction l E W).obj (S.reduction.obj M))
  let H := inverseImageIntegralDerived l E h
  let ΔW := integralComparisonConstantTower l E W
  let ΔZ := integralComparisonConstantTower l E Z
  let U (X : Scheme.{u}) := coefficientSequenceDerivedRestriction.{u, u} l E X
  let B := integralComparisonDerivedSequencePullback l E h
  let Ht := integralDerivedTowerInverseImage l E h
  let d : ΔW ⟶ S.reduction ⋙ U W :=
    Functor.whiskerRight S.adjunction.unit ΔW ≫
      Functor.whiskerLeft (S.reduction ⋙ U W) (integralComparisonTowerCounit l E W)
  let γ : integralDerivedPullback l E h ⋙ ΔZ ⟶ S.reduction ⋙ B ⋙ U Z :=
    Functor.whiskerRight F.realization.hom ΔZ ≫
      Functor.whiskerLeft (S.reduction ⋙ B ⋙ U Z) (integralComparisonTowerCounit l E Z)
  let β : H ⋙ ΔZ ⟶ S.reduction ⋙ B ⋙ U Z :=
    (integralTowerInverseImageDiagonal l E h).hom ≫
      Functor.whiskerRight d Ht ≫
      Functor.whiskerLeft S.reduction (integralDerivedTowerInverseImageUnit l E h).hom
  obtain ⟨K, eK, P', q, hq, hformula⟩ :=
    chosenResolution_formula l E h hW hZ M
  let := hq
  let P := P'.obj
  let r : DerivedCategory.Q.obj P ≅ M := asIso (DerivedCategory.Q.map q) ≪≫ eK
  let aP := (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P ≫
    DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P) ≫
      (integralDerivedPullbackComparison l E h).inv.app P'
  have hP : ΔZ.map aP ≫ γ.app (DerivedCategory.Q.obj P) =
      β.app (DerivedCategory.Q.obj P) := by
    simpa only [γ, β, d, aP, P, H, ΔW, ΔZ, U, B, Ht, e, δ,
      Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, Functor.map_comp, Category.assoc] using
      integralPullbackKFlatReductionCounit l E h S ρ F P'
  have ha : H.map r.hom ≫ a = aP ≫ (integralDerivedPullback l E h).map r.hom := by
    rw [show a = _ from hformula]
    simp only [r, Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc]
    rw [← Category.assoc (H.map eK.hom), ← H.map_comp,
      eK.hom_inv_id, H.map_id, Category.id_comp]
    erw [← Category.assoc (H.map (DerivedCategory.Q.map q)),
      (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.naturality q]
    simp only [Functor.comp_map, Category.assoc, IsIso.hom_inv_id_assoc, aP, P]
  have ht := counitIdentity_transport H (integralDerivedPullback l E h) ΔZ
    (S.reduction ⋙ B ⋙ U Z) γ β r aP a ha hP
  simpa only [γ, β, d, H, ΔW, ΔZ, U, B, Ht, e, δ,
    Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.map_comp, Category.assoc] using ht

private inductive CompositionVertex
  | v0 | v1 | v2 | v3 | v4 | v5
  deriving DecidableEq, Fintype

section AbstractPasting

variable {A0 A1 A2 A3 A4 A5 : Type a}
  [Category.{b} A0] [Category.{b} A1] [Category.{b} A2]
  [Category.{b} A3] [Category.{b} A4] [Category.{b} A5]
  [Abelian A0] [Abelian A1] [Abelian A2] [Abelian A3] [Abelian A4] [Abelian A5]
  [HasDerivedCategory.{c} A0] [HasDerivedCategory.{c} A1] [HasDerivedCategory.{c} A2]
  [HasDerivedCategory.{c} A3] [HasDerivedCategory.{c} A4] [HasDerivedCategory.{c} A5]

private instance exactFunctor_additive {A B : Type a} [Category.{b} A] [Category.{b} B]
    [Abelian A] [Abelian B] (F : A ⥤ₑ B) : F.obj.Additive :=
  exactFunctor_le_additiveFunctor A B _ F.property

private def deriveTwoCell
    (F : A0 ⥤ₑ A1) (G : A1 ⥤ₑ A2) (H : A0 ⥤ₑ A3) (I : A3 ⥤ₑ A2)
    (e : F.obj ⋙ G.obj ≅ H.obj ⋙ I.obj) :=
  (Functor.mapDerivedCategoryCompIso F.obj G.obj).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso H.obj I.obj

private def deriveComposeCell
    (F : A0 ⥤ₑ A1) (G : A1 ⥤ₑ A2) (H : A0 ⥤ₑ A2)
    (e : F.obj ⋙ G.obj ≅ H.obj) :=
  (Functor.mapDerivedCategoryCompIso F.obj G.obj).symm ≪≫
    Functor.mapDerivedCategoryNatIso e

private def deriveExpandCell
    (F : A0 ⥤ₑ A2) (G : A0 ⥤ₑ A1) (H : A1 ⥤ₑ A2)
    (e : F.obj ≅ G.obj ⋙ H.obj) :=
  Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso G.obj H.obj

private theorem deriveUnitComposition
    (UV : A0 ⥤ₑ A3) (UW : A1 ⥤ₑ A4) (UZ : A2 ⥤ₑ A5)
    (FK : A0 ⥤ₑ A1) (FH : A1 ⥤ₑ A2) (FJ : A0 ⥤ₑ A2)
    (HK : A3 ⥤ₑ A4) (HH : A4 ⥤ₑ A5) (HJ : A3 ⥤ₑ A5)
    (ak : UV.obj ⋙ HK.obj ≅ FK.obj ⋙ UW.obj)
    (ah : UW.obj ⋙ HH.obj ≅ FH.obj ⋙ UZ.obj)
    (aj : UV.obj ⋙ HJ.obj ≅ FJ.obj ⋙ UZ.obj)
    (ct : HK.obj ⋙ HH.obj ≅ HJ.obj) (cs : FJ.obj ≅ FK.obj ⋙ FH.obj)
    (heq : Functor.whiskerLeft UV.obj ct.hom ≫ aj.hom ≫
        Functor.whiskerRight cs.hom UZ.obj =
      Functor.whiskerRight ak.hom HH.obj ≫ Functor.whiskerLeft FK.obj ah.hom) :
    Functor.whiskerLeft UV.obj.mapDerivedCategory (deriveComposeCell HK HH HJ ct).hom ≫
        (deriveTwoCell UV HJ FJ UZ aj).hom ≫
        Functor.whiskerRight (deriveExpandCell FJ FK FH cs).hom UZ.obj.mapDerivedCategory =
      Functor.whiskerRight (deriveTwoCell UV HK FK UW ak).hom HH.obj.mapDerivedCategory ≫
        Functor.whiskerLeft FK.obj.mapDerivedCategory (deriveTwoCell UW HH FH UZ ah).hom := by
  let C : CompositionVertex → Type a
    | .v0 => A0
    | .v1 => A1
    | .v2 => A2
    | .v3 => A3
    | .v4 => A4
    | .v5 => A5
  let : ∀ i : CompositionVertex, Category.{b} (C i)
    | .v0 => inferInstance
    | .v1 => inferInstance
    | .v2 => inferInstance
    | .v3 => inferInstance
    | .v4 => inferInstance
    | .v5 => inferInstance
  let : ∀ i : CompositionVertex, Abelian (C i)
    | .v0 => inferInstance
    | .v1 => inferInstance
    | .v2 => inferInstance
    | .v3 => inferInstance
    | .v4 => inferInstance
    | .v5 => inferInstance
  let : ∀ i : CompositionVertex, HasDerivedCategory.{c} (C i)
    | .v0 => inferInstance
    | .v1 => inferInstance
    | .v2 => inferInstance
    | .v3 => inferInstance
    | .v4 => inferInstance
    | .v5 => inferInstance
  let Uv : ExactDerivedPasting.Word C .v0 .v3 := .edge UV
  let Uw : ExactDerivedPasting.Word C .v1 .v4 := .edge UW
  let Uz : ExactDerivedPasting.Word C .v2 .v5 := .edge UZ
  let Hk : ExactDerivedPasting.Word C .v3 .v4 := .edge HK
  let Hh : ExactDerivedPasting.Word C .v4 .v5 := .edge HH
  let Hj : ExactDerivedPasting.Word C .v3 .v5 := .edge HJ
  let Fk : ExactDerivedPasting.Word C .v0 .v1 := .edge FK
  let Fh : ExactDerivedPasting.Word C .v1 .v2 := .edge FH
  let Fj : ExactDerivedPasting.Word C .v0 .v2 := .edge FJ
  let dk : ExactDerivedPasting.Expression C (.comp Uv Hk) (.comp Fk Uw) :=
    .cell ak.hom
  let dh : ExactDerivedPasting.Expression C (.comp Uw Hh) (.comp Fh Uz) :=
    .cell ah.hom
  let dj : ExactDerivedPasting.Expression C (.comp Uv Hj) (.comp Fj Uz) :=
    .cell aj.hom
  let dc : ExactDerivedPasting.Expression C (.comp Hk Hh) Hj :=
    .cell ct.hom
  let fc : ExactDerivedPasting.Expression C Fj (.comp Fk Fh) :=
    .cell cs.hom
  let left : ExactDerivedPasting.Expression C
      (.comp Uv (.comp Hk Hh)) (.comp (.comp Fk Fh) Uz) :=
    .vcomp (.input Uv dc) (.vcomp dj (.output fc Uz))
  let right : ExactDerivedPasting.Expression C
      (.comp Uv (.comp Hk Hh)) (.comp (.comp Fk Fh) Uz) :=
    .vcomp (.assocInv Uv Hk Hh)
      (.vcomp (.output dk Hh)
        (.vcomp (.assoc Fk Uw Hh)
          (.vcomp (.input Fk dh) (.assocInv Fk Fh Uz))))
  have he : left.ordinary = right.ordinary := by
    apply NatTrans.ext
    funext M
    have ht := congr_app heq M
    simpa only [left, right, dk, dh, dj, dc, fc, Uv, Uw, Uz, Hk, Hh, Hj, Fk, Fh, Fj,
      ExactDerivedPasting.Expression.ordinary, ExactDerivedPasting.Word.ordinary,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht
  have hdk : dk.derived = (deriveTwoCell UV HK FK UW ak).hom := by
    dsimp only [dk, Uv, Uw, Uz, Hk, Hh, Hj, Fk, Fh, Fj,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have hdh : dh.derived = (deriveTwoCell UW HH FH UZ ah).hom := by
    dsimp only [dh, Uv, Uw, Uz, Hk, Hh, Hj, Fk, Fh, Fj,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have hdj : dj.derived = (deriveTwoCell UV HJ FJ UZ aj).hom := by
    dsimp only [dj, Uv, Uw, Uz, Hk, Hh, Hj, Fk, Fh, Fj,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have hdc : dc.derived = (deriveComposeCell HK HH HJ ct).hom := by
    dsimp only [dc, Uv, Uw, Uz, Hk, Hh, Hj, Fk, Fh, Fj,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have hfc : fc.derived = (deriveExpandCell FJ FK FH cs).hom := by
    dsimp only [fc, Uv, Uw, Uz, Hk, Hh, Hj, Fk, Fh, Fj,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have ht := (ExactDerivedPasting.exact_derived_transformation_pasting C).2.1 left right he
  apply NatTrans.ext
  funext M
  have ht := congr_app ht M
  simpa only [left, right, ExactDerivedPasting.Expression.derived,
    hdk, hdh, hdj, hdc, hfc, Uv, Uw, Uz, Fk, Fh, Fj, Hk, Hh, Hj,
    ExactDerivedPasting.Word.derived, ExactDerivedPasting.Word.ordinary, ExactFunctor.of_fst,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_id', Functor.whiskerRight_id',
    Category.id_comp, Category.comp_id, Category.assoc] using ht

private theorem deriveDiagonalComposition
    (DV : A0 ⥤ₑ A3) (DW : A1 ⥤ₑ A4) (DZ : A2 ⥤ₑ A5)
    (IK : A0 ⥤ₑ A1) (IH : A1 ⥤ₑ A2) (IJ : A0 ⥤ₑ A2)
    (HK : A3 ⥤ₑ A4) (HH : A4 ⥤ₑ A5) (HJ : A3 ⥤ₑ A5)
    (ak : IK.obj ⋙ DW.obj ≅ DV.obj ⋙ HK.obj)
    (ah : IH.obj ⋙ DZ.obj ≅ DW.obj ⋙ HH.obj)
    (aj : IJ.obj ⋙ DZ.obj ≅ DV.obj ⋙ HJ.obj)
    (ct : HK.obj ⋙ HH.obj ≅ HJ.obj) (ci : IK.obj ⋙ IH.obj ≅ IJ.obj)
    (heq : Functor.whiskerRight ci.hom DZ.obj ≫ aj.hom =
      Functor.whiskerLeft IK.obj ah.hom ≫ Functor.whiskerRight ak.hom HH.obj ≫
        Functor.whiskerLeft DV.obj ct.hom) :
    Functor.whiskerRight (deriveComposeCell IK IH IJ ci).hom DZ.obj.mapDerivedCategory ≫
        (deriveTwoCell IJ DZ DV HJ aj).hom =
      Functor.whiskerLeft IK.obj.mapDerivedCategory (deriveTwoCell IH DZ DW HH ah).hom ≫
        Functor.whiskerRight (deriveTwoCell IK DW DV HK ak).hom HH.obj.mapDerivedCategory ≫
        Functor.whiskerLeft DV.obj.mapDerivedCategory (deriveComposeCell HK HH HJ ct).hom := by
  let C : CompositionVertex → Type a
    | .v0 => A0
    | .v1 => A1
    | .v2 => A2
    | .v3 => A3
    | .v4 => A4
    | .v5 => A5
  let : ∀ i : CompositionVertex, Category.{b} (C i)
    | .v0 => inferInstance
    | .v1 => inferInstance
    | .v2 => inferInstance
    | .v3 => inferInstance
    | .v4 => inferInstance
    | .v5 => inferInstance
  let : ∀ i : CompositionVertex, Abelian (C i)
    | .v0 => inferInstance
    | .v1 => inferInstance
    | .v2 => inferInstance
    | .v3 => inferInstance
    | .v4 => inferInstance
    | .v5 => inferInstance
  let : ∀ i : CompositionVertex, HasDerivedCategory.{c} (C i)
    | .v0 => inferInstance
    | .v1 => inferInstance
    | .v2 => inferInstance
    | .v3 => inferInstance
    | .v4 => inferInstance
    | .v5 => inferInstance
  let Dv : ExactDerivedPasting.Word C .v0 .v3 := .edge DV
  let Dw : ExactDerivedPasting.Word C .v1 .v4 := .edge DW
  let Dz : ExactDerivedPasting.Word C .v2 .v5 := .edge DZ
  let Ik : ExactDerivedPasting.Word C .v0 .v1 := .edge IK
  let Ih : ExactDerivedPasting.Word C .v1 .v2 := .edge IH
  let Ij : ExactDerivedPasting.Word C .v0 .v2 := .edge IJ
  let Hk : ExactDerivedPasting.Word C .v3 .v4 := .edge HK
  let Hh : ExactDerivedPasting.Word C .v4 .v5 := .edge HH
  let Hj : ExactDerivedPasting.Word C .v3 .v5 := .edge HJ
  let dk : ExactDerivedPasting.Expression C (.comp Ik Dw) (.comp Dv Hk) :=
    .cell ak.hom
  let dh : ExactDerivedPasting.Expression C (.comp Ih Dz) (.comp Dw Hh) :=
    .cell ah.hom
  let dj : ExactDerivedPasting.Expression C (.comp Ij Dz) (.comp Dv Hj) :=
    .cell aj.hom
  let dc : ExactDerivedPasting.Expression C (.comp Hk Hh) Hj :=
    .cell ct.hom
  let ic : ExactDerivedPasting.Expression C (.comp Ik Ih) Ij :=
    .cell ci.hom
  let left : ExactDerivedPasting.Expression C
      (.comp (.comp Ik Ih) Dz) (.comp Dv Hj) :=
    .vcomp (.output ic Dz) dj
  let right : ExactDerivedPasting.Expression C
      (.comp (.comp Ik Ih) Dz) (.comp Dv Hj) :=
    .vcomp (.assoc Ik Ih Dz)
      (.vcomp (.input Ik dh)
        (.vcomp (.assocInv Ik Dw Hh)
          (.vcomp (.output dk Hh)
            (.vcomp (.assoc Dv Hk Hh) (.input Dv dc)))))
  have he : left.ordinary = right.ordinary := by
    apply NatTrans.ext
    funext M
    have ht := congr_app heq M
    simpa only [left, right, dk, dh, dj, dc, ic, Dv, Dw, Dz, Hk, Hh, Hj, Ik, Ih, Ij,
      ExactDerivedPasting.Expression.ordinary, ExactDerivedPasting.Word.ordinary,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht
  have hdk : dk.derived = (deriveTwoCell IK DW DV HK ak).hom := by
    dsimp only [dk, Dv, Dw, Dz, Hk, Hh, Hj, Ik, Ih, Ij,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have hdh : dh.derived = (deriveTwoCell IH DZ DW HH ah).hom := by
    dsimp only [dh, Dv, Dw, Dz, Hk, Hh, Hj, Ik, Ih, Ij,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have hdj : dj.derived = (deriveTwoCell IJ DZ DV HJ aj).hom := by
    dsimp only [dj, Dv, Dw, Dz, Hk, Hh, Hj, Ik, Ih, Ij,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have hdc : dc.derived = (deriveComposeCell HK HH HJ ct).hom := by
    dsimp only [dc, Dv, Dw, Dz, Hk, Hh, Hj, Ik, Ih, Ij,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have hic : ic.derived = (deriveComposeCell IK IH IJ ci).hom := by
    dsimp only [ic, Dv, Dw, Dz, Hk, Hh, Hj, Ik, Ih, Ij,
      ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
      ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
      ExactDerivedPasting.Word.derived, deriveTwoCell, deriveComposeCell, deriveExpandCell,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.refl_hom, Iso.refl_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.mapDerivedCategoryNatIso, Localization.liftNatIso_hom]
    simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id',
      Category.id_comp, Category.comp_id]
    rfl
  have ht := (ExactDerivedPasting.exact_derived_transformation_pasting C).2.1 left right he
  apply NatTrans.ext
  funext M
  have ht := congr_app ht M
  simpa only [left, right, ExactDerivedPasting.Expression.derived,
    hdk, hdh, hdj, hdc, hic, Dv, Dw, Dz, Ik, Ih, Ij, Hk, Hh, Hj,
    ExactDerivedPasting.Word.derived, ExactDerivedPasting.Word.ordinary, ExactFunctor.of_fst,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_id', Functor.whiskerRight_id',
    Category.id_comp, Category.comp_id, Category.assoc] using ht

end AbstractPasting

private theorem derivedTowerUnit_composition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    Functor.whiskerLeft (coefficientSequenceDerivedRestriction l E V)
        (towerDerivedCompositor l E h k).hom ≫
      (integralDerivedTowerInverseImageUnit l E (h ≫ k)).hom ≫
      Functor.whiskerRight (integralComparisonSystemComposition l E h k).hom
        (coefficientSequenceDerivedRestriction l E Z) =
    Functor.whiskerRight (integralDerivedTowerInverseImageUnit l E k).hom
        (integralDerivedTowerInverseImage l E h) ≫
      Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E k)
        (integralDerivedTowerInverseImageUnit l E h).hom := by
  have hh := deriveUnitComposition
    (ExactFunctor.of (coefficientSequenceRestriction l E V))
    (ExactFunctor.of (coefficientSequenceRestriction l E W))
    (ExactFunctor.of (coefficientSequenceRestriction l E Z))
    (ExactFunctor.of (integralComparisonSequencePullback l E k))
    (ExactFunctor.of (integralComparisonSequencePullback l E h))
    (ExactFunctor.of (integralComparisonSequencePullback l E (h ≫ k)))
    (ExactFunctor.of (integralTowerInverseImage l E k))
    (ExactFunctor.of (integralTowerInverseImage l E h))
    (ExactFunctor.of (integralTowerInverseImage l E (h ≫ k)))
    (integralTowerInverseImageUnit l E k) (integralTowerInverseImageUnit l E h)
    (integralTowerInverseImageUnit l E (h ≫ k)) (towerCompositorNat l E h k)
    (integralComparisonSequenceComposition l E h k) (by
      apply NatTrans.ext
      funext M
      change (towerCompositor l E h k (integralInverseImageComposition l E h k)
          ((coefficientSequenceRestriction l E V).obj M)).hom ≫
          (integralTowerInverseImageUnit l E (h ≫ k)).hom.app M ≫
          (coefficientSequenceRestriction l E Z).map
            ((integralComparisonSequenceComposition l E h k).hom.app M) = _
      exact towerUnit_composition l E h k (integralInverseImageComposition l E h k)
        (integralInverseImageComposition_existsUnique l E h k).exists.choose_spec M)
  simpa only [deriveTwoCell, deriveComposeCell, deriveExpandCell, ExactFunctor.of_fst,
    integralDerivedTowerInverseImageUnit, integralComparisonSystemComposition,
    integralInverseImageDerivedComposition, integralTowerInverseImageDiagonal,
    towerDerivedCompositor, coefficientSequenceDerivedRestriction,
    integralComparisonDerivedSequencePullback, integralDerivedTowerInverseImage,
    integralComparisonConstantTower, inverseImageIntegralDerived] using hh

private theorem derivedTowerDiagonal_composition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    Functor.whiskerRight (integralInverseImageDerivedComposition l E h k).hom
        (integralComparisonConstantTower l E Z) ≫
      (integralTowerInverseImageDiagonal l E (h ≫ k)).hom =
    Functor.whiskerLeft (inverseImageIntegralDerived l E k)
        (integralTowerInverseImageDiagonal l E h).hom ≫
      Functor.whiskerRight (integralTowerInverseImageDiagonal l E k).hom
        (integralDerivedTowerInverseImage l E h) ≫
      Functor.whiskerLeft (integralComparisonConstantTower l E V)
        (towerDerivedCompositor l E h k).hom := by
  have hh := deriveDiagonalComposition
    (ExactFunctor.of (Functor.const ℕᵒᵖ : integralTowerModules l E V ⥤ _))
    (ExactFunctor.of (Functor.const ℕᵒᵖ : integralTowerModules l E W ⥤ _))
    (ExactFunctor.of (Functor.const ℕᵒᵖ : integralTowerModules l E Z ⥤ _))
    (ExactFunctor.of (inverseImageIntegralModules l E k))
    (ExactFunctor.of (inverseImageIntegralModules l E h))
    (ExactFunctor.of (inverseImageIntegralModules l E (h ≫ k)))
    (ExactFunctor.of (integralTowerInverseImage l E k))
    (ExactFunctor.of (integralTowerInverseImage l E h))
    (ExactFunctor.of (integralTowerInverseImage l E (h ≫ k)))
    (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E k))
    (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E h))
    (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E (h ≫ k)))
    (towerCompositorNat l E h k) (integralInverseImageComposition l E h k) (by
      apply NatTrans.ext
      funext M
      apply NatTrans.ext
      funext n
      change (integralInverseImageComposition l E h k).hom.app M ≫ 𝟙 _ =
        𝟙 _ ≫ (inverseImageIntegralModules l E h).map (𝟙 _) ≫
          (integralInverseImageComposition l E h k).hom.app M
      erw [(inverseImageIntegralModules l E h).map_id]
      simp only [Category.id_comp, Category.comp_id])
  simpa only [id_eq, deriveTwoCell, deriveComposeCell, deriveExpandCell, ExactFunctor.of_fst,
    integralDerivedTowerInverseImageUnit, integralComparisonSystemComposition,
    integralInverseImageDerivedComposition, integralTowerInverseImageDiagonal,
    towerDerivedCompositor, coefficientSequenceDerivedRestriction,
    integralComparisonDerivedSequencePullback, integralDerivedTowerInverseImage,
    integralComparisonConstantTower, inverseImageIntegralDerived] using hh

private theorem towerUnit_derivedComposition {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (N : DerivedCategory (integralTowerModules l E V))
    (T : coefficientSequenceDerived l E V)
    (δ : (integralComparisonConstantTower l E V).obj N ⟶
      (coefficientSequenceDerivedRestriction l E V).obj T) :
    (integralComparisonConstantTower l E Z).map
        ((integralInverseImageDerivedComposition l E h k).hom.app N) ≫
        (integralTowerInverseImageDiagonal l E (h ≫ k)).hom.app N ≫
        (integralDerivedTowerInverseImage l E (h ≫ k)).map δ ≫
        (integralDerivedTowerInverseImageUnit l E (h ≫ k)).hom.app T ≫
        (coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonSystemComposition l E h k).hom.app T) =
      (integralTowerInverseImageDiagonal l E h).hom.app
          ((inverseImageIntegralDerived l E k).obj N) ≫
        (integralDerivedTowerInverseImage l E h).map
          ((integralTowerInverseImageDiagonal l E k).hom.app N ≫
            (integralDerivedTowerInverseImage l E k).map δ ≫
            (integralDerivedTowerInverseImageUnit l E k).hom.app T) ≫
        (integralDerivedTowerInverseImageUnit l E h).hom.app
          ((integralComparisonDerivedSequencePullback l E k).obj T) := by
  have hd := congr_app (derivedTowerDiagonal_composition l E h k) N
  have hu := congr_app (derivedTowerUnit_composition l E h k) T
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app] at hd hu
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hd]
  simp only [Category.assoc]
  erw [← (towerDerivedCompositor l E h k).hom.naturality_assoc δ]
  rw [hu]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]

/-- The specified integral inverse-image comparison respects composition, as an
actual equality in the ambient completed-coefficient derived category.
Source: blueprint Global powers; Stacks 03D6, 0D6D and 0941
(blueprint: lem-trf-integral-inverse-image-comparison-composition).

Proof:
1. Integral pullback preserves the recorded constructible category. The specified
inverse-image compositor is the unique one respecting constant sections.
2. Its action on the adjunction generators is the composite of the two generator
maps. Naturality of these generators and the pullback comma maps therefore prove
composition of the whole-tower tensor units, before taking any reductions.
3. Exact-derived transformation pasting transports this ordinary tower identity
and the constant-tower diagonal identity to the derived categories. Naturality of
the derived tower compositor combines them for the reduction unit of N.
4. The K-flat reduction counit identity is transported from the representative
actually chosen in the comparison map to N by naturality. Resolution matching
computes the iterated pullback comparison after the specified realization eta.
The preceding tower identity identifies its adjunct with that of the composite
comparison. Injectivity of the constant-tower/derived-limit adjunction then gives
equality after eta; cancellation of eta proves the displayed equality -/
theorem integralInverseImageComparison_composition
    (D : IntegralComparisonSystem.{u} l)
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ v : V, Invertible (l : V.residueField v)]
    (N : sfIntegralConstructibleCategory l E V) :
    sfIntegralConstructible l E W ((integralDerivedPullback l E k).obj N.obj) ∧
      (integralInverseImageDerivedComposition l E h k).hom.app N.obj ≫
          inverseImagePullbackComparisonDerived l E (h ≫ k)
            (fun z ↦ isUnit_of_map_unit (IsLocalRing.residue (Z.presheaf.stalk z)) _
              ((map_natCast (IsLocalRing.residue (Z.presheaf.stalk z)) l).symm ▸
                isUnit_of_invertible (l : Z.residueField z)))
            (fun v ↦ isUnit_of_map_unit (IsLocalRing.residue (V.presheaf.stalk v)) _
              ((map_natCast (IsLocalRing.residue (V.presheaf.stalk v)) l).symm ▸
                isUnit_of_invertible (l : V.residueField v))) N.obj ≫
          (integralComparisonComposition l E D h k N).hom =
        (inverseImageIntegralDerived l E h).map
            (inverseImagePullbackComparisonDerived l E k
              (fun w ↦ isUnit_of_map_unit (IsLocalRing.residue (W.presheaf.stalk w)) _
                ((map_natCast (IsLocalRing.residue (W.presheaf.stalk w)) l).symm ▸
                  isUnit_of_invertible (l : W.residueField w)))
              (fun v ↦ isUnit_of_map_unit (IsLocalRing.residue (V.presheaf.stalk v)) _
                ((map_natCast (IsLocalRing.residue (V.presheaf.stalk v)) l).symm ▸
                  isUnit_of_invertible (l : V.residueField v))) N.obj) ≫
          inverseImagePullbackComparisonDerived l E h
            (fun z ↦ isUnit_of_map_unit (IsLocalRing.residue (Z.presheaf.stalk z)) _
              ((map_natCast (IsLocalRing.residue (Z.presheaf.stalk z)) l).symm ▸
                isUnit_of_invertible (l : Z.residueField z)))
            (fun w ↦ isUnit_of_map_unit (IsLocalRing.residue (W.presheaf.stalk w)) _
              ((map_natCast (IsLocalRing.residue (W.presheaf.stalk w)) l).symm ▸
                isUnit_of_invertible (l : W.residueField w)))
            ((integralDerivedPullback l E k).obj N.obj) := by
  refine ⟨((constructibleIntegralPullback l E k).obj N).property, ?_⟩
  let hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z) := fun z ↦
    isUnit_of_map_unit (IsLocalRing.residue (Z.presheaf.stalk z)) _
      ((map_natCast (IsLocalRing.residue (Z.presheaf.stalk z)) l).symm ▸
        isUnit_of_invertible (l : Z.residueField z))
  let hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w) := fun w ↦
    isUnit_of_map_unit (IsLocalRing.residue (W.presheaf.stalk w)) _
      ((map_natCast (IsLocalRing.residue (W.presheaf.stalk w)) l).symm ▸
        isUnit_of_invertible (l : W.residueField w))
  let hV : ∀ v : V, IsUnit (l : V.presheaf.stalk v) := fun v ↦
    isUnit_of_map_unit (IsLocalRing.residue (V.presheaf.stalk v)) _
      ((map_natCast (IsLocalRing.residue (V.presheaf.stalk v)) l).symm ▸
        isUnit_of_invertible (l : V.residueField v))
  let Δ := integralComparisonConstantTower l E Z
  let U := coefficientSequenceDerivedRestriction l E Z
  let T := (integralComparisonDerivedSequencePullback l E h).obj
    ((integralComparisonDerivedSequencePullback l E k).obj
      (((D.coefficient E).system V).reduction.obj N.obj))
  let η := integralComparisonEta l E D h k N
  let a := (integralInverseImageDerivedComposition l E h k).hom.app N.obj
  let b := inverseImagePullbackComparisonDerived l E (h ≫ k) hZ hV N.obj
  let c := (integralComparisonComposition l E D h k N).hom
  let f := (inverseImageIntegralDerived l E h).map
    (inverseImagePullbackComparisonDerived l E k hW hV N.obj)
  let g := inverseImagePullbackComparisonDerived l E h hZ hW
    ((integralDerivedPullback l E k).obj N.obj)
  change a ≫ b ≫ c = f ≫ g
  apply (cancel_mono η.hom).1
  apply ((integralComparisonConstantAdjunction l E Z).homEquiv _ (U.obj T)).symm.injective
  change Δ.map ((a ≫ b ≫ c) ≫ η.hom) ≫
      (integralComparisonTowerCounit l E Z).app (U.obj T) =
    Δ.map ((f ≫ g) ≫ η.hom) ≫
      (integralComparisonTowerCounit l E Z).app (U.obj T)
  let S := (D.coefficient E).system V
  let δ := (integralComparisonConstantTower l E V).map (S.adjunction.unit.app N.obj) ≫
    (integralComparisonTowerCounit l E V).app
      ((coefficientSequenceDerivedRestriction l E V).obj (S.reduction.obj N.obj))
  let τ := (integralComparisonSystemComposition l E h k).hom.app (S.reduction.obj N.obj)
  have hcomp : c ≫ η.hom =
      ((D.coefficient E).pullback (h ≫ k)).realization.hom.app N.obj ≫
        (coefficientSequenceLimit l E Z).map τ := by
    simp only [c, η, integralComparisonComposition, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hk := comparison_counit l E k hV hW S ((D.coefficient E).roos W)
    ((D.coefficient E).pullback k) N.obj
  have hkh := comparison_counit l E (h ≫ k) hV hZ S ((D.coefficient E).roos Z)
    ((D.coefficient E).pullback (h ≫ k)) N.obj
  have hh := integralPullbackResolutionMatching l E D h k hV hW hZ N
  have ht := towerUnit_derivedComposition l E h k N.obj (S.reduction.obj N.obj) δ
  have hleft : Δ.map ((a ≫ b ≫ c) ≫ η.hom) ≫
      (integralComparisonTowerCounit l E Z).app (U.obj T) =
      Δ.map a ≫ (integralTowerInverseImageDiagonal l E (h ≫ k)).hom.app N.obj ≫
        (integralDerivedTowerInverseImage l E (h ≫ k)).map δ ≫
        (integralDerivedTowerInverseImageUnit l E (h ≫ k)).hom.app (S.reduction.obj N.obj) ≫
        U.map τ := by
    rw [Category.assoc, Category.assoc, hcomp]
    simp only [Functor.map_comp, Category.assoc]
    erw [(integralComparisonTowerCounit l E Z).naturality (U.map τ)]
    simp only [Functor.id_map]
    erw [← Δ.map_comp_assoc b]
    erw [← Category.assoc _ _ (U.map τ), hkh]
    simp only [Category.assoc]
    rfl
  have hright : Δ.map ((f ≫ g) ≫ η.hom) ≫
      (integralComparisonTowerCounit l E Z).app (U.obj T) =
      (integralTowerInverseImageDiagonal l E h).hom.app
          ((inverseImageIntegralDerived l E k).obj N.obj) ≫
        (integralDerivedTowerInverseImage l E h).map
          ((integralTowerInverseImageDiagonal l E k).hom.app N.obj ≫
            (integralDerivedTowerInverseImage l E k).map δ ≫
            (integralDerivedTowerInverseImageUnit l E k).hom.app (S.reduction.obj N.obj)) ≫
        (integralDerivedTowerInverseImageUnit l E h).hom.app
          ((integralComparisonDerivedSequencePullback l E k).obj (S.reduction.obj N.obj)) := by
    simp only [Functor.map_comp, Category.assoc]
    erw [← Δ.map_comp_assoc g η.hom]
    erw [hh]
    erw [← Category.assoc, (integralTowerInverseImageDiagonal l E h).hom.naturality]
    simp only [Functor.comp_map, Category.assoc]
    erw [← (integralDerivedTowerInverseImage l E h).map_comp_assoc]
    erw [← (integralComparisonConstantTower l E W).map_comp_assoc]
    erw [hk]
    simp only [δ, Functor.map_comp, Category.assoc]
    rfl
  exact hleft.trans (ht.trans hright.symm)

end AlgebraicGeometry.ProEtale
