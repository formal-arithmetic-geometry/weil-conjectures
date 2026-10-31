/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveLineRestriction
public import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.WeilSheaf.Native.NativeImmersionHeartLocalization
import WeilConjectures.AlgebraicGeometry.Native.NativeCompactificationModelComparison
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # The affine chart of the relative projective line -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory Limits Pretriangulated

universe v vC vD vE uC uD uE wC wD wE

private theorem transport_localization_triangle
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) {A B D : C}
    (e₁ : A ≅ T.obj₁) (e₂ : B ≅ T.obj₂) (e₃ : D ≅ T.obj₃)
    (a : A ⟶ B) (b : B ⟶ D)
    (ha : a ≫ e₂.hom = e₁.hom ≫ T.mor₁)
    (hb : b ≫ e₃.hom = e₂.hom ≫ T.mor₂) :
    ∃ w, Triangle.mk a b w ∈ distTriang C := by
  refine ⟨e₃.hom ≫ T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv,
    isomorphic_distinguished _ hT _ ?_⟩
  refine Triangle.isoMk _ _ e₁ e₂ e₃ ha hb ?_
  change (e₃.hom ≫ T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv) ≫
    (shiftFunctor C (1 : ℤ)).map e₁.hom = e₃.hom ≫ T.mor₃
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id]

private theorem exact_localization_triangle
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
    {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
    (P : C ⥤ D) (J : D ⥤ C) (Q : C ⥤ E) (I : E ⥤ C)
    [P.Additive] [J.Additive] [Q.Additive] [I.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (aj : J ⊣ P) (ai : Q ⊣ I)
    (h : ∀ M, ∃ z : aj.counit.app M ≫ ai.unit.app M = 0,
      (ShortComplex.mk (aj.counit.app M) (ai.unit.app M) z).ShortExact)
    (K : _root_.DerivedCategory C) :
    ∃ w, Triangle.mk (aj.mapExactDerivedCategory.counit.app K)
      (ai.mapExactDerivedCategory.unit.app K) w ∈ distTriang (_root_.DerivedCategory C) := by
  classical
  have hrep (L : CochainComplex C ℤ) :
      ∃ w, Triangle.mk
        (aj.mapExactDerivedCategory.counit.app (_root_.DerivedCategory.Q.obj L))
        (ai.mapExactDerivedCategory.unit.app (_root_.DerivedCategory.Q.obj L)) w ∈
          distTriang (_root_.DerivedCategory C) := by
    let a := (aj.mapHomologicalComplex (.up ℤ)).counit.app L
    let b := (ai.mapHomologicalComplex (.up ℤ)).unit.app L
    let S := ShortComplex.mk a b (by ext n : 1; exact (h (L.X n)).choose)
    have hS : S.ShortExact :=
      HomologicalComplex.shortExact_of_degreewise_shortExact S
        (fun n ↦ (h (L.X n)).choose_spec)
    let e₁ := J.mapDerivedCategory.mapIso (P.mapDerivedCategoryFactors.app L) ≪≫
      J.mapDerivedCategoryFactors.app ((P.mapHomologicalComplex (.up ℤ)).obj L)
    let e₃ := I.mapDerivedCategory.mapIso (Q.mapDerivedCategoryFactors.app L) ≪≫
      I.mapDerivedCategoryFactors.app ((Q.mapHomologicalComplex (.up ℤ)).obj L)
    apply transport_localization_triangle (_root_.DerivedCategory.triangleOfSES_distinguished hS)
      e₁ (Iso.refl _) e₃
    · change aj.mapExactDerivedCategory.counit.app (_root_.DerivedCategory.Q.obj L) ≫
          𝟙 _ = e₁.hom ≫ _root_.DerivedCategory.Q.map a
      rw [Category.comp_id]
      simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app]
      simp only [e₁, a, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_inv,
        Category.assoc]
    · have hu : ai.mapExactDerivedCategory.unit.app (_root_.DerivedCategory.Q.obj L) =
          _root_.DerivedCategory.Q.map b ≫ e₃.inv := by
        simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
        rfl
      rw [hu]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.refl_hom,
        Category.id_comp, _root_.DerivedCategory.triangleOfSES_mor₂]
      rfl
  let L := _root_.DerivedCategory.Q.objPreimage K
  let e := _root_.DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨w, hw⟩ := hrep L
  apply transport_localization_triangle hw
    ((P.mapDerivedCategory ⋙ J.mapDerivedCategory).mapIso e.symm) e.symm
    ((Q.mapDerivedCategory ⋙ I.mapDerivedCategory).mapIso e.symm)
  · exact (aj.mapExactDerivedCategory.counit.naturality e.inv).symm
  · exact (ai.mapExactDerivedCategory.unit.naturality e.inv).symm

private theorem section_restriction_identity
    {A : Type uC} [Category.{vC} A] {B : Type uD} [Category.{vD} B]
    {L : A ⥤ B} {R : B ⥤ A} {I : B ⥤ A} {D : A ⥤ B}
    (a : L ⊣ R) (b : I ⊣ D) (e : L ⋙ I ≅ 𝟭 A) (K : A) :
    let d := (a.comp b).ofNatIsoLeft e
    let c := Adjunction.rightAdjointUniq d Adjunction.id
    R.map (b.unit.app (L.obj K)) ≫ c.hom.app (I.obj (L.obj K)) =
      e.inv.app (R.obj (L.obj K)) ≫ I.map (a.counit.app (L.obj K)) := by
  dsimp only
  let d := (a.comp b).ofNatIsoLeft e
  let c := Adjunction.rightAdjointUniq d Adjunction.id
  have hc (M : A) : c.hom.app M = e.inv.app (R.obj (D.obj M)) ≫
      I.map (a.counit.app (D.obj M)) ≫ b.counit.app M := by
    have h := Adjunction.rightAdjointUniq_hom_app_counit d Adjunction.id M
    change c.hom.app M ≫ 𝟙 _ = d.counit.app M at h
    rw [Category.comp_id] at h
    rw [h]
    simp only [d, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Adjunction.comp_counit_app]
    rfl
  change R.map (b.unit.app (L.obj K)) ≫ c.hom.app _ = _
  rw [hc]
  have hn := e.inv.naturality (R.map (b.unit.app (L.obj K)))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  rw [← Category.assoc, hn, Category.assoc]
  change e.inv.app (R.obj (L.obj K)) ≫
      I.map (L.map (R.map (b.unit.app (L.obj K)))) ≫
        I.map (a.counit.app (D.obj (I.obj (L.obj K)))) ≫
          b.counit.app (I.obj (L.obj K)) = _
  have hm := a.counit.naturality (b.unit.app (L.obj K))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hm
  rw [← I.map_comp_assoc, hm]
  rw [I.map_comp, Category.assoc, b.left_triangle_components,
    Category.comp_id]

namespace AlgebraicGeometry.WeilComplex

attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing
  ULift.commRing AlgebraicClosure.instCommRing

private noncomputable def chartExtension
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [X.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilComplex k₀ l U ⥤ WeilComplex k₀ l X :=
  (objectProperty k₀ l U).liftFullSubcategory (objectProperty k₀ l X)
    (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory
    (fun K hK ↦
      ⟨(ProEtaleWeilSheaf.extensionByZero k₀ l j).bounded_mapDerivedCategory_obj hK.1,
        fun n ↦ (WeilSheaf.objectProperty k₀ l X).prop_of_iso
          (((ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategoryHomologyFunctorIso
            n).app K)
          (WeilSheaf.isAdicConstructibleSheaf_extensionByZero j _ (hK.2 n))⟩)

private theorem chart_localization
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {U X Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    ∃ α : upperStar j ⋙ chartExtension (k₀ := k₀) (l := l) j ⟶ 𝟭 _,
      ∀ K, ∃ w, Triangle.mk (α.app K)
        ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) i).unit.app K) w ∈
          distTriang (WeilComplex k₀ l X) := by
  classical
  have : PreservesFiniteColimits (ProEtaleWeilSheaf.lowerStar k₀ l i) :=
    ProEtaleWeilSheaf.preservesFiniteColimits_lowerStar_of_isCompl i j hij
  obtain ⟨aj, ai, hlocal⟩ :=
    ProEtaleWeilSheaf.nativeImmersionHeartLocalization k₀ l X U Z j i hij
  let ajd := aj.mapExactDerivedCategory
  let aid := ai.mapExactDerivedCategory
  let ai' := ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l i
  let c := Adjunction.rightAdjointUniq aid ai'
  let α : upperStar j ⋙ chartExtension (k₀ := k₀) (l := l) j ⟶ 𝟭 _ :=
    { app K := ObjectProperty.homMk (ajd.counit.app K.obj)
      naturality K L f := by
        apply (objectProperty k₀ l X).fullyFaithfulι.map_injective
        exact ajd.counit.naturality f.hom }
  refine ⟨α, fun K ↦ ?_⟩
  obtain ⟨w, hw⟩ := exact_localization_triangle
    (ProEtaleWeilSheaf.upperStar k₀ l j) (ProEtaleWeilSheaf.extensionByZero k₀ l j)
    (ProEtaleWeilSheaf.upperStar k₀ l i) (ProEtaleWeilSheaf.lowerStar k₀ l i)
    aj ai hlocal.2.2.2.2 K.obj
  have hb : (ai'.unit.app K.obj) ≫ c.inv.app
        ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.obj K.obj) =
      aid.unit.app K.obj := by
    rw [← Adjunction.unit_rightAdjointUniq_hom_app aid ai' K.obj]
    change (aid.unit.app K.obj ≫ c.hom.app _) ≫ c.inv.app _ = aid.unit.app K.obj
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  obtain ⟨w', hw'⟩ := transport_localization_triangle hw
    (Iso.refl _) (Iso.refl _)
    (c.symm.app ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.obj K.obj))
    (ajd.counit.app K.obj) (ai'.unit.app K.obj)
    (by
      change ajd.counit.app K.obj ≫ 𝟙 _ = 𝟙 _ ≫ ajd.counit.app K.obj
      simp only [Category.comp_id, Category.id_comp])
    (by
      change ai'.unit.app K.obj ≫ c.inv.app _ = 𝟙 _ ≫ aid.unit.app K.obj
      rw [Category.id_comp]
      exact hb)
  let ι := (objectProperty k₀ l X).ι
  let T : Triangle (WeilComplex k₀ l X) := Triangle.mk (α.app K)
    ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) i).unit.app K)
    (ObjectProperty.homMk (w' ≫ (ι.commShiftIso (1 : ℤ)).inv.app
      ((upperStar j ⋙ chartExtension (k₀ := k₀) (l := l) j).obj K)))
  refine ⟨T.mor₃, ?_⟩
  change ι.mapTriangle.obj T ∈ distTriang _
  apply isomorphic_distinguished _ hw' _
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change ι.map ((upperStarDerivedLowerStarAdjunction i).unit.app K) = ai'.unit.app K.obj
    simp only [upperStarDerivedLowerStarAdjunction,
      Adjunction.map_restrictFullyFaithful_unit_app, Iso.refl_hom, NatTrans.id_app,
      ]
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id]
    rfl
  · change ((w' ≫ (ι.commShiftIso (1 : ℤ)).inv.app
        ((upperStar j ⋙ chartExtension (k₀ := k₀) (l := l) j).obj K)) ≫
        (ι.commShiftIso (1 : ℤ)).hom.app
          ((upperStar j ⋙ chartExtension (k₀ := k₀) (l := l) j).obj K)) ≫
        (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = 𝟙 _ ≫ w'
    simp only [CategoryTheory.Functor.map_id, Category.id_comp,
      Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id, Category.comp_id]

/-- The compact-support localization triangle for the affine chart of the projective line
(blueprint: lem-pur-b3-weil-affine-localization).

Source: blueprint `sk-prop-an` (integration; recorded unit Step 5), the open-closed
triangle followed by proper direct
image), and `prop-sf-open-closed-triangle-all-stages`. Identify Y with the affine line over X
using the given cartesian square. Its standard compactification is the projective line over
X, with complementary closed section infinity. Apply the open-closed localization triangle
to q^*K. Proper direct image along q preserves distinguished triangles. The composition
comparison identifies its first term with Rπ_!π^*K and its last term with K, since infinity
is a section. The middle term is Rq_*q^*K by properness of q. Under these comparisons the
second arrow is restriction to infinity: use the counit description of restriction and the
adjunction identities. The first arrow is natural in K since it is the open counit followed
by proper direct image, and all comparison maps are natural. No calculation of projective
or affine cohomology is required for this localization statement. -/
theorem exists_affineChart_localization
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
    [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ α : upperStar π ⋙ derivedLowerShriek k₀ l π ⟶
        projectiveLineCohomology (k₀ := k₀) (l := l) X,
      ∀ K, ∃ w, Triangle.mk (α.app K) ((projectiveLineRestriction X).app K) w ∈
        distTriang (WeilComplex k₀ l X) := by
  classical
  let q := ProjectiveLine X ↘ X
  let i := ProjectiveLine.infinity X
  let aY : Y ≅ 𝔸(PUnit.{u + 1}; X) :=
    hπ.isoIsPullback _ _ (AffineSpace.isPullback_map
      (n := PUnit.{u + 1}) (X ↘ Spec (CommRingCat.of k₀))).flip
  let j := aY.hom ≫ ProjectiveLine.affineChart X
  have hjq : j ≫ q = π := by
    dsimp only [j, q]
    rw [Category.assoc, ProjectiveLine.affineChart_over]
    exact hπ.isoIsPullback_hom_fst _ _ _
  have : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (aY.hom ≫ ProjectiveLine.affineChart X))
  have : IsClosedImmersion (i ≫ q) := by
    change IsClosedImmersion (ProjectiveLine.infinity X ≫ ProjectiveLine X ↘ X)
    rw [ProjectiveLine.infinity_over]
    infer_instance
  have : IsClosedImmersion i := .of_comp i q
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change (i ≫ q) ≫ (X ↘ Spec (CommRingCat.of k₀)) = _
    rw [ProjectiveLine.infinity_over, Category.id_comp]⟩
  have : j.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change j ≫ q ≫ (X ↘ Spec (CommRingCat.of k₀)) = _
    rw [← Category.assoc, hjq, comp_over]⟩
  let c : Compactification π :=
    { Z := ProjectiveLine X
      g := q
      i := j
      comm := hjq.symm
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  have : QuasiCompact j := c.quasiCompact_openImmersion inferInstance
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    change IsCompl (Set.range (ProjectiveLine.infinity X).base) (Set.range j.base)
    rw [ProjectiveLine.range_infinity, ← Scheme.Hom.coe_opensRange j]
    rw [show j.opensRange = (ProjectiveLine.affineChart X).opensRange from
      Scheme.Hom.opensRange_comp_of_isIso _ _]
    exact isCompl_compl.symm
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π (Spec (CommRingCat.of k₀))]
    infer_instance
  have : QuasiCompact (Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over π (Spec (CommRingCat.of k₀))]
    infer_instance
  have : LocallyOfFiniteType (ProjectiveLine X ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (q ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (ProjectiveLine X ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (q ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiSeparated (ProjectiveLine X ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiSeparated (q ≫ X ↘ Spec (CommRingCat.of k₀)))
  obtain ⟨ec⟩ := (nativeWeilCompactificationModelComparison k₀ l π).2.2 c
  let E := chartExtension (k₀ := k₀) (l := l) j
  let L := upperStar (k₀ := k₀) (l := l) q
  let R := derivedLowerStar (k₀ := k₀) (l := l) q
  let J := upperStar (k₀ := k₀) (l := l) j
  let I := upperStar (k₀ := k₀) (l := l) i
  let D := derivedLowerStar (k₀ := k₀) (l := l) i
  let ef : E ⋙ R ≅ derivedLowerShriek k₀ l π :=
    ((objectProperty k₀ l X).fullyFaithfulι.whiskeringRight _).preimageIso ec
  let ep : upperStar (k₀ := k₀) (l := l) π ≅ L ⋙ J :=
    (upperStarCongrIso hjq).symm ≪≫ upperStarCompIso j q
  let eF : upperStar π ⋙ derivedLowerShriek k₀ l π ≅ (L ⋙ J ⋙ E) ⋙ R :=
    Functor.isoWhiskerLeft (upperStar π) ef.symm ≪≫
      (Functor.associator (upperStar π) E R).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight ep E) R ≪≫
      Functor.isoWhiskerRight (Functor.associator L J E) R
  obtain ⟨α₀, hα₀⟩ := chart_localization (k₀ := k₀) (l := l) j i hij
  let α := eF.hom ≫ Functor.whiskerRight (Functor.whiskerLeft L α₀) R
  refine ⟨α, fun K ↦ ?_⟩
  let e : L ⋙ I ≅ 𝟭 _ :=
    (upperStarCompIso i q).symm ≪≫ upperStarCongrIso ProjectiveLine.infinity_over ≪≫
      upperStarIdIso X
  let adjq := upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) q
  let adji := upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) i
  let d := (adjq.comp adji).ofNatIsoLeft e
  let ei : D ⋙ R ≅ 𝟭 _ := Adjunction.rightAdjointUniq d Adjunction.id
  obtain ⟨w, hw⟩ := hα₀ (L.obj K)
  have hpush := R.map_distinguished _ hw
  apply transport_localization_triangle hpush (eF.app K) (Iso.refl _)
    ((ei.app (I.obj (L.obj K)) ≪≫ e.app K).symm)
  · change (eF.hom.app K ≫ R.map (α₀.app (L.obj K))) ≫ 𝟙 _ =
      eF.hom.app K ≫ R.map (α₀.app (L.obj K))
    exact Category.comp_id _
  · have hr : R.map (adji.unit.app (L.obj K)) ≫ ei.hom.app (I.obj (L.obj K)) ≫
        e.hom.app K = (projectiveLineRestriction X).app K := by
      have h := section_restriction_identity adjq adji e K
      change R.map (adji.unit.app (L.obj K)) ≫ ei.hom.app (I.obj (L.obj K)) = _ at h
      rw [← Category.assoc, h]
      simp only [projectiveLineRestriction, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
      erw [Category.id_comp]
      exact Category.assoc _ _ _
    change (projectiveLineRestriction X).app K ≫
      (e.inv.app K ≫ ei.inv.app (I.obj (L.obj K))) =
        𝟙 _ ≫ R.map (adji.unit.app (L.obj K))
    rw [← hr]
    simp only [Category.assoc, Category.id_comp]
    erw [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry.WeilComplex
