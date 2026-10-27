/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N9, B8
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom
import Sheaf.Paper.CondensedQcqsPushforwardContinuity
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Open extension preserves bounded-target internal-Hom continuity

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemmas 6.3.14(2), 6.8.12;
Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3 and its open-immersion argument
(blueprint: lem-sfb-rhom-continuity-open-extension).

Continuity is expressed on every cohomology sheaf. Exact filtered colimits identify
these maps with the cohomology of the evaluation-induced comparison formed by taking
termwise sheaf colimits of functorial complex representatives. In particular, no
ordinary categorical colimit of a diagram in the triangulated derived category is used.
The map `colimit.post` has components obtained by applying internal Hom and cohomology
to the original complex-colimit inclusions, fixing the comparison canonically.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

section ContinuityCalculus

universe v₁ v₂ v₃ w₁ w₂ w₃ vI wI

variable {C : Type w₁} {B : Type w₂} {E : Type w₃}
  [Category.{v₁} C] [Category.{v₂} B] [Category.{v₃} E]
  {I : Type wI} [Category.{vI} I]

private theorem isGE_iso [Abelian C] [HasDerivedCategory.{v₁} C]
    {X Y : DerivedCategory C} (e : X ≅ Y) (a : ℤ) (h : X.IsGE a) : Y.IsGE a := by
  have : DerivedCategory.TStructure.t.IsGE X a := h
  exact DerivedCategory.TStructure.t.isGE_of_iso e a

private theorem post_naturality [HasColimitsOfShape I C] [HasColimitsOfShape I B]
    (D : I ⥤ C) (F G : C ⥤ B) (η : F ⟶ G) :
    colimMap (Functor.whiskerLeft D η) ≫ colimit.post D G =
      colimit.post D F ≫ η.app (colimit D) := by
  apply colimit.hom_ext
  intro i
  simp only [ι_colimMap_assoc, Functor.whiskerLeft_app, colimit.ι_post,
    colimit.ι_post_assoc]
  exact (η.naturality (colimit.ι D i)).symm

private theorem post_iso [HasColimitsOfShape I C] [HasColimitsOfShape I B]
    (D : I ⥤ C) {F G : C ⥤ B} (e : F ≅ G) (h : IsIso (colimit.post D F)) :
    IsIso (colimit.post D G) := by
  have := h
  have he := post_naturality D F G e.hom
  have : IsIso (colimMap (Functor.whiskerLeft D e.hom) ≫ colimit.post D G) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (colimMap (Functor.whiskerLeft D e.hom)) _

private theorem post_diagram_naturality
    [HasColimitsOfShape I C] [HasColimitsOfShape I B]
    {D D' : I ⥤ C} (α : D ⟶ D') (F : C ⥤ B) :
    colimMap (Functor.whiskerRight α F) ≫ colimit.post D' F =
      colimit.post D F ≫ F.map (colimMap α) := by
  apply colimit.hom_ext
  intro i
  simp only [ι_colimMap_assoc, Functor.whiskerRight_app, colimit.ι_post,
    colimit.ι_post_assoc, ← F.map_comp, ι_colimMap]

private theorem quasiIso_colimit_map [Abelian C]
    [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
    {D D' : I ⥤ CochainComplex C ℤ} (α : D ⟶ D')
    (hα : ∀ i, QuasiIso (α.app i)) : QuasiIso (colimMap α) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor C (.up ℤ) q
  have hi (i : I) : IsIso ((Functor.whiskerRight α H).app i) := by
    have := hα i
    exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap (α.app i) q))
  have : IsIso (Functor.whiskerRight α H) := NatIso.isIso_of_isIso_app _
  have he := post_diagram_naturality α H
  have : IsIso (colimit.post D H ≫ H.map (colimMap α)) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_left (colimit.post D H) (H.map (colimMap α))

private theorem post_of_truncation [Abelian C] [HasDerivedCategory.{v₁} C]
    [HasColimitsOfShape I C] [HasExactColimitsOfShape I C]
    (D : I ⥤ CochainComplex C ℤ) (a : ℤ)
    (ha : ∀ i, (DerivedCategory.Q.obj (D.obj i)).IsGE a)
    (F : DerivedCategory C ⥤ B) [HasColimitsOfShape I B]
    (h : IsIso (AlgebraicGeometry.ProEtale.condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ F))) : IsIso (colimit.post D (DerivedCategory.Q ⋙ F)) := by
  let α := Functor.whiskerLeft D
    ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans C)
  have hα (i : I) : QuasiIso (α.app i) := by
    apply (CochainComplex.quasiIso_πTruncGE_iff _ a).2
    exact (DerivedCategory.isGE_Q_obj_iff _ a).1 (ha i)
  have : QuasiIso (colimMap α) := quasiIso_colimit_map α hα
  have : IsIso (DerivedCategory.Q.map (colimMap α)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  have he : colimit.post D (DerivedCategory.Q ⋙ F) ≫
      F.map (DerivedCategory.Q.map (colimMap α)) =
        AlgebraicGeometry.ProEtale.condensedContinuityComparison D a
          (DerivedCategory.Q ⋙ F) := by
    apply colimit.hom_ext
    intro i
    simp only [colimit.ι_post_assoc, Functor.comp_map, ← F.map_comp,
      ← DerivedCategory.Q.map_comp, ι_colimMap]
    simp only [AlgebraicGeometry.ProEtale.condensedContinuityComparison, colimit.ι_desc]
    rfl
  have := h
  have : IsIso (colimit.post D (DerivedCategory.Q ⋙ F) ≫
      F.map (DerivedCategory.Q.map (colimMap α))) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map (DerivedCategory.Q.map (colimMap α)))

private theorem model_post_quasiIso [Abelian C] [Abelian B]
    [HasDerivedCategory.{v₁} C] [HasDerivedCategory.{v₂} B]
    [HasColimitsOfShape I C] [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    (D : I ⥤ CochainComplex C ℤ) (L : CochainComplex C ℤ ⥤ CochainComplex B ℤ)
    (F : DerivedCategory C ⥤ DerivedCategory B)
    (e : DerivedCategory.Q ⋙ F ≅ L ⋙ DerivedCategory.Q)
    (h : ∀ q : ℤ, IsIso (colimit.post D
      (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q))) :
    QuasiIso (colimit.post D L) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor B (.up ℤ) q
  let ε : DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q ≅ L ⋙ H :=
    Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor B q) ≪≫
      Functor.isoWhiskerLeft L (DerivedCategory.homologyFunctorFactors B q)
  have hp := post_iso D ε (h q)
  have : IsIso (colimit.post (D ⋙ L) H ≫ H.map (colimit.post D L)) := by
    rw [colimit.post_post]
    exact hp
  exact IsIso.of_isIso_comp_left (colimit.post (D ⋙ L) H) (H.map (colimit.post D L))

private theorem post_comp_model [Abelian C] [Abelian B]
    [HasDerivedCategory.{v₁} C] [HasDerivedCategory.{v₂} B]
    [HasColimitsOfShape I C] [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    [HasColimitsOfShape I E]
    (D : I ⥤ CochainComplex C ℤ) (L : CochainComplex C ℤ ⥤ CochainComplex B ℤ)
    (F : DerivedCategory C ⥤ DerivedCategory B)
    (e : DerivedCategory.Q ⋙ F ≅ L ⋙ DerivedCategory.Q)
    (G : DerivedCategory B ⥤ E)
    (hF : ∀ q : ℤ, IsIso (colimit.post D
      (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q)))
    (hG : IsIso (colimit.post (D ⋙ L) (DerivedCategory.Q ⋙ G))) :
    IsIso (colimit.post D (DerivedCategory.Q ⋙ F ⋙ G)) := by
  have : QuasiIso (colimit.post D L) := model_post_quasiIso D L F e hF
  have : IsIso (DerivedCategory.Q.map (colimit.post D L)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  have := hG
  have h : IsIso (colimit.post D (L ⋙ DerivedCategory.Q ⋙ G)) := by
    rw [← colimit.post_post]
    dsimp only [Functor.comp_map]
    infer_instance
  exact post_iso D (Functor.isoWhiskerRight e G).symm h

private noncomputable def resolution_model_iso [Abelian C]
    [IsGrothendieckAbelian.{v₁} C] [HasDerivedCategory.{v₁} C]
    (L : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (H : HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory C (.up ℤ))
    (F : DerivedCategory C ⥤ DerivedCategory C)
    (α : H ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ F)
    (e : HomotopyCategory.quotient _ _ ⋙ H ≅ L ⋙ HomotopyCategory.quotient _ _)
    [IsIso (Functor.whiskerLeft
      (CochainComplex.kInjectiveResolutionFunctor.{v₁} C ⋙
        HomotopyCategory.quotient _ _) α)] :
    DerivedCategory.Q ⋙ F ≅
      CochainComplex.kInjectiveResolutionFunctor.{v₁} C ⋙ L ⋙ DerivedCategory.Q := by
  let R := CochainComplex.kInjectiveResolutionFunctor.{v₁} C
  let η := CochainComplex.toKInjectiveResolution.{v₁} C
  have : IsIso (Functor.whiskerRight η DerivedCategory.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{v₁} C M).2
  exact Functor.isoWhiskerRight (asIso (Functor.whiskerRight η DerivedCategory.Q)) F ≪≫
    Functor.isoWhiskerLeft R
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C).symm F) ≪≫
    (asIso (Functor.whiskerLeft (R ⋙ HomotopyCategory.quotient _ _) α)).symm ≪≫
    Functor.isoWhiskerLeft R (Functor.isoWhiskerRight e DerivedCategory.Qh) ≪≫
    Functor.isoWhiskerLeft (R ⋙ L) (DerivedCategory.quotientCompQhIso C)

end ContinuityCalculus

namespace AlgebraicGeometry.ProEtale.CondensedRing

private noncomputable def homModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (A : DerivedCategory (supportModules Λ X)) :
    CochainComplex (supportModules Λ X) ℤ ⥤ CochainComplex (supportModules Λ X) ℤ :=
  CochainComplex.kInjectiveResolutionFunctor.{u + 1} (supportModules Λ X) ⋙
    CochainComplex.internalHom (DerivedCategory.Qh.objPreimage A).as

set_option maxHeartbeats 800000 in
-- Comparing the concrete closed structures requires additional elaboration steps.
set_option synthInstance.maxSize 4096 in
private noncomputable def homModelIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (A : DerivedCategory (supportModules Λ X)) :
    DerivedCategory.Q ⋙ (derivedHom Λ X).obj (op A) ≅
      homModel Λ X A ⋙ DerivedCategory.Q := by
  let C := supportModules Λ X
  let P := DerivedCategory.Qh.objPreimage A
  have : IsIso (Functor.whiskerLeft
      (CochainComplex.kInjectiveResolutionFunctor.{u + 1} C ⋙
        HomotopyCategory.quotient _ _) (DerivedCategory.internalHomQhObjUnit P)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    dsimp
    infer_instance
  exact resolution_model_iso (CochainComplex.internalHom P.as)
    (HomotopyCategory.internalHom P) (DerivedCategory.internalHomQhObj P)
    (DerivedCategory.internalHomQhObjUnit P) (HomotopyCategory.quotientCompInternalHomIso P)

private theorem pushforward_isGE
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategory (supportModules Λ X))
    (a : ℤ) [K.IsGE a] : ((lowerStar Λ f).rightDerivedFunctor.obj K).IsGE a := by
  let Kp : DerivedCategory.Plus (supportModules Λ X) := ⟨K, ⟨a, inferInstance⟩⟩
  have : Kp.IsGE a := ⟨(show K.IsGE a from inferInstance).1⟩
  apply (DerivedCategory.isGE_iff _ a).2
  intro q hq
  exact ((lowerStar Λ f).isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    Kp a hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((lowerStar Λ f).rightDerivedFunctorPlusCompatibility.app Kp)).symm

attribute [local irreducible] homModel supportPullback openImmersionLowerShriek derivedHom
  Functor.mapDerivedCategory Functor.rightDerivedFunctor DerivedCategory.monoidalClosed
  CochainComplex.internalHom CochainComplex.kInjectiveResolutionFunctor

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 1600000 in
-- The concrete derived functors involve deeply nested module and monoidal structures.
set_option synthInstance.maxSize 4096 in
/-- Exact open extension preserves both bounded-target internal-Hom continuity and its
chosen uniform lower bound, without a constructibility hypothesis.

Source: Bhatt--Scholze, Lemmas 6.3.14(2), 6.8.12, refined using Hemo--Richarz--Scholbach,
Lemma 5.3(1) and the open case of its proof of (2)
(blueprint: lem-sfb-rhom-continuity-open-extension).

Proof:
1. Noetherianity makes the open immersion quasi-compact; an open immersion is
   quasi-separated. Realize its closed complement by the vanishing ideal sheaf.
2. The natural open internal-Hom formula identifies the functor in the conclusion
   with `Rv_* RHom(A,v^*(-))`. Exact pullback preserves colimits and lower bounds.
3. Choose the functorial K-injective replacement of complexes and then apply the
   cochain internal Hom from a representative of A. The derived internal-Hom
   comparison identifies this genuine complex functor with RHom(A,-).
4. Exact filtered colimits commute with cohomology. The assumed continuity thus
   makes the comparison for the complex model a quasi-isomorphism. Its values on
   the pulled-back diagram have the common lower bound c+d by the assumed bound.
5. Apply bounded-below qcqs pushforward continuity to this model diagram. Its
   truncation comparison agrees with the original comparison after the canonical
   quasi-isomorphism from the untruncated colimit. Composition and naturality of
   `colimit.post` give exactly the comparison of the statement.
6. Exact pullback preserves the input lower bound c; the hypothesis then gives
   c+d for internal Hom. The right-derived direct image preserves that bound by
   negative derived-functor vanishing and bounded-below/total compatibility. -/
theorem openImmersionLowerShriek_rhom_continuity
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {V T : Scheme.{u}} (v : V ⟶ T) [IsOpenImmersion v] [TopologicalSpace.NoetherianSpace T]
    (A : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) (condensedRingObj Λ.X V)))
    (d : ℤ)
    (hcontinuity : ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (N : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ.X V)) ℤ) (c : ℤ),
      (∀ i : I, (DerivedCategory.Q.obj (N.obj i)).IsGE c) → ∀ q : ℤ,
      IsIso (colimit.post N
        (DerivedCategory.Q ⋙ (derivedHom Λ.X V).obj (op A) ⋙
          DerivedCategory.homologyFunctor _ q)))
    (hbound : ∀ (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ.X V))) (c : ℤ),
      N.IsGE c → (((derivedHom Λ.X V).obj (op A)).obj N).IsGE (c + d)) :
    (∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
      (N : I ⥤ CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ.X T)) ℤ) (c : ℤ),
      (∀ i : I, (DerivedCategory.Q.obj (N.obj i)).IsGE c) → ∀ q : ℤ,
      IsIso (colimit.post N
        (DerivedCategory.Q ⋙
          (derivedHom Λ.X T).obj (op ((openImmersionLowerShriek Λ.X v).mapDerivedCategory.obj A))
          ⋙ DerivedCategory.homologyFunctor _ q))) ∧
    (∀ (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ.X T))) (c : ℤ),
      N.IsGE c →
        (((derivedHom Λ.X T).obj
          (op ((openImmersionLowerShriek Λ.X v).mapDerivedCategory.obj A))).obj N).IsGE
            (c + d)) := by
  let R := supportPullback Λ.X v
  let H := (derivedHom Λ.X V).obj (op A)
  let G := (lowerStar Λ.X v).rightDerivedFunctor
  have : TopologicalSpace.NoetherianSpace V :=
    v.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have : QuasiCompact v := inferInstance
  let Z : TopologicalSpace.Closeds T :=
    ⟨(Set.range v.base)ᶜ, v.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  have hij : Set.range J.subschemeι.base = (Set.range v.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  obtain ⟨p, o, k, hp, ho, hk, hon, hkn⟩ :=
    openClosedInternalHomFormulas Λ.X J.subschemeι v hij
  let F := (derivedHom Λ.X T).obj
    (op ((openImmersionLowerShriek Λ.X v).mapDerivedCategory.obj A))
  let e : F ≅ R.mapDerivedCategory ⋙ H ⋙ G :=
    NatIso.ofComponents (fun N ↦ o A N) (by
      intro N N' b
      have h := hon A A N N' (𝟙 A) b
      rw [(openImmersionLowerShriek Λ.X v).mapDerivedCategory.map_id A, op_id,
        (derivedHom Λ.X T).map_id _, NatTrans.id_app, Category.id_comp,
        op_id, (derivedHom Λ.X V).map_id _, NatTrans.id_app, Category.id_comp] at h
      exact h)
  constructor
  · intro I _ _ N c hN q
    have : HasColimitsOfShape I (supportModules Λ.X V) := inferInstance
    have : HasColimitsOfShape I (supportModules Λ.X T) := inferInstance
    have : HasColimitsOfShape I (CochainComplex (supportModules Λ.X V) ℤ) := inferInstance
    have : HasColimitsOfShape I (CochainComplex (supportModules Λ.X T) ℤ) := inferInstance
    let R' := R.mapHomologicalComplex (.up ℤ)
    let L := R' ⋙ homModel Λ.X V A
    have : HasColimit (N ⋙ L) :=
      HasColimitsOfShape.has_colimit (C := CochainComplex (supportModules Λ.X V) ℤ) _
    let ε : DerivedCategory.Q ⋙ (R.mapDerivedCategory ⋙ H) ≅ L ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerRight R.mapDerivedCategoryFactors H ≪≫
        Functor.isoWhiskerLeft R' (homModelIso Λ.X V A)
    have hR (i : I) : (DerivedCategory.Q.obj ((N ⋙ R').obj i)).IsGE c := by
      have := hN i
      exact isGE_iso (R.mapDerivedCategoryFactors.app (N.obj i)) c
        (R.isGE_mapDerivedCategory_obj (DerivedCategory.Q.obj (N.obj i)) c)
    have : PreservesColimitsOfSize.{u + 1, u + 1} R :=
      (supportPullbackAdjunction Λ.X v).leftAdjoint_preservesColimits
    have : PreservesColimitsOfShape I R' := by
      dsimp only [R']
      infer_instance
    have hF (r : ℤ) : IsIso (colimit.post N
        (DerivedCategory.Q ⋙ (R.mapDerivedCategory ⋙ H) ⋙
          DerivedCategory.homologyFunctor _ r)) := by
      have := hcontinuity I (N ⋙ R') c hR r
      have hpost : IsIso (colimit.post N
          (R' ⋙ DerivedCategory.Q ⋙ H ⋙ DerivedCategory.homologyFunctor _ r)) := by
        rw [← colimit.post_post]
        dsimp only [Functor.comp_map]
        infer_instance
      exact post_iso N
        (Functor.isoWhiskerRight R.mapDerivedCategoryFactors
          (H ⋙ DerivedCategory.homologyFunctor _ r)).symm hpost
    have hL (i : I) : (DerivedCategory.Q.obj ((N ⋙ L).obj i)).IsGE (c + d) := by
      exact isGE_iso ((homModelIso Λ.X V A).app ((N ⋙ R').obj i)) (c + d)
        (hbound _ c (hR i))
    have hG : IsIso (colimit.post (N ⋙ L)
        (DerivedCategory.Q ⋙ G ⋙ DerivedCategory.homologyFunctor _ q)) := by
      apply post_of_truncation (N ⋙ L) (c + d) hL
        (G ⋙ DerivedCategory.homologyFunctor _ q)
      exact condensed_qcqs_pushforward_continuity Λ.X v (N ⋙ L) (c + d)
        (fun i n hn ↦ ((DerivedCategory.isGE_iff _ _).1 (hL i) n hn).of_iso
          ((DerivedCategory.homologyFunctorFactors _ n).app ((N ⋙ L).obj i)).symm) q
    have hpost := post_comp_model N L (R.mapDerivedCategory ⋙ H) ε
      (G ⋙ DerivedCategory.homologyFunctor _ q) hF hG
    exact post_iso N
      (Functor.isoWhiskerLeft DerivedCategory.Q
        (Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor _ q))).symm hpost
  · intro N c hN
    have : N.IsGE c := hN
    have hR := R.isGE_mapDerivedCategory_obj N c
    have hH := hbound _ c hR
    have : (H.obj (R.mapDerivedCategory.obj N)).IsGE (c + d) := hH
    exact isGE_iso (e.app N).symm (c + d)
      (pushforward_isGE Λ.X v (H.obj (R.mapDerivedCategory.obj N)) (c + d))

end AlgebraicGeometry.ProEtale.CondensedRing
