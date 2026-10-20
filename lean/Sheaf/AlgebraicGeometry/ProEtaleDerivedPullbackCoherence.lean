/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Associativity of canonical finite-coefficient derived pro-etale pullback comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0D6D,
`lemma-derived-pullback-composition`, its K-flat representative computation and the
associativity of inverse-image comparisons
(blueprint: lem-trf-derived-pullback-coherence).
-/

@[expose] public section

set_option autoImplicit false
-- Replaying the sectionwise transport tactics for linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] proEtaleRingModuleAdjunctionNormalized
  proEtaleRingModuleUnitSection proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors
  CochainComplex.IsAcyclicTensorKFlat SheafOfModules.IsFlatOnSite
  proEtaleRingModulePullback proEtaleConstantRingComparison
  proEtaleCanonicalPullbackComposition proEtaleConstantRingPullbackComposition
  proEtaleRingDirectImageMap

-- All data selected below are fixed by the existing normalization: the units fix the
-- adjunctions, the section formula fixes d, conjugation fixes a, and degree maps fix b.
-- The structure only exposes these determined witnesses from the existing theorem.
private structure ComparisonWitnesses
    {AK AH AC D A B : Type*}
    (NK : AK → Prop) (NH : AH → Prop) (NC : AC → Prop)
    (HD : D → Prop) (HA : AK → AH → AC → D → A → Prop)
    (HB : A → B → Prop) (HC : B → Prop) where
  adjk : AK
  adjh : AH
  adjc : AC
  nk : NK adjk
  nh : NH adjh
  nc : NC adjc
  d : D
  hd : HD d
  a : A
  ha : HA adjk adjh adjc d a
  b : B
  hb : HB a b
  hc : HC b

private theorem ComparisonWitnesses.nonempty
    {AK AH AC D A B : Type*}
    (NK : AK → Prop) (NH : AH → Prop) (NC : AC → Prop)
    (HD : D → Prop) (HA : AK → AH → AC → D → A → Prop)
    (HB : A → B → Prop) (HC : B → Prop)
    (h : ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC b) :
    Nonempty (ComparisonWitnesses NK NH NC HD HA HB HC) := by
  obtain ⟨ak, ah, ac, nk, nh, nc, d, hd, a, ha, b, hb, hc⟩ := h
  exact ⟨⟨ak, ah, ac, nk, nh, nc, d, hd, a, ha, b, hb, hc⟩⟩

private theorem ComparisonWitnesses.to_exists
    {AK AH AC D A B : Type*}
    {NK : AK → Prop} {NH : AH → Prop} {NC : AC → Prop}
    {HD : D → Prop} {HA : AK → AH → AC → D → A → Prop}
    {HB : A → B → Prop} {HC : B → Prop}
    (p : ComparisonWitnesses NK NH NC HD HA HB HC) :
    ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC b :=
  ⟨p.adjk, p.adjh, p.adjc, p.nk, p.nh, p.nc, p.d, p.hd,
    p.a, p.ha, p.b, p.hb, p.hc⟩

private abbrev UniqueData
    {I AK AH AC D A B : Type*}
    {NK : AK → Prop} {NH : AH → Prop} {NC : AC → Prop}
    {HD : D → Prop} {HA : AK → AH → AC → D → A → Prop}
    {HB : A → B → Prop} {HC : I → B → Prop}
    (_t : ∃! i, ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC i b) (i : I) :=
  ComparisonWitnesses NK NH NC HD HA HB (HC i)

private theorem UniqueData.exists
    {I AK AH AC D A B : Type*}
    {NK : AK → Prop} {NH : AH → Prop} {NC : AC → Prop}
    {HD : D → Prop} {HA : AK → AH → AC → D → A → Prop}
    {HB : A → B → Prop} {HC : I → B → Prop}
    (t : ∃! i, ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC i b) :
    Nonempty (UniqueData t (Classical.choose t.exists)) :=
  ComparisonWitnesses.nonempty _ _ _ _ _ _ _ (Classical.choose_spec t.exists)

private theorem UniqueData.unique_of_formula
    {I AK AH AC D A B : Type*}
    {NK : AK → Prop} {NH : AH → Prop} {NC : AC → Prop}
    {HD : D → Prop} {HA : AK → AH → AC → D → A → Prop}
    {HB : A → B → Prop} {HC : I → B → Prop}
    (t : ∃! i, ∃ ak ah ac, NK ak ∧ NH ah ∧ NC ac ∧
      ∃ d, HD d ∧ ∃ a, HA ak ah ac d a ∧ ∃ b, HB a b ∧ HC i b)
    {i j : I} (di : UniqueData t i)
    (h : ∀ b, HB di.a b → HC i b → HC j b) : i = j := by
  apply t.unique di.to_exists
  exact ⟨di.adjk, di.adjh, di.adjc, di.nk, di.nh, di.nc, di.d, di.hd,
    di.a, di.ha, di.b, di.hb, h di.b di.hb di.hc⟩

private abbrev PullbackData
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (c : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj RV ≅ RZ)
    (hc : proEtaleRingCompositeCoefficients h k RV RW RZ ck ch = c)
    (comparison : proEtaleRingDerivedPullback (h ≫ k) RV RZ c ≅
      proEtaleRingDerivedPullback k RV RW ck ⋙ proEtaleRingDerivedPullback h RW RZ ch) :=
  UniqueData (proEtaleCanonicalPullbackComposition_existsUnique
    h k RV RW RZ ck ch c hc.symm) comparison

private theorem pullbackData_exists
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    : Nonempty (PullbackData h k RV RW RZ ck ch
      (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)
      rfl (proEtaleCanonicalPullbackComposition h k RV RW RZ ck ch)) := by
  unfold proEtaleCanonicalPullbackComposition
  exact UniqueData.exists (proEtaleCanonicalPullbackComposition_existsUnique h k RV RW RZ
    ck ch (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch) rfl)

private theorem pullbackData_transport
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (c : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj RV ≅ RZ)
    (hc : proEtaleRingCompositeCoefficients h k RV RW RZ ck ch = c) :
    Nonempty (PullbackData h k RV RW RZ ck ch c hc
      (eqToIso (congrArg (proEtaleRingDerivedPullback (h ≫ k) RV RZ) hc.symm) ≪≫
        proEtaleCanonicalPullbackComposition h k RV RW RZ ck ch)) := by
  subst c
  simpa only [eqToIso_refl, Iso.refl_trans] using
    pullbackData_exists h k RV RW RZ ck ch

@[irreducible] private noncomputable def constantData
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : Type u) [CommRing A] :
    PullbackData h k (proEtaleConstantRing V A) (proEtaleConstantRing W A)
      (proEtaleConstantRing Z A) (proEtaleConstantRingComparison k A)
      (proEtaleConstantRingComparison h A) (proEtaleConstantRingComparison (h ≫ k) A)
      (proEtaleConstantRingCompositeCoefficients_eq h k A)
      (proEtaleConstantRingPullbackComposition h k A).symm := by
  apply Classical.choice
  have he : (proEtaleConstantRingPullbackComposition h k A).symm =
      eqToIso (congrArg
        (proEtaleRingDerivedPullback (h ≫ k) (proEtaleConstantRing V A)
          (proEtaleConstantRing Z A))
        (proEtaleConstantRingCompositeCoefficients_eq h k A).symm) ≪≫
          proEtaleCanonicalPullbackComposition h k (proEtaleConstantRing V A)
            (proEtaleConstantRing W A) (proEtaleConstantRing Z A)
            (proEtaleConstantRingComparison k A) (proEtaleConstantRingComparison h A) := by
    unfold proEtaleConstantRingPullbackComposition
    rfl
  rw [he]
  exact pullbackData_transport h k
    (proEtaleConstantRing V A) (proEtaleConstantRing W A) (proEtaleConstantRing Z A)
    (proEtaleConstantRingComparison k A) (proEtaleConstantRingComparison h A)
    (proEtaleConstantRingComparison (h ≫ k) A)
    (proEtaleConstantRingCompositeCoefficients_eq h k A)

@[irreducible] private noncomputable def ordinaryComp
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A (h ≫ k) ≅
      proEtaleConstantRingPullback A k ⋙ proEtaleConstantRingPullback A h :=
  (constantData h k A).a

@[irreducible] private noncomputable def directComp
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    proEtaleConstantRingPushforward A h ⋙ proEtaleConstantRingPushforward A k ≅
      proEtaleConstantRingPushforward A (h ≫ k) :=
  (constantData h k A).d

private theorem mate_eq
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    {RF : D ⥤ C} {RG : E ⥤ D} {RH : E ⥤ C}
    (ak ak' : F ⊣ RF) (ah ah' : G ⊣ RG) (ac ac' : H ⊣ RH)
    (hk : ak = ak') (hh : ah = ah') (hc : ac = ac')
    (a : H ≅ F ⋙ G) (d : RG ⋙ RF ≅ RH)
    (ha : conjugateIsoEquiv (ak.comp ah) ac a = d) :
    a = (Adjunction.leftAdjointCompIso ak' ah' ac' d).symm := by
  subst ak'
  subst ah'
  subst ac'
  apply (conjugateIsoEquiv (ak.comp ah) ac).injective
  rw [ha]
  exact ((conjugateIsoEquiv (ak.comp ah) ac).apply_symm_apply d).symm

@[irreducible] private noncomputable def normalizedAdj
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A] :
    proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f :=
  (constantData f (𝟙 Y) A).adjh

private theorem normalizedAdj_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (adj : proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f)
    (hn : proEtaleRingModuleAdjunctionNormalized f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) adj) :
    adj = normalizedAdj f A := by
  unfold normalizedAdj
  unfold proEtaleRingModuleAdjunctionNormalized at hn
  have nh := (constantData f (𝟙 Y) A).nh
  unfold proEtaleRingModuleAdjunctionNormalized at nh
  apply Adjunction.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  exact (hn M U.unop m).trans (nh M U.unop m).symm

private theorem ordinaryComp_eq
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    ordinaryComp h k A =
      (Adjunction.leftAdjointCompIso (normalizedAdj k A) (normalizedAdj h A)
        (normalizedAdj (h ≫ k) A) (directComp h k A)).symm := by
  unfold ordinaryComp directComp
  exact mate_eq _ _ _ _ _ _
    (normalizedAdj_eq k A _ (constantData h k A).nk)
    (normalizedAdj_eq h A _ (constantData h k A).nh)
    (normalizedAdj_eq (h ≫ k) A _ (constantData h k A).nc)
    (constantData h k A).a (constantData h k A).d (constantData h k A).ha

private theorem derivedFormula_components
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a : H ≅ F ⋙ G)
    (b : H.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ))
    (hb : ∀ (K : CochainComplex C ℤ) (n : ℤ), (b.hom.app K).f n = a.hom.app (K.X n))
    (K : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (b.hom.app K) =
      (Functor.mapDerivedCategoryNatIso a ≪≫
        Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have hbK : b.hom.app K =
      (NatTrans.mapHomologicalComplex a.hom (ComplexShape.up ℤ)).app K := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hb K n
  rw [hbK]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors]
  exact (Functor.mapDerivedCategoryNatIso_fac a K).symm

private theorem pullbackData_comparison
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ)
    (c : (proEtaleSheafInverseImage (h ≫ k) CommRingCat.{u + 1}).obj RV ≅ RZ)
    (hc : proEtaleRingCompositeCoefficients h k RV RW RZ ck ch = c)
    (comparison : proEtaleRingDerivedPullback (h ≫ k) RV RZ c ≅
      proEtaleRingDerivedPullback k RV RW ck ⋙ proEtaleRingDerivedPullback h RW RZ ch)
    (D : PullbackData h k RV RW RZ ck ch c hc comparison) :
    comparison = Functor.mapDerivedCategoryNatIso D.a ≪≫
      Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback k RV RW ck)
        (proEtaleRingModulePullback h RW RZ ch) := by
  apply UniqueData.unique_of_formula (proEtaleCanonicalPullbackComposition_existsUnique
    h k RV RW RZ ck ch c hc.symm) D
  intro b hb hD K hK hflat
  refine ⟨(hD K hK hflat).1, (hD K hK hflat).2.1, ?_⟩
  unfold proEtaleRingDerivedPullbackFactors
  exact derivedFormula_components (proEtaleRingModulePullback k RV RW ck)
    (proEtaleRingModulePullback h RW RZ ch) (proEtaleRingModulePullback (h ≫ k) RV RZ c)
    D.a b hb K

private theorem constantComparison_eq
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A] :
    (proEtaleConstantRingPullbackComposition h k A).symm =
      Functor.mapDerivedCategoryNatIso (ordinaryComp h k A) ≪≫
        Functor.mapDerivedCategoryCompIso (proEtaleConstantRingPullback A k)
          (proEtaleConstantRingPullback A h) := by
  unfold ordinaryComp
  exact pullbackData_comparison h k _ _ _ _ _ _ _ _ (constantData h k A)

private theorem directImage_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) (A : Type u) [CommRing A]
    (N : proEtaleRingModules X (proEtaleConstantRing X A)) (U : Y.ProEt)
    (m : ((proEtaleConstantRingPushforward A f).obj N).val.obj (Opposite.op U)) :
    ((eqToIso (congrArg (proEtaleConstantRingPushforward A) e)).hom.app N).val.app
        (Opposite.op U) m =
      N.val.map (eqToHom (congrArg (fun t ↦ (proEtaleBaseChange t).obj U) e.symm)).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

private theorem pasting_transport
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (e : fg = f ≫ g) (U : P.Over Q Z) :
    (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g fg e).hom.app U =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U) e) ≫
        (MorphismProperty.Over.pullbackComp (P := P) (Q := Q) f g).hom.app U := by
  cases e
  simp

private theorem site_pasting
    {C : Type*} [Category C] [HasPullbacks C] {P Q : MorphismProperty C}
    [P.IsStableUnderBaseChange] [Q.IsMultiplicative] [Q.RespectsIso]
    [Q.IsStableUnderBaseChange]
    {X Y Z W : C} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X) (U : P.Over Q X) :
    (MorphismProperty.Over.pullbackComp j (h ≫ k)).hom.app U ≫
        (MorphismProperty.Over.pullback P Q j).map
          ((MorphismProperty.Over.pullbackComp h k).hom.app U) =
      eqToHom (congrArg (fun t ↦ (MorphismProperty.Over.pullback P Q t).obj U)
        (Category.assoc j h k).symm) ≫
        (MorphismProperty.Over.pullbackComp (j ≫ h) k).hom.app U ≫
        (MorphismProperty.Over.pullbackComp j h).hom.app
          ((MorphismProperty.Over.pullback P Q k).obj U) := by
  have hp := NatTrans.congr_app (congrArg Iso.hom
    (MorphismProperty.Over.pullbackComp_assoc (P := P) (Q := Q) j h k)) U
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hp
  rw [pasting_transport (j ≫ h) k (j ≫ h ≫ k) (Category.assoc j h k).symm U] at hp
  simpa only [Category.assoc] using hp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem directComp_hom_apply
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) (A : Type u) [CommRing A]
    (N : proEtaleRingModules Z (proEtaleConstantRing Z A)) (U : V.ProEt)
    (m : ((proEtaleConstantRingPushforward A h ⋙
      proEtaleConstantRingPushforward A k).obj N).val.obj (Opposite.op U)) :
    ((directComp h k A).hom.app N).val.app (Opposite.op U) m =
      N.val.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U).op m := by
  unfold directComp
  exact (constantData h k A).hd N U m

private theorem directImage_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    {N N' : proEtaleRingModules X (proEtaleConstantRing X A)} (a : N ⟶ N') (U : Y.ProEt)
    (m : ((proEtaleConstantRingPushforward A f).obj N).val.obj (Opposite.op U)) :
    (((proEtaleConstantRingPushforward A f).map a).val.app (Opposite.op U)) m =
      a.val.app (Opposite.op ((proEtaleBaseChange f).obj U)) m := rfl

private theorem directImage_obj_map_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (N : proEtaleRingModules X (proEtaleConstantRing X A))
    {U V : Y.ProEt} (a : U ⟶ V)
    (m : ((proEtaleConstantRingPushforward A f).obj N).val.obj (Opposite.op V)) :
    (((proEtaleConstantRingPushforward A f).obj N).val.map a.op) m =
      N.val.map ((proEtaleBaseChange f).map a).op m := rfl

private theorem restriction_pasting
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat} (N : PresheafOfModules R)
    {U V T U' V' : C} (a : U ⟶ V) (b : V ⟶ T)
    (c : U ⟶ U') (d : U' ⟶ V') (e : V' ⟶ T)
    (h : a ≫ b = c ≫ d ≫ e) (m : N.obj (Opposite.op T)) :
    N.map a.op (N.map b.op m) = N.map c.op (N.map d.op (N.map e.op m)) := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp,
    ← PresheafOfModules.map_comp_apply, ← op_comp]
  rw [h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem directImage_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (A : Type u) [CommRing A] :
    Functor.isoWhiskerLeft (proEtaleConstantRingPushforward A j) (directComp h k A) ≪≫
        (directComp j (h ≫ k) A) =
      (Functor.associator (proEtaleConstantRingPushforward A j)
          (proEtaleConstantRingPushforward A h)
          (proEtaleConstantRingPushforward A k)).symm ≪≫
        Functor.isoWhiskerRight (directComp j h A)
          (proEtaleConstantRingPushforward A k) ≪≫
        (directComp (j ≫ h) k A) ≪≫
        eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.assoc j h k)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  cases U using Opposite.rec
  rename_i U
  ext m
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [directImage_map_apply k A ((directComp j h A).hom.app N) U]
  erw [directComp_hom_apply j h A N ((proEtaleBaseChange k).obj U)]
  erw [directComp_hom_apply (j ≫ h) k A N U]
  conv_rhs => erw [directImage_transport (Category.assoc j h k) A N U]
  conv_lhs => erw [directComp_hom_apply h k A
    ((proEtaleConstantRingPushforward A j).obj N) U m]
  conv_lhs => erw [directComp_hom_apply j (h ≫ k) A N U]
  conv_lhs => erw [directImage_obj_map_apply j A N
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).hom.app U)]
  exact restriction_pasting N.val _ _ _ _ _
    (site_pasting (P := @WeaklyEtale) (Q := ⊤) j h k U) m

private theorem mate_transport
    {C D E I : Type*} [Category C] [Category D] [Category E]
    (L : I → C ⥤ E) (R : I → E ⥤ C) (adj : ∀ i, L i ⊣ R i)
    {F : C ⥤ D} {G : D ⥤ E} {F' : D ⥤ C} {G' : E ⥤ D}
    (aF : F ⊣ F') (aG : G ⊣ G') {i i' : I} (e : i = i')
    (d : G' ⋙ F' ≅ R i) :
    Adjunction.leftAdjointCompIso aF aG (adj i')
        (d ≪≫ eqToIso (congrArg R e)) =
      Adjunction.leftAdjointCompIso aF aG (adj i) d ≪≫ eqToIso (congrArg L e) := by
  cases e
  simp

private theorem ordinary_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (A : Type u) [CommRing A] (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (ordinaryComp j (h ≫ k) A).hom.app M ≫
        (proEtaleConstantRingPullback A j).map ((ordinaryComp h k A).hom.app M) =
      (eqToIso (congrArg (proEtaleConstantRingPullback A)
        (Category.assoc j h k).symm)).hom.app M ≫
        (ordinaryComp (j ≫ h) k A).hom.app M ≫
        (ordinaryComp j h A).hom.app ((proEtaleConstantRingPullback A k).obj M) := by
  have hh := Adjunction.leftAdjointCompIso_assoc
    (normalizedAdj k A) (normalizedAdj h A) (normalizedAdj j A)
    (normalizedAdj (h ≫ k) A) (normalizedAdj (j ≫ h) A)
    (normalizedAdj (j ≫ h ≫ k) A)
    (directComp h k A) (directComp j h A)
    ((directComp (j ≫ h) k A) ≪≫
      eqToIso (congrArg (proEtaleConstantRingPushforward A) (Category.assoc j h k)))
    (directComp j (h ≫ k) A) (directImage_coherence j h k A)
  have ht := mate_transport (proEtaleConstantRingPullback A)
    (proEtaleConstantRingPushforward A) (fun f ↦ normalizedAdj f A)
    (normalizedAdj k A) (normalizedAdj (j ≫ h) A) (Category.assoc j h k)
    (directComp (j ≫ h) k A)
  rw [ht] at hh
  have hi := NatTrans.congr_app (congrArg Iso.inv hh) M
  simpa only [ordinaryComp_eq, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id, Category.assoc, eqToIso.inv, eqToIso.hom]
    using hi.symm

private theorem descend_coherence
    {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory B]
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ B)
    (F02 : C ⥤ E) (F13 : D ⥤ B) (F03 F03' : C ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [F02.Additive] [F13.Additive]
    [F03.Additive] [F03'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F02] [PreservesFiniteColimits F02]
    [PreservesFiniteLimits F13] [PreservesFiniteColimits F13]
    [PreservesFiniteLimits F03] [PreservesFiniteColimits F03]
    [PreservesFiniteLimits F03'] [PreservesFiniteColimits F03']
    (a02 : F02 ≅ F ⋙ G) (a13 : F13 ≅ G ⋙ H)
    (a0 : F03 ≅ F02 ⋙ H) (a1 : F03' ≅ F ⋙ F13) (e : F03 ≅ F03')
    (ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13) :
    (Functor.mapDerivedCategoryNatIso a0).hom ≫
        (Functor.mapDerivedCategoryCompIso F02 H).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso a02).hom
          H.mapDerivedCategory ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F G).hom
          H.mapDerivedCategory =
      (Functor.mapDerivedCategoryNatIso e).hom ≫
        (Functor.mapDerivedCategoryNatIso a1).hom ≫
        (Functor.mapDerivedCategoryCompIso F F13).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryNatIso a13).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory (Functor.mapDerivedCategoryCompIso G H).hom := by
  have hd := congrArg (fun t ↦ (Functor.mapDerivedCategoryNatIso t).hom) ho
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hd
  have hR := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a02 H
  have hL := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F a13
  have hC := Functor.mapDerivedCategoryCompIso_assoc F G H
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F02 H).hom,
    ← hR, Category.assoc, ← hC]
  have ht := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).hom ≫
    Functor.whiskerLeft F.mapDerivedCategory
      (Functor.mapDerivedCategoryCompIso G H).hom) hd
  calc
    _ = ((Functor.mapDerivedCategoryNatIso e).hom ≫
          (Functor.mapDerivedCategoryNatIso a1).hom ≫
          (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F a13)).hom) ≫
        (Functor.mapDerivedCategoryCompIso F (G ⋙ H)).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryCompIso G H).hom := by
            simpa only [Category.assoc] using ht
    _ = _ := by
      simp only [Category.assoc]
      rw [← Category.assoc (Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft F a13)).hom, hL]
      simp only [Category.assoc]


private theorem derived_transport
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) (A : Type u) [CommRing A] :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (proEtaleConstantRingPullback A) e))).hom =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

/-- Canonical derived pullback comparisons for three scheme morphisms are associative.
The inverse of `proEtaleConstantRingPullbackComposition` is the comparison `c` in the
node: the selected `proEtaleCanonicalPullbackComposition`, transported along the equality
between composite and canonical constant-section coefficient identifications. Thus its
termwise K-flat normalization is retained. The displayed transport identifies the two
parenthesizations of the triple scheme morphism; the functor associator has identity
components, so the target objects in the two paths agree definitionally.
Source: Stacks Project, Tag 0D6D and Modules on Sites, Tag 03D8
(blueprint: lem-trf-derived-pullback-coherence).
Proof: (1) Apply `lem-trf-constant-coefficient-composition` to all four pairs
(j,h), (h,k), (j,hk), and (hj,k). The canonical coefficient identification of each
composite is therefore the one required by the composition lemma, even on an empty
source (`prop-weil-pbc-proetale-constant-ring-map`).
(2) Construct the ordinary direct-image comparisons by restriction along canonical
fibre-product pasting isomorphisms (`def-pc-fibre-product` and
`def-weil-pbc-proetale-operations`). The two triple expansions preserve the same
projections and agree by the fibre-product universal property. Their scalar actions
agree by step (1), giving the right-adjoint coherence equation.
(3) Conjugate these comparisons under the normalized module adjunctions, using
`def-weil-pbc-composite-adjunction` and `lem-weil-pbc-conjugate-iso-unit-equation`.
The unit equation characterizes the ordinary comparison, whose tensor formula sends
m tensor r to (m tensor 1) tensor r; balancing gives its inverse.
(4) Apply `lem-trf-adjoint-composition-coherence` to the six adjunctions and invert
its equality. This gives the ordinary pullback comparison cocycle, with associator.
(5) Resolve M by a K-flat complex P with flat terms (`lem-pc-kflat-resolution`).
Successive pullbacks remain K-flat with flat terms by
`lem-weil-pbc-ringed-pullback-preserves-kflat`. The normalization in
`lem-weil-pbc-proetale-derived-pullback-composition` identifies each derived comparison
with its termwise ordinary comparison. Apply step (4) degreewise and localize to obtain
the equality on Q(P); naturality makes these degree maps complex maps.
(6) Both paths are natural in M. Apply naturality to the resolution isomorphism
Q(P) to M and cancel its image under the triple pullback to obtain the claimed equality.
No boundedness or flatness hypothesis on the scheme morphisms is used. -/
theorem proEtaleConstantRingDerivedPullback_composition_coherence
    {X Y Z W : Scheme.{u}} (j : W ⟶ Z) (h : Z ⟶ Y) (k : Y ⟶ X)
    (A : Type u) [CommRing A] [Finite A] (M : proEtaleDerivedCategory X A) :
    (proEtaleConstantRingPullbackComposition j (h ≫ k) A).inv.app M ≫
        (proEtaleConstantRingDerivedPullback A j).map
          ((proEtaleConstantRingPullbackComposition h k A).inv.app M) =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
        (Category.assoc j h k).symm)).hom.app M ≫
        (proEtaleConstantRingPullbackComposition (j ≫ h) k A).inv.app M ≫
        (proEtaleConstantRingPullbackComposition j h A).inv.app
          ((proEtaleConstantRingDerivedPullback A k).obj M) := by
  let F := proEtaleConstantRingPullback A k
  let G := proEtaleConstantRingPullback A h
  let H := proEtaleConstantRingPullback A j
  let F02 := proEtaleConstantRingPullback A (h ≫ k)
  let F13 := proEtaleConstantRingPullback A (j ≫ h)
  let a02 := (ordinaryComp h k A)
  let a13 := (ordinaryComp j h A)
  let a0 := (ordinaryComp j (h ≫ k) A)
  let a1 := (ordinaryComp (j ≫ h) k A)
  let e := eqToIso (congrArg (proEtaleConstantRingPullback A)
    (Category.assoc j h k).symm)
  have ho : a0 ≪≫ Functor.isoWhiskerRight a02 H =
      e ≪≫ a1 ≪≫ Functor.isoWhiskerLeft F a13 := by
    apply Iso.ext
    apply NatTrans.ext
    funext N
    exact ordinary_coherence j h k A N
  have hh := descend_coherence F G H F02 F13
    (proEtaleConstantRingPullback A (j ≫ h ≫ k))
    (proEtaleConstantRingPullback A ((j ≫ h) ≫ k)) a02 a13 a0 a1 e ho
  have hm := NatTrans.congr_app hh M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hm
  have he := congrArg (fun t ↦ t.app M)
    (derived_transport (Category.assoc j h k).symm A)
  change (Functor.mapDerivedCategoryNatIso e).hom.app M = _ at he
  rw [he] at hm
  change ((proEtaleConstantRingPullbackComposition j (h ≫ k) A).symm).hom.app M ≫
      (proEtaleConstantRingDerivedPullback A j).map
        (((proEtaleConstantRingPullbackComposition h k A).symm).hom.app M) =
    (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A)
      (Category.assoc j h k).symm)).hom.app M ≫
      ((proEtaleConstantRingPullbackComposition (j ≫ h) k A).symm).hom.app M ≫
      ((proEtaleConstantRingPullbackComposition j h A).symm).hom.app
        ((proEtaleConstantRingDerivedPullback A k).obj M)
  simp only [constantComparison_eq, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  exact hm

end AlgebraicGeometry.Scheme
