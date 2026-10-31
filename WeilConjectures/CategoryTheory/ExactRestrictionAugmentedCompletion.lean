/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AugmentedDerivedTowerUnit
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Localization.Adjunction

/-! # Exact restriction and augmented derived completion

Source: Stacks Project, Tags 0940 and 0A07 (`sites-cohomology.tex`), with the
agent-written augmentation normalization in the DAG
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion).

The helper definitions below use the existing strict tower, cochain, limit, and
exact-derived constructions. Universal derived presentations are supplied with
comparisons; a Roos-triangle property alone does not specify these data.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB vA vB wA wB wTA wTB

open CategoryTheory.Limits

namespace CategoryTheory.ExactRestrictionAugmentedCompletion

/-- Levelwise application to strict towers, using Mathlib's whiskering functor.
Source: Stacks 0940
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion). -/
abbrev towerMap {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    (U : B ⥤ A) : (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ A) :=
  (Functor.whiskeringRight ℕᵒᵖ B A).obj U

/-- Levelwise finite-limit preservation is the existing functor-category instance.
Source: Stacks 0940
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion). -/
instance towerMapFiniteLimits {A : Type uA} {B : Type uB}
    [Category.{vA} A] [Category.{vB} B] [HasFiniteLimits B]
    (U : B ⥤ A) [PreservesFiniteLimits U] :
    PreservesFiniteLimits (towerMap U) := ⟨fun _ _ _ ↦ inferInstance⟩

/-- Levelwise finite-colimit preservation is the existing functor-category instance.
Source: Stacks 0940
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion). -/
instance towerMapFiniteColimits {A : Type uA} {B : Type uB}
    [Category.{vA} A] [Category.{vB} B] [HasFiniteColimits B]
    (U : B ⥤ A) [PreservesFiniteColimits U] :
    PreservesFiniteColimits (towerMap U) := ⟨fun _ _ _ ↦ inferInstance⟩

/-- The ordinary limit is additive because it preserves binary products.
Source: Stacks 0940
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion). -/
instance limitAdditive (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Ordinary tower limit applied degreewise, with no product-exactness hypothesis.
Source: Stacks 0940
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion). -/
noncomputable abbrev complexLimit (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)

/-- Constant strict towers applied degreewise.
Source: Stacks 0940
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion). -/
abbrev complexConstant (A : Type uA) [Category.{vA} A] [Abelian A] :
    CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ :=
  (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapHomologicalComplex (.up ℤ)

/-- The compatible-family limit isomorphism, constructed from the ordinary adjunction.
Its component in degree `k` is `preservesLimitIso U (X.X k)`, whose projection
identity is `preservesLimitIso_hom_π`. Source: Stacks 0940 and 0A07
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion). -/
noncomputable def ordinaryLimitIso {A : Type uA} {B : Type uB}
    [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    {E : A ⥤ B} {U : B ⥤ A} [U.Additive] (a : E ⊣ U) :
    complexLimit B ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      (towerMap U).mapHomologicalComplex (.up ℤ) ⋙ complexLimit A :=
  letI : PreservesLimitsOfSize.{0, 0} U := a.rightAdjoint_preservesLimits
  NatIso.mapHomologicalComplex (preservesLimitNatIso U) (.up ℤ)

/-- The ordinary constant/limit unit on cochain complexes.
Source: Stacks 0940, constant-tower/limit adjunction
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion). -/
noncomputable def ordinaryUnit (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] :
    𝟭 (CochainComplex A ℤ) ⟶ complexConstant A ⋙ complexLimit A :=
  (Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv ≫
    NatTrans.mapHomologicalComplex
      (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⊣ lim).unit (.up ℤ)

/-- The two defining equations for the maps `t` and `v` of the augmented-unit lemma.
The actual completion map is `v ≫ Functor.whiskerRight t RL`.
Source: Stacks 099M and `exists_augmentedDerivedTowerUnit`
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion). -/
def NormalizedUnit {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{wA} A]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    (T : CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (η : complexConstant A ⟶ T)
    (LT : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A))
    (ε : DerivedCategory.Q ⋙ LT ⟶ T ⋙ DerivedCategory.Q)
    (RL : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (δ : complexLimit A ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (t : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⟶ LT)
    (v : 𝟭 (DerivedCategory A) ⟶
      (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⋙ RL) : Prop :=
  (∀ P : CochainComplex A ℤ,
    t.app (DerivedCategory.Q.obj P) ≫ ε.app P =
      (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map (η.app P)) ∧
  (∀ P : CochainComplex A ℤ,
    v.app (DerivedCategory.Q.obj P) ≫ RL.map
        ((Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((ordinaryUnit A).app P) ≫
        δ.app ((complexConstant A).obj P))

end CategoryTheory.ExactRestrictionAugmentedCompletion

namespace CategoryTheory.ExactRestrictionAugmentedCompletion

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem monicKInjectiveResolutions
    {C : Type uA} [Category.{vA} C] [Abelian C]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q) :
    Abelian.HasKInjectiveResolutions C := by
  constructor
  intro K
  obtain ⟨I, q, hI, hq⟩ := h K
  -- Add a contractible summand to make the resolution monic in every degree.
  let T := CochainComplex.mappingCone (𝟙 K)
  let e : HomotopyEquiv (T ⊞ I) I :=
    { hom := biprod.snd
      inv := biprod.inr
      homotopyHomInvId := by
        let h₀ : Homotopy (𝟙 T) 0 :=
          CochainComplex.mappingCone.liftHomotopy _ _ _
            (CochainComplex.mappingCone.snd _) 0 (by simp) (by simp)
        let h₁ := (h₀.compRight (biprod.inl : T ⟶ T ⊞ I)).compLeft
          (biprod.fst : T ⊞ I ⟶ T)
        let h₂ := Homotopy.add h₁ (Homotopy.refl
          ((biprod.snd : T ⊞ I ⟶ I) ≫ biprod.inr))
        exact (Homotopy.ofEq (by simp)).trans
          (h₂.symm.trans (Homotopy.ofEq (by simp)))
      homotopyInvHomId := Homotopy.ofEq (by simp) }
  have : (T ⊞ I).IsKInjective := e.symm.isKInjective
  let i : K ⟶ T ⊞ I :=
    biprod.lift (CochainComplex.mappingCone.inr (𝟙 K)) q
  have hi : Mono i := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    have hfac : i.f n ≫ (biprod.fst : T ⊞ I ⟶ T).f n ≫
        (CochainComplex.mappingCone.snd (𝟙 K)).v n n (add_zero n) = 𝟙 _ := by
      simp [i, T]
    exact mono_of_mono_fac hfac
  have : QuasiIso e.hom := e.quasiIso_hom
  have : QuasiIso i := by
    have : QuasiIso (i ≫ e.hom) := by simpa [i, e] using hq
    exact (quasiIso_iff_comp_right i e.hom).mp inferInstance
  exact ⟨T ⊞ I, inferInstance, i, hi, inferInstance⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryUnitCompatibility
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    {E : A ⥤ B} {U : B ⥤ A} [U.Additive] (a : E ⊣ U)
    (P : CochainComplex B ℤ) :
    (U.mapHomologicalComplex (.up ℤ)).map ((ordinaryUnit B).app P) ≫
        (ordinaryLimitIso a).hom.app ((complexConstant B).obj P) ≫
        (complexLimit A).map
          ((NatIso.mapHomologicalComplex (Functor.compConstIso ℕᵒᵖ U) (.up ℤ)).inv.app P) =
      (ordinaryUnit A).app ((U.mapHomologicalComplex (.up ℤ)).obj P) := by
  ext k
  apply limit.hom_ext
  intro n
  simp [ordinaryUnit, ordinaryLimitIso, complexLimit, complexConstant,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
    Functor.mapHomologicalComplexIdIso, preservesLimitNatIso, Functor.compConstIso,
    constLimAdj, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryCompletionCompatibility
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    {E : A ⥤ B} {U : B ⥤ A} [U.Additive] (a : E ⊣ U)
    (TA : CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (ηA : complexConstant A ⟶ TA) (ηB : complexConstant B ⟶ TB)
    (θ : TB ⋙ (towerMap U).mapHomologicalComplex (.up ℤ) ≅
      U.mapHomologicalComplex (.up ℤ) ⋙ TA)
    (hη : ∀ P : CochainComplex B ℤ,
      ((towerMap U).mapHomologicalComplex (.up ℤ)).map (ηB.app P) ≫ θ.hom.app P =
        (NatIso.mapHomologicalComplex
          (Functor.compConstIso ℕᵒᵖ U) (.up ℤ)).inv.app P ≫
            ηA.app ((U.mapHomologicalComplex (.up ℤ)).obj P))
    (P : CochainComplex B ℤ) :
    (U.mapHomologicalComplex (.up ℤ)).map
        ((ordinaryUnit B).app P ≫ (complexLimit B).map (ηB.app P)) ≫
        (ordinaryLimitIso a).hom.app (TB.obj P) ≫
        (complexLimit A).map (θ.hom.app P) =
      (ordinaryUnit A).app ((U.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (complexLimit A).map (ηA.app ((U.mapHomologicalComplex (.up ℤ)).obj P)) := by
  have hn := (ordinaryLimitIso a).hom.naturality (ηB.app P)
  dsimp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, ← Category.assoc _ _
    ((complexLimit A).map (θ.hom.app P)), hn]
  simp only [Category.assoc]
  rw [← Functor.map_comp, hη, Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ (complexLimit A).map
      (ηA.app ((U.mapHomologicalComplex (.up ℤ)).obj P)))
      (ordinaryUnitCompatibility a P)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalizedCompletion
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{wA} A]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
    (T : CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (η : complexConstant A ⟶ T)
    (LT : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A))
    (ε : DerivedCategory.Q ⋙ LT ⟶ T ⋙ DerivedCategory.Q)
    (RL : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (δ : complexLimit A ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RL)
    (t : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⟶ LT)
    (v : 𝟭 (DerivedCategory A) ⟶
      (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⋙ RL)
    (h : NormalizedUnit T η LT ε RL δ t v) (P : CochainComplex A ℤ) :
    (v ≫ Functor.whiskerRight t RL).app (DerivedCategory.Q.obj P) ≫ RL.map (ε.app P) =
      DerivedCategory.Q.map ((ordinaryUnit A).app P ≫ (complexLimit A).map (η.app P)) ≫
        δ.app (T.obj P) := by
  change (v.app _ ≫ RL.map (t.app _)) ≫ RL.map (ε.app P) = _
  have hn := δ.naturality (η.app P)
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← RL.map_comp, h.1 P, RL.map_comp, ← Category.assoc, h.2 P,
    Category.assoc, ← hn, ← Category.assoc, ← DerivedCategory.Q.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derives
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wB} D]
    (F : C ⥤ D) [F.Additive] :
    (CochainComplex.KInjectives.localizerMorphism C).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : X.obj.IsKInjective := X.property
  have : Y.obj.IsKInjective := Y.property
  have hq : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp hq
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    erw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unitIso
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wB} D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (RF : DerivedCategory C ⥤ DerivedCategory D)
    (δ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    [RF.IsLeftKanExtension δ]
    (I : CochainComplex C ℤ) [I.IsKInjective] : IsIso (δ.app I) := by
  have : RF.IsRightDerivedFunctor δ (HomologicalComplex.quasiIso C (.up ℤ)) :=
    ⟨inferInstance⟩
  exact (derives F).isIso_of_isRightDerivedFunctor δ (CochainComplex.KInjectives.mk I)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derivedAdjunction
    {C : Type uA} {D : Type uB} [Category.{vA} C] [Category.{vB} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wA} C] [HasDerivedCategory.{wB} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    Nonempty (F.mapDerivedCategory ⊣ G.mapDerivedCategory) := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory := ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q G.mapDerivedCategory := ⟨(Functor.mapDerivedCategoryFactors _).symm⟩
  exact ⟨(a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    F.mapDerivedCategory G.mapDerivedCategory⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem natTransExtResolving
    {C : Type uA} {D : Type uB} {H : Type wA}
    [Category.{vA} C] [Category.{vB} D] [Category.{wB} H]
    (W : MorphismProperty C) (q : C ⥤ D) [q.IsLocalization W]
    (P : C → Prop) (hP : ∀ X : C, ∃ (Y : C) (j : Y ⟶ X), P Y ∧ W j)
    {F G : D ⥤ H} (t s : F ⟶ G)
    (h : ∀ X : C, P X → t.app (q.obj X) = s.app (q.obj X)) : t = s := by
  apply Localization.natTrans_ext q W
  intro X
  obtain ⟨Y, j, hY, hj⟩ := hP X
  have := Localization.inverts q W j hj
  apply (cancel_epi (F.map (q.map j))).mp
  rw [t.naturality, s.naturality, h Y hY]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem kanRightAdjoint
    {C : Type uA} {D : Type uB} {H : Type vA} {H' : Type vB}
    [Category C] [Category D] [Category H] [Category H']
    {S : H' ⥤ H} {R : H ⥤ H'} (a : S ⊣ R)
    (q : C ⥤ D) (F : C ⥤ H) (RF : D ⥤ H)
    (ε : q ⋙ RF ⟶ F) [RF.IsRightKanExtension ε] :
    (RF ⋙ R).IsRightKanExtension
      ((Functor.associator q RF R).inv ≫ Functor.whiskerRight ε R) := by
  classical
  let ε' := (Functor.associator q RF R).inv ≫ Functor.whiskerRight ε R
  let lift (G : D ⥤ H') (b : q ⋙ G ⟶ F ⋙ R) : G ⟶ RF ⋙ R :=
    ((a.whiskerRight D).homEquiv G RF)
      (RF.liftOfIsRightKanExtension ε (G ⋙ S)
        (((a.whiskerRight C).homEquiv (q ⋙ G) F).symm b))
  have mate (G : D ⥤ H') (t : G ⟶ RF ⋙ R) :
      ((a.whiskerRight C).homEquiv (q ⋙ G) F).symm
          (Functor.whiskerLeft q t ≫ ε') =
        Functor.whiskerLeft q (((a.whiskerRight D).homEquiv G RF).symm t) ≫ ε := by
    ext X
    dsimp [Adjunction.homEquiv, Adjunction.whiskerRight, ε']
    simp only [Category.id_comp, Category.comp_id]
    rw [S.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj,
      Category.assoc] using
      congrArg (fun f ↦ S.map (t.app (q.obj X)) ≫ f)
        (a.counit.naturality (ε.app X))
  have fac (G : D ⥤ H') (b : q ⋙ G ⟶ F ⋙ R) :
      Functor.whiskerLeft q (lift G b) ≫ ε' = b := by
    apply ((a.whiskerRight C).homEquiv (q ⋙ G) F).symm.injective
    rw [mate]
    dsimp only [lift]
    rw [Equiv.symm_apply_apply]
    exact RF.liftOfIsRightKanExtension_fac ε (G ⋙ S) _
  have uniq (G : D ⥤ H') (b : q ⋙ G ⟶ F ⋙ R) (t : G ⟶ RF ⋙ R)
      (ht : Functor.whiskerLeft q t ≫ ε' = b) : t = lift G b := by
    apply ((a.whiskerRight D).homEquiv G RF).symm.injective
    apply RF.hom_ext_of_isRightKanExtension ε
    have h := congrArg (((a.whiskerRight C).homEquiv (q ⋙ G) F).symm) ht
    rw [mate] at h
    dsimp only [lift]
    rw [Equiv.symm_apply_apply]
    exact h.trans (RF.liftOfIsRightKanExtension_fac ε (G ⋙ S) _).symm
  constructor
  refine ⟨IsTerminal.ofUniqueHom
    (fun Z ↦ CostructuredArrow.homMk (lift Z.left Z.hom) (fac Z.left Z.hom)) ?_⟩
  intro Z m
  apply CostructuredArrow.hom_ext
  exact uniq Z.left Z.hom m.left (by simpa using m.w)

-- Keep the supplied statement verbatim, including its redundant resolution and homotopy data.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- Exact right adjoints preserve the normalized augmented derived completion unit.

Source: Stacks 0940 and 0A07, exact-adjoint strict-tower case; augmentation/Kan
normalization written in the DAG
(blueprint: lem-weil-pbc-exact-restriction-augmented-completion).

The first equation fixes `γ` on every strict tower complex. The equation for `ρ`
is imposed on the resolving class only. The quantified pairs `(tA, vA)` and
`(tB, vB)` are exactly the unique maps of `exists_augmentedDerivedTowerUnit`,
by `NormalizedUnit`; thus the last equation uses its actual maps `c = RF(t) ∘ v`.
All four derived-category morphism universes are independent.

Proof:
1. Upgrade the given tower resolutions to monomorphic ones by adjoining the
   contractible mapping cone of the identity. For an additive functor, a
   quasi-isomorphism between K-injectives is a homotopy equivalence and remains
   so after application of the functor. Thus the K-injective derivability
   structure computes every supplied universal right-derived comparison.
2. Apply the exact adjunction levelwise: the right adjoint preserves
   K-injectives. Both `RLB ⋙ D(U)` and `D(U^T) ⋙ RLA` are universal right
   derived functors of `complexLimit B ⋙ Q ⋙ D(U)`. Their units are `α` and `β`
   below, with `β` using `ordinaryLimitIso a` and the exact localization factors.
   Derived uniqueness gives `γ`, its equation on every complex, and uniqueness.
3. Localize the exact tower adjunction using the canonical exact-functor factors.
   Its right adjoint preserves right Kan extensions: transpose a transformation,
   lift through the given Kan extension, then transpose back. The counit
   naturality and the adjunction triangles verify factorization and uniqueness.
4. Lift `εA` followed by the inverse of `θ` to obtain `σ`. Both counits are
   invertible on the resolving class; naturality along its quasi-isomorphisms
   makes `σ` invertible everywhere. Set `ρ = σ⁻¹`. The lift equation gives its
   normalization on every complex. Cancel the invertible counits only on the
   resolving class to prove uniqueness there, then extend by localization.
5. The two equations of `NormalizedUnit` and naturality of `δ` give directly
   `c(QP) ≫ RL(εP) = Q(νP ≫ L(ηP)) ≫ δ(TP)`. This is the ordinary-map
   normalization of `exists_augmentedDerivedTowerUnit`, proved here for the
   supplied `t` and `v`. The ordinary restriction comparison preserves `ν`:
   degreewise, both maps have identity composite with every limit projection.
   Naturality and the augmentation square then show it preserves `ν ≫ L(η)`.
6. Check the desired equality on the resolving class, after postcomposition
   with `RLA(LTA(U.mapDerivedCategoryFactors.hom) ≫ εA)`, which is invertible
   there. Naturality of `γ` at `εB`, its all-complex equation, step 5, and the
   equation for `ρ` reduce both sides to the same ordinary map followed by `δA`.
   Naturality along a resolving quasi-isomorphism and localization extend the
   equality to every derived object. No countable product exactness or
   invertibility of a counit away from the resolving class is used. -/
theorem exists_exactRestrictionAugmentedCompletion
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{vA} A] [IsGrothendieckAbelian.{vB} B]
    [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]
    (hIA : ∀ K : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (j : K ⟶ I), I.IsKInjective ∧ QuasiIso j)
    (hIB : ∀ K : CochainComplex B ℤ,
      ∃ (I : CochainComplex B ℤ) (j : K ⟶ I), I.IsKInjective ∧ QuasiIso j)
    (hITA : ∀ K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (j : K ⟶ I), I.IsKInjective ∧ QuasiIso j)
    (hITB : ∀ K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (j : K ⟶ I), I.IsKInjective ∧ QuasiIso j)
    (E : A ⥤ B) (U : B ⥤ A) [E.Additive] [U.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] (a : E ⊣ U)
    (RLA : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (RLB : DerivedCategory (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory B)
    (δA : complexLimit A ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RLA)
    (δB : complexLimit B ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RLB)
    [RLA.IsLeftKanExtension δA] [RLB.IsLeftKanExtension δB] :
    ∃ γ : RLB ⋙ U.mapDerivedCategory ≅ (towerMap U).mapDerivedCategory ⋙ RLA,
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
        U.mapDerivedCategory.map (δB.app X) ≫ γ.hom.app (DerivedCategory.Q.obj X) =
          U.mapDerivedCategoryFactors.hom.app ((complexLimit B).obj X) ≫
            DerivedCategory.Q.map ((ordinaryLimitIso a).hom.app X) ≫
            δA.app (((towerMap U).mapHomologicalComplex (.up ℤ)).obj X) ≫
            RLA.map ((towerMap U).mapDerivedCategoryFactors.inv.app X)) ∧
      (∀ γ' : RLB ⋙ U.mapDerivedCategory ≅ (towerMap U).mapDerivedCategory ⋙ RLA,
        (∀ X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
          U.mapDerivedCategory.map (δB.app X) ≫ γ'.hom.app (DerivedCategory.Q.obj X) =
            U.mapDerivedCategoryFactors.hom.app ((complexLimit B).obj X) ≫
              DerivedCategory.Q.map ((ordinaryLimitIso a).hom.app X) ≫
              δA.app (((towerMap U).mapHomologicalComplex (.up ℤ)).obj X) ≫
              RLA.map ((towerMap U).mapDerivedCategoryFactors.inv.app X)) → γ' = γ) ∧
      (∀ (TA : CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
        (TB : CochainComplex B ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
        [TA.Additive] [TB.Additive]
        (hTA : ∀ (P Q : CochainComplex A ℤ) (f g : P ⟶ Q),
          Nonempty (Homotopy f g) → Nonempty (Homotopy (TA.map f) (TA.map g)))
        (hTB : ∀ (P Q : CochainComplex B ℤ) (f g : P ⟶ Q),
          Nonempty (Homotopy f g) → Nonempty (Homotopy (TB.map f) (TB.map g)))
        (ηA : complexConstant A ⟶ TA) (ηB : complexConstant B ⟶ TB)
        (LTA : DerivedCategory A ⥤ DerivedCategory (ℕᵒᵖ ⥤ A))
        (LTB : DerivedCategory B ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
        (εA : DerivedCategory.Q ⋙ LTA ⟶ TA ⋙ DerivedCategory.Q)
        (εB : DerivedCategory.Q ⋙ LTB ⟶ TB ⋙ DerivedCategory.Q)
        [LTA.IsRightKanExtension εA] [LTB.IsRightKanExtension εB]
        (PA : CochainComplex A ℤ → Prop) (PB : CochainComplex B ℤ → Prop)
        (hPA : ∀ K : CochainComplex A ℤ,
          ∃ (P : CochainComplex A ℤ) (j : P ⟶ K), PA P ∧ QuasiIso j)
        (hPB : ∀ K : CochainComplex B ℤ,
          ∃ (P : CochainComplex B ℤ) (j : P ⟶ K), PB P ∧ QuasiIso j)
        (hεA : ∀ P : CochainComplex A ℤ, PA P → IsIso (εA.app P))
        (hεB : ∀ P : CochainComplex B ℤ, PB P → IsIso (εB.app P))
        (hUP : ∀ P : CochainComplex B ℤ,
          PB P → PA ((U.mapHomologicalComplex (.up ℤ)).obj P))
        (θ : TB ⋙ (towerMap U).mapHomologicalComplex (.up ℤ) ≅
          U.mapHomologicalComplex (.up ℤ) ⋙ TA)
        (hη : ∀ P : CochainComplex B ℤ,
          ((towerMap U).mapHomologicalComplex (.up ℤ)).map (ηB.app P) ≫ θ.hom.app P =
            (NatIso.mapHomologicalComplex
              (Functor.compConstIso ℕᵒᵖ U) (.up ℤ)).inv.app P ≫
                ηA.app ((U.mapHomologicalComplex (.up ℤ)).obj P)),
        ∃ ρ : LTB ⋙ (towerMap U).mapDerivedCategory ≅ U.mapDerivedCategory ⋙ LTA,
          (∀ P : CochainComplex B ℤ, PB P →
            ρ.hom.app (DerivedCategory.Q.obj P) ≫
                LTA.map (U.mapDerivedCategoryFactors.hom.app P) ≫
                εA.app ((U.mapHomologicalComplex (.up ℤ)).obj P) =
              (towerMap U).mapDerivedCategory.map (εB.app P) ≫
                (towerMap U).mapDerivedCategoryFactors.hom.app (TB.obj P) ≫
                DerivedCategory.Q.map (θ.hom.app P)) ∧
          (∀ ρ' : LTB ⋙ (towerMap U).mapDerivedCategory ≅ U.mapDerivedCategory ⋙ LTA,
            (∀ P : CochainComplex B ℤ, PB P →
              ρ'.hom.app (DerivedCategory.Q.obj P) ≫
                  LTA.map (U.mapDerivedCategoryFactors.hom.app P) ≫
                  εA.app ((U.mapHomologicalComplex (.up ℤ)).obj P) =
                (towerMap U).mapDerivedCategory.map (εB.app P) ≫
                  (towerMap U).mapDerivedCategoryFactors.hom.app (TB.obj P) ≫
                  DerivedCategory.Q.map (θ.hom.app P)) → ρ' = ρ) ∧
          (∀ (tA : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⟶ LTA)
            (vA : 𝟭 (DerivedCategory A) ⟶
              (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)).mapDerivedCategory ⋙ RLA)
            (tB : (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategory ⟶ LTB)
            (vB : 𝟭 (DerivedCategory B) ⟶
              (Functor.const ℕᵒᵖ : B ⥤ (ℕᵒᵖ ⥤ B)).mapDerivedCategory ⋙ RLB),
            NormalizedUnit TA ηA LTA εA RLA δA tA vA →
            NormalizedUnit TB ηB LTB εB RLB δB tB vB →
            ∀ M : DerivedCategory B,
              U.mapDerivedCategory.map ((vB ≫ Functor.whiskerRight tB RLB).app M) ≫
                  γ.hom.app (LTB.obj M) ≫ RLA.map (ρ.hom.app M) =
                (vA ≫ Functor.whiskerRight tA RLA).app (U.mapDerivedCategory.obj M))) := by
  classical
  let := monicKInjectiveResolutions hITA
  let := monicKInjectiveResolutions hITB
  have : (towerMap U).PreservesKInjectiveComplexes :=
    (a.whiskerRight ℕᵒᵖ).preservesKInjectiveComplexes
  let F := complexLimit B ⋙ DerivedCategory.Q ⋙ U.mapDerivedCategory
  let α : F ⟶ DerivedCategory.Q ⋙ (RLB ⋙ U.mapDerivedCategory) :=
    Functor.whiskerRight δB U.mapDerivedCategory
  let β : F ⟶ DerivedCategory.Q ⋙ ((towerMap U).mapDerivedCategory ⋙ RLA) :=
    Functor.whiskerLeft (complexLimit B) U.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (ordinaryLimitIso a).hom DerivedCategory.Q ≫
      Functor.whiskerLeft ((towerMap U).mapHomologicalComplex (.up ℤ)) δA ≫
      Functor.whiskerRight (towerMap U).mapDerivedCategoryFactors.inv RLA
  have hd : (CochainComplex.KInjectives.localizerMorphism (ℕᵒᵖ ⥤ B)).Derives F := by
    intro X Y f hf
    have : IsIso (DerivedCategory.Q.map ((complexLimit B).map f.hom)) :=
      derives (lim : (ℕᵒᵖ ⥤ B) ⥤ B) f hf
    change IsIso (U.mapDerivedCategory.map
      (DerivedCategory.Q.map ((complexLimit B).map f.hom)))
    infer_instance
  have hα : (RLB ⋙ U.mapDerivedCategory).IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ)) := by
    apply hd.isRightDerivedFunctor_of_isIso α
    intro I
    have := I.property
    have := unitIso (lim : (ℕᵒᵖ ⥤ B) ⥤ B) RLB δB I.obj
    change IsIso (U.mapDerivedCategory.map (δB.app I.obj))
    infer_instance
  have hβ : ((towerMap U).mapDerivedCategory ⋙ RLA).IsRightDerivedFunctor β
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ)) := by
    apply hd.isRightDerivedFunctor_of_isIso β
    intro I
    have := I.property
    have := unitIso (lim : (ℕᵒᵖ ⥤ A) ⥤ A) RLA δA
      (((towerMap U).mapHomologicalComplex (.up ℤ)).obj I.obj)
    dsimp [β]
    infer_instance
  let γ := Functor.rightDerivedUnique (RLB ⋙ U.mapDerivedCategory)
    ((towerMap U).mapDerivedCategory ⋙ RLA) α β
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))
  have hγ (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
      U.mapDerivedCategory.map (δB.app X) ≫ γ.hom.app (DerivedCategory.Q.obj X) =
        U.mapDerivedCategoryFactors.hom.app ((complexLimit B).obj X) ≫
          DerivedCategory.Q.map ((ordinaryLimitIso a).hom.app X) ≫
          δA.app (((towerMap U).mapHomologicalComplex (.up ℤ)).obj X) ≫
          RLA.map ((towerMap U).mapDerivedCategoryFactors.inv.app X) := by
    simpa [γ, β, α, Functor.rightDerivedUnique] using
      Functor.rightDerivedNatTrans_app (RLB ⋙ U.mapDerivedCategory)
        ((towerMap U).mapDerivedCategory ⋙ RLA) α β
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ)) (𝟙 F) X
  have : (RLB ⋙ U.mapDerivedCategory).IsLeftKanExtension α :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))
  refine ⟨γ, hγ, ?_, ?_⟩
  · intro γ' hγ'
    apply Iso.ext
    apply (RLB ⋙ U.mapDerivedCategory).hom_ext_of_isLeftKanExtension α
    ext X
    exact (hγ' X).trans (hγ X).symm
  · intro TA TB _ _ hTA hTB ηA ηB LTA LTB εA εB _ _ PA PB hPA hPB hεA hεB hUP θ hη
    let R := (towerMap U).mapDerivedCategory
    let V := U.mapDerivedCategory
    let Uc := U.mapHomologicalComplex (.up ℤ)
    let Rc := (towerMap U).mapHomologicalComplex (.up ℤ)
    let ε' : DerivedCategory.Q ⋙ (LTB ⋙ R) ⟶ TB ⋙ DerivedCategory.Q ⋙ R :=
      Functor.whiskerRight εB R
    obtain ⟨ad⟩ := derivedAdjunction (a.whiskerRight ℕᵒᵖ)
    have : (LTB ⋙ R).IsRightKanExtension ε' := by
      have he : (Functor.associator DerivedCategory.Q LTB R).inv ≫
          Functor.whiskerRight εB R = ε' := by
        ext P
        simp [ε']
      rw [← he]
      exact kanRightAdjoint ad DerivedCategory.Q (TB ⋙ DerivedCategory.Q) LTB εB
    let b : DerivedCategory.Q ⋙ (V ⋙ LTA) ⟶ TB ⋙ DerivedCategory.Q ⋙ R :=
      Functor.whiskerRight U.mapDerivedCategoryFactors.hom LTA ≫
        Functor.whiskerLeft Uc εA ≫
        Functor.whiskerRight θ.inv DerivedCategory.Q ≫
        Functor.whiskerLeft TB (towerMap U).mapDerivedCategoryFactors.inv
    let σ : V ⋙ LTA ⟶ LTB ⋙ R := (LTB ⋙ R).liftOfIsRightKanExtension ε' (V ⋙ LTA) b
    have hσ (P : CochainComplex B ℤ) :
        σ.app (DerivedCategory.Q.obj P) ≫ R.map (εB.app P) =
          LTA.map (U.mapDerivedCategoryFactors.hom.app P) ≫ εA.app (Uc.obj P) ≫
            DerivedCategory.Q.map (θ.inv.app P) ≫
            (towerMap U).mapDerivedCategoryFactors.inv.app (TB.obj P) :=
      (LTB ⋙ R).liftOfIsRightKanExtension_fac_app ε' (V ⋙ LTA) b P
    have hσP (P : CochainComplex B ℤ) (hP : PB P) :
        IsIso (σ.app (DerivedCategory.Q.obj P)) := by
      have := hεB P hP
      have := hεA (Uc.obj P) (hUP P hP)
      have : IsIso (σ.app (DerivedCategory.Q.obj P) ≫ R.map (εB.app P)) := by
        rw [hσ]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (R.map (εB.app P))
    have hσQ (K : CochainComplex B ℤ) : IsIso (σ.app (DerivedCategory.Q.obj K)) := by
      obtain ⟨P, j, hP, hj⟩ := hPB K
      have := hσP P hP
      have : QuasiIso j := hj
      exact (NatTrans.isIso_app_iff_of_iso σ (asIso (DerivedCategory.Q.map j))).mp
        inferInstance
    have : IsIso σ := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro M
      have := hσQ (DerivedCategory.Q.objPreimage M)
      exact (NatTrans.isIso_app_iff_of_iso σ (DerivedCategory.Q.objObjPreimageIso M)).mp
        inferInstance
    let ρ : LTB ⋙ R ≅ V ⋙ LTA := (asIso σ).symm
    have hρ (P : CochainComplex B ℤ) :
        ρ.hom.app (DerivedCategory.Q.obj P) ≫
            LTA.map (U.mapDerivedCategoryFactors.hom.app P) ≫ εA.app (Uc.obj P) =
          R.map (εB.app P) ≫ (towerMap U).mapDerivedCategoryFactors.hom.app (TB.obj P) ≫
            DerivedCategory.Q.map (θ.hom.app P) := by
      have h := hσ P
      apply (cancel_epi (σ.app (DerivedCategory.Q.obj P))).mp
      change σ.app _ ≫ (inv σ).app _ ≫ _ = _
      rw [← Category.assoc, show σ.app _ ≫ (inv σ).app _ = 𝟙 _ from
        NatTrans.congr_app (IsIso.hom_inv_id σ) _, Category.id_comp]
      rw [← Category.assoc, ← Category.assoc, h]
      simp [← DerivedCategory.Q.map_comp, Category.assoc, V, R, Uc]
    refine ⟨ρ, fun P _ ↦ hρ P, ?_, ?_⟩
    · intro ρ' hρ'
      apply Iso.ext
      apply natTransExtResolving (HomologicalComplex.quasiIso B (.up ℤ))
        DerivedCategory.Q PB hPB ρ'.hom ρ.hom
      intro P hP
      have := hεA (Uc.obj P) (hUP P hP)
      apply (cancel_mono
        (LTA.map (U.mapDerivedCategoryFactors.hom.app P) ≫ εA.app (Uc.obj P))).mp
      simpa only [Category.assoc] using (hρ' P hP).trans (hρ P).symm
    · intro tA vA tB vB hA hB M
      let cA := vA ≫ Functor.whiskerRight tA RLA
      let cB := vB ≫ Functor.whiskerRight tB RLB
      let l : V ⟶ V ⋙ LTA ⋙ RLA :=
        Functor.whiskerRight cB V ≫ Functor.whiskerLeft LTB γ.hom ≫
          Functor.whiskerRight ρ.hom RLA
      let r : V ⟶ V ⋙ LTA ⋙ RLA := Functor.whiskerLeft V cA
      suffices he : l = r from NatTrans.congr_app he M
      apply natTransExtResolving (HomologicalComplex.quasiIso B (.up ℤ))
        DerivedCategory.Q PB hPB l r
      intro P hP
      have := hεA (Uc.obj P) (hUP P hP)
      apply (cancel_mono (RLA.map
        (LTA.map (U.mapDerivedCategoryFactors.hom.app P) ≫ εA.app (Uc.obj P)))).mp
      change (V.map (cB.app _) ≫ γ.hom.app _ ≫ RLA.map (ρ.hom.app _)) ≫ _ =
        cA.app (V.obj _) ≫ _
      rw [Category.assoc, Category.assoc, ← RLA.map_comp, hρ, RLA.map_comp,
        RLA.map_comp]
      have hn := γ.hom.naturality (εB.app P)
      change V.map (RLB.map (εB.app P)) ≫ γ.hom.app (DerivedCategory.Q.obj (TB.obj P)) =
        γ.hom.app (LTB.obj (DerivedCategory.Q.obj P)) ≫ RLA.map (R.map (εB.app P)) at hn
      rw [← Category.assoc (γ.hom.app _), ← hn]
      simp only [Category.assoc]
      rw [← Category.assoc (V.map _), ← V.map_comp,
        normalizedCompletion TB ηB LTB εB RLB δB tB vB hB P, V.map_comp]
      simp only [Category.assoc]
      rw [reassoc_of% hγ (TB.obj P)]
      simp only [← RLA.map_comp, Iso.inv_hom_id_app_assoc]
      have hu := U.mapDerivedCategoryFactors.hom.naturality
        ((ordinaryUnit B).app P ≫ (complexLimit B).map (ηB.app P))
      dsimp only [Functor.comp_map] at hu
      rw [← Category.assoc (V.map _), hu]
      simp only [Category.assoc]
      have hd := δA.naturality (θ.hom.app P)
      change DerivedCategory.Q.map ((complexLimit A).map (θ.hom.app P)) ≫
          δA.app (TA.obj (Uc.obj P)) =
        δA.app (Rc.obj (TB.obj P)) ≫ RLA.map (DerivedCategory.Q.map (θ.hom.app P)) at hd
      rw [← hd]
      simp only [← DerivedCategory.Q.map_comp_assoc]
      rw [ordinaryCompletionCompatibility a TA TB ηA ηB θ hη P]
      rw [RLA.map_comp, ← Category.assoc (cA.app _)]
      have hc := cA.naturality (U.mapDerivedCategoryFactors.hom.app P)
      change U.mapDerivedCategoryFactors.hom.app P ≫
          cA.app (DerivedCategory.Q.obj (Uc.obj P)) =
        cA.app (V.obj (DerivedCategory.Q.obj P)) ≫
          RLA.map (LTA.map (U.mapDerivedCategoryFactors.hom.app P)) at hc
      dsimp only [Functor.id_obj]
      rw [← hc]
      simp only [Category.assoc]
      rw [normalizedCompletion TA ηA LTA εA RLA δA tA vA hA (Uc.obj P)]

end CategoryTheory.ExactRestrictionAugmentedCompletion
