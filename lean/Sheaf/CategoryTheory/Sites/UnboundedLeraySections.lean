/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.CategoryTheory.Sites.RingedSiteSectionFunctors
import Sheaf.CategoryTheory.Sites.LeraySectionResolutionQuasiIso
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Unbounded objectwise Leray comparison on ringed sites

Source: Stacks Project, Cohomology on Sites, Tag 0D6H, second assertion
(blueprint: lem-sfb-ringed-site-unbounded-leray-sections).

The section functors and their unbounded right derived functors are the existing
`RingedSiteSectionFunctors.sectionEvaluation` and its existing `rightDerivedFunctor`
(the defining expression of `derivedEvaluation`). The comparison is
specified by its value on every K-injective resolution and by restriction squares.
The unit formula is the canonical composition comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u wC wD wA

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedSiteSectionFunctors

namespace CategoryTheory.UnboundedSectionsLocalization

/-- Restriction of abelian sections along a site arrow, with scalars forgotten.
Source: Stacks Project, Tag 0D6H, objectwise naturality
(blueprint: lem-sfb-ringed-site-unbounded-leray-sections). -/
def lerayRestriction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {V' V : C} (v : V' ⟶ V) :
    sectionEvaluation R V ⟶ sectionEvaluation R V' where
  app M := M.val.presheaf.map v.op
  naturality {_M _N} a := (((PresheafOfModules.toPresheaf R.obj).map a.val).naturality v.op).symm

/-- The ordinary restriction transformation induces the restriction on unbounded
right derived sectionEvaluation; thus it includes identities and composites.
Source: Stacks Project, Tag 0D6H
(blueprint: lem-sfb-ringed-site-unbounded-leray-sections). -/
def lerayDerivedRestriction {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasDerivedCategory.{wC} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{wA} AddCommGrpCat.{u}]
    {V' V : C} (v : V' ⟶ V) :
    (sectionEvaluation R V).rightDerivedFunctor ⟶ (sectionEvaluation R V').rightDerivedFunctor :=
  Functor.rightDerivedFunctorNatTrans (lerayRestriction R v)

private theorem natTrans_ext_kInjectives
    {A E : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Abelian.HasKInjectiveResolutions A] [Category E]
    {F G : DerivedCategory A ⥤ E} (α β : F ⟶ G)
    (h : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      α.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)) =
        β.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) : α = β := by
  ext X
  let Q := HomotopyCategory.KInjectives.Qh (C := A)
  obtain ⟨I, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := Q) X
  obtain ⟨I, hI, rfl⟩ := I.mk_surjective
  have hi : α.app (Q.obj (.mk I)) = β.app (Q.obj (.mk I)) := h I
  apply (cancel_epi (F.map e.hom)).mp
  rw [α.naturality, β.naturality, hi]

private theorem compUnit_app
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    (X : HomotopyCategory A (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app X =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) := by
  have hi := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).inv_hom_id_app X
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
  simp [Functor.rightDerivedFunctorCompUnit, hi]

private theorem derivedNatTrans_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (τ : F ⟶ G)
    (X : HomotopyCategory A (.up ℤ)) :
    F.rightDerivedFunctorUnit.app X ≫
        (Functor.rightDerivedFunctorNatTrans τ).app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app X) ≫
        G.rightDerivedFunctorUnit.app X :=
  Functor.rightDerivedNatTrans_app _ _ _ _ (HomotopyCategory.quasiIso A (.up ℤ)) _ _

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.rightDerivedFunctorCompUnit Functor.rightDerivedFunctorNatTrans

private theorem mapHomotopy_whiskerLeft_app
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    (F : A ⥤ B) {G G' : B ⥤ E} [F.Additive] [G.Additive] [G'.Additive]
    (τ : G ⟶ G') (X : HomotopyCategory A (.up ℤ)) :
    (NatTrans.mapHomotopyCategory (Functor.whiskerLeft F τ) (.up ℤ)).app X =
      (NatTrans.mapHomotopyCategory τ (.up ℤ)).app
        ((F.mapHomotopyCategory (.up ℤ)).obj X) := by
  obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rfl

private theorem compUnit_naturality
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) {G G' : B ⥤ E} [F.Additive] [G.Additive] [G'.Additive]
    (τ : G ⟶ G') (X : HomotopyCategory A (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app X ≫
        (Functor.rightDerivedFunctorNatTrans τ).app
          (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj X)) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (Functor.whiskerLeft F τ) (.up ℤ)).app X) ≫
        (Functor.rightDerivedFunctorCompUnit F G').app X := by
  simp only [compUnit_app, Category.assoc]
  erw [(Functor.rightDerivedFunctorNatTrans τ).naturality]
  erw [← Category.assoc, derivedNatTrans_unit, Category.assoc,
    mapHomotopy_whiskerLeft_app]

private theorem iso_square_of_units
    {C D E : Type*} [Category C] [Category D] [Category E]
    {S T : C ⥤ E} {L : C ⥤ D} {RS RT P Q : D ⥤ E}
    (η : S ⟶ L ⋙ RS) (θ : T ⟶ L ⋙ RT)
    (W : MorphismProperty C) [L.IsLocalization W] [RS.IsRightDerivedFunctor η W]
    (e : P ≅ RS) (e' : Q ≅ RT) (ρ : P ⟶ Q) (δ : RS ⟶ RT) (σ : S ⟶ T)
    (ηP : S ⟶ L ⋙ P) (ηQ : T ⟶ L ⋙ Q)
    (hP : η ≫ Functor.whiskerLeft L e.inv = ηP)
    (hQ : θ ≫ Functor.whiskerLeft L e'.inv = ηQ)
    (hδ : η ≫ Functor.whiskerLeft L δ = σ ≫ θ)
    (hρ : ηP ≫ Functor.whiskerLeft L ρ = σ ≫ ηQ) :
    ρ ≫ e'.hom = e.hom ≫ δ := by
  apply (cancel_epi e.inv).mp
  apply (cancel_mono e'.inv).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id]
  apply RS.rightDerived_ext η W
  calc
    η ≫ Functor.whiskerLeft L (e.inv ≫ ρ) =
        ηP ≫ Functor.whiskerLeft L ρ := by
      rw [Functor.whiskerLeft_comp, ← Category.assoc, hP]
    _ = σ ≫ ηQ := hρ
    _ = η ≫ Functor.whiskerLeft L (δ ≫ e'.inv) := by
      rw [Functor.whiskerLeft_comp, ← Category.assoc, hδ, Category.assoc, hQ]

private theorem exists_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    {S : C ⥤ E} {L : C ⥤ D} {R P : D ⥤ E}
    (η : S ⟶ L ⋙ R) (θ : S ⟶ L ⋙ P)
    (W : MorphismProperty C) [L.IsLocalization W]
    [R.IsRightDerivedFunctor η W] [P.IsRightDerivedFunctor θ W] :
    ∃ e : P ≅ R, ∀ X, η.app X ≫ e.inv.app (L.obj X) = θ.app X := by
  refine ⟨(Functor.rightDerivedUnique R P η θ W).symm, ?_⟩
  intro X
  exact (Functor.rightDerivedNatTrans_app _ _ _ _ W (𝟙 _) X).trans (by simp)

private theorem derivedComp_of_unitIso
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    (hG : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      IsIso (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj I)))) :
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor
      (Functor.rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso A (.up ℤ)) := by
  let h := HomotopyCategory.KInjectives.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  apply h.isRightDerivedFunctor_of_isIso
  intro X
  obtain ⟨I, hI, rfl⟩ := X.mk_surjective
  change IsIso ((Functor.rightDerivedFunctorCompUnit F G).app
    ((HomotopyCategory.quotient _ _).obj I))
  have := hG I
  rw [compUnit_app]
  infer_instance

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
  (u : D ⥤ C) [u.IsContinuous K J]
  (a : B ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj A)

/-- The canonical sectionwise module direct image, with scalar restriction induced by a.
This is an abbreviation of the recorded localization interface, not a new lift of
an underlying functor. Source: Stacks Project, Tag 0D6H and Modules on Sites, Tag 04J0
(blueprint: lem-sfb-ringed-site-unbounded-leray-sections). -/
abbrev lerayDirectImage :=
  SheafOfModules.pushforward.{u} (sectionModuleMap u a)

/-- The canonical identity of underived abelian section functors.
Source: Stacks Project, Tag 0D6H
(blueprint: lem-sfb-ringed-site-unbounded-leray-sections). -/
def leraySectionFunctorIdentity (V : D) :
    lerayDirectImage A B u a ⋙
      sectionEvaluation ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) V ≅
    sectionEvaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (u.obj V) :=
  Iso.refl _

/-- The ordinary site pushforward has literally the source's sections at u(V),
including every differential of an unbounded complex. The ring action before
forgetting scalars is restriction along the structural map a at V.
Source: Stacks Project, Tag 0D6H and Modules on Sites, Tag 04J0
(blueprint: lem-sfb-ringed-site-unbounded-leray-sections). -/
def leraySectionComplexIdentity (V : D)
    (I : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) ℤ) :
    ((sectionEvaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      (u.obj V)).mapHomologicalComplex (.up ℤ)).obj I ≅
    ((sectionEvaluation ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)
      V).mapHomologicalComplex (.up ℤ)).obj
        (((lerayDirectImage A B u a).mapHomologicalComplex (.up ℤ)).obj I) :=
  Iso.refl _

private theorem lerayEvaluationUnit_isIso
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)]
    [HasDerivedCategory.{wD} (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{u}]
    (I : CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) ℤ) [I.IsKInjective]
    (V : D) :
    IsIso ((sectionEvaluation ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)
      V).rightDerivedFunctorUnit.app
        (((lerayDirectImage A B u a).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj I))) := by
  let F := lerayDirectImage A B u a
  let G := sectionEvaluation ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) V
  obtain ⟨T, hT, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    ((F.mapHomologicalComplex (.up ℤ)).obj I)
  have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j) :=
    leraySectionResolution_quasiIso A B u a I T j V
  have hmap : IsIso (DerivedCategory.Qh.{wA}.map
      ((G.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient _ _).map j))) := by
    rw [Functor.mapHomotopyCategory_map]
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using
        (inferInstance : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map j))
  have hunit : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj T)) := inferInstance
  have hqj : IsIso (DerivedCategory.Qh.{wD}.map
      ((HomotopyCategory.quotient _ _).map j)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    simpa only [HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using hj
  have hnat := G.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ _).map j)
  dsimp only [Functor.comp_map] at hnat
  have hcomp : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        G.rightDerivedFunctor.map
          (DerivedCategory.Qh.{wD}.map ((HomotopyCategory.quotient _ _).map j))) := by
    rw [← hnat]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hcomp

set_option maxHeartbeats 400000 in
-- The normalized restriction square compares three independent derived-category universes.
/-- Canonical natural unbounded Leray isomorphisms at all site objects, compatible
with restriction and normalized by the derived units on K-injective representatives.
Source: Stacks Project, Cohomology on Sites, Tag 0D6H, second assertion
(blueprint: lem-sfb-ringed-site-unbounded-leray-sections).

Proof:
1. By prop-pur-kinjective-resolutions-exist choose a K-injective I representing E
and a K-injective resolution j : f_*I -> T. These compute Rf_*E and its derived
sections. No assertion that f_*I is K-injective is needed.
2. Localize at V and u(V) using lem-weil-pbc-localize-ringed-site-morphism.
Lemma lem-pur-kinjective-restrict-localized keeps both representatives K-injective;
lem-weil-pbc-finite-type-restriction-exact keeps j a quasi-isomorphism.
3. Constant sheafification is left adjoint to terminal sectionEvaluation on D/V by
lem-weil-pbc-constant-sheaf-maps-global-sections, and is left exact by
lem-weil-pbc-sheafification-sets-exact. The identity of B(V) therefore defines the
punctual ringed-topos morphism. The module comparison
lem-weil-pbc-singleton-site-module-comparison identifies its pushforward with sectionEvaluation.
4. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition to the localized
morphism and the punctual morphism. Its normalization says j(V) is a
quasi-isomorphism. Forgetting scalars preserves that property. Inverting its class
and composing the canonical resolution identifications gives the displayed comparison.
5. By lem-weil-pbc-kinjective-hom-derived, derived arrows are represented by maps
between K-injectives. The target comparison lift commutes with j up to homotopy;
sectionEvaluation preserves this homotopy. Thus the comparisons are natural in E and
independent of resolutions. The unit formula on every K-injective I determines them uniquely.
6. Naturality of j as a map of sheaves gives T(v) j(V) = j(V') I(u(v)).
Invert the localized j(V) to obtain exactly the final restriction square.
There is no boundedness, quasi-coherence, terminal-object or flatness assumption. -/
theorem unboundedLeraySections
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)]
    [HasDerivedCategory.{wC} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))]
    [HasDerivedCategory.{wD} (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{u}] :
    ∃! e : ∀ V : D,
      (lerayDirectImage A B u a).rightDerivedFunctor ⋙
        (sectionEvaluation ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)
          V).rightDerivedFunctor ≅
      (sectionEvaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
        (u.obj V)).rightDerivedFunctor,
      (∀ (I : CochainComplex (ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) ℤ) [I.IsKInjective]
        (V : D),
        HEq
          ((Functor.rightDerivedFunctorUnit.{u + 1, u + 1, u, u, wC, wA}
            (sectionEvaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
              (u.obj V))).app ((HomotopyCategory.quotient _ _).obj I) ≫
          (e V).inv.app
            (DerivedCategory.Qh.{wC}.obj ((HomotopyCategory.quotient _ _).obj I)))
          (DerivedCategory.Qh.{wA}.map
            ((NatTrans.mapHomotopyCategory
              (leraySectionFunctorIdentity A B u a V).inv (.up ℤ)).app
                ((HomotopyCategory.quotient _ _).obj I)) ≫
          (Functor.rightDerivedFunctorCompUnit.{u, u, u, u + 1, u + 1, u + 1, wC, wD, wA}
            (lerayDirectImage A B u a)
            (sectionEvaluation ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) V)).app
              ((HomotopyCategory.quotient _ _).obj I))) ∧
      ∀ (V' V : D) (v : V' ⟶ V),
        Functor.whiskerLeft
            (lerayDirectImage A B u a).rightDerivedFunctor
            (lerayDerivedRestriction ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) v) ≫
          (e V').hom =
        (e V).hom ≫
          lerayDerivedRestriction ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
            (u.map v) := by
  classical
  let F := lerayDirectImage A B u a
  let G (V : D) :=
    sectionEvaluation ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) V
  let H (V : D) :=
    sectionEvaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (u.obj V)
  let W := HomotopyCategory.quasiIso
    (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) (.up ℤ)
  have hd (V : D) : (F.rightDerivedFunctor ⋙ (G V).rightDerivedFunctor).IsRightDerivedFunctor
      (Functor.rightDerivedFunctorCompUnit F (G V)) W := by
    apply derivedComp_of_unitIso F (G V)
    intro I hI
    dsimp only [F, G]
    exact lerayEvaluationUnit_isIso A B u a I V
  have hex (V : D) := exists_comparison (H V).rightDerivedFunctorUnit
    (Functor.rightDerivedFunctorCompUnit F (G V)) W
  choose e he using hex
  refine ⟨e, ⟨?_, ?_⟩, ?_⟩
  · intro I hI V
    apply heq_of_eq
    change _ = DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory (𝟙 _) (.up ℤ)).app _) ≫ _
    simpa only [NatTrans.mapHomotopyCategory_id, NatTrans.id_app, Functor.map_id,
      Category.id_comp] using he V ((HomotopyCategory.quotient _ _).obj I)
  · intro V' V v
    let τ : G V ⟶ G V' :=
      lerayRestriction ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) v
    let σ : H V ⟶ H V' := lerayRestriction ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      (u.map v)
    change Functor.whiskerLeft F.rightDerivedFunctor (Functor.rightDerivedFunctorNatTrans τ) ≫
      (e V').hom = (e V).hom ≫ Functor.rightDerivedFunctorNatTrans σ
    apply iso_square_of_units (H V).rightDerivedFunctorUnit
      (H V').rightDerivedFunctorUnit W (e V) (e V') _ _
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory σ (.up ℤ)) DerivedCategory.Qh)
      (Functor.rightDerivedFunctorCompUnit F (G V))
      (Functor.rightDerivedFunctorCompUnit F (G V'))
    · ext X
      exact he V X
    · ext X
      exact he V' X
    · ext X
      exact derivedNatTrans_unit σ X
    · ext X
      exact compUnit_naturality F τ X
  · intro e' he'
    funext V
    apply Iso.ext_inv
    apply natTrans_ext_kInjectives
    intro I hI
    apply (cancel_epi ((H V).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I))).mp
    have h := eq_of_heq (he'.1 I V)
    change _ = DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory (𝟙 _) (.up ℤ)).app _) ≫ _ at h
    simp only [NatTrans.mapHomotopyCategory_id, NatTrans.id_app, Functor.map_id,
      Category.id_comp] at h
    exact h.trans (he V ((HomotopyCategory.quotient _ _).obj I)).symm

end CategoryTheory.UnboundedSectionsLocalization
