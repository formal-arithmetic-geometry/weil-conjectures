/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.TraceFormula.OrientedPointCohomology
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.Comma
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.Paper.OrientedConstructibleSheafVanishing
import Sheaf.Paper.ConstructibleVanishingCanonicalStrata
import Sheaf.Paper.PsiConstructibilityDescent
import Sheaf.TraceFormula.PsiProperSurjectiveConstructibility

/-!
# Constructible strata for Psi-good oriented nearby-cycle cohomology

Source: Lu--Zheng, Duality and nearby cycles over general bases, Theorem 4.27(2)
and the following definition of constructibility, v7 author PDF
(blueprint: lem-trf-psi-good-oriented-cohomology-strata).

The canonical site, scalar and stratum transports below connect the recorded nearby-cycle
functor to the recorded constructible sheaf and stratification interfaces. All constructions
have real data. Only the theorem and named properties of the transports are postponed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.OrientedNearbyCycles CategoryTheory.AdicSites

namespace AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata

private def productConeIsLimit {C D J : Type*} [Category C] [Category D]
    [Category J] {F : J ⥤ C × D} {c : Cone F}
    (hc : IsLimit ((CategoryTheory.Prod.fst C D).mapCone c))
    (hd : IsLimit ((CategoryTheory.Prod.snd C D).mapCone c)) : IsLimit c where
  lift t := (hc.lift ((CategoryTheory.Prod.fst C D).mapCone t),
    hd.lift ((CategoryTheory.Prod.snd C D).mapCone t))
  fac t j := Prod.ext (hc.fac _ j) (hd.fac _ j)
  uniq t m hm := by
    apply Prod.ext
    · exact hc.uniq ((CategoryTheory.Prod.fst C D).mapCone t) m.1
        (fun j ↦ congrArg (fun a ↦ a.1) (hm j))
    · exact hd.uniq ((CategoryTheory.Prod.snd C D).mapCone t) m.2
        (fun j ↦ congrArg (fun a ↦ a.2) (hm j))

private theorem productHasFiniteLimits {C D : Type*} [Category C] [Category D]
    [HasFiniteLimits C] [HasFiniteLimits D] : HasFiniteLimits (C × D) := by
  constructor
  intro J _ _
  constructor
  intro F
  let c : Cone F :=
    { pt := (limit (F ⋙ CategoryTheory.Prod.fst C D),
        limit (F ⋙ CategoryTheory.Prod.snd C D))
      π :=
        { app := fun j ↦ (limit.π _ j, limit.π _ j)
          naturality := by
            intro i j h
            apply Prod.ext
            · simpa using (limit.w (F ⋙ CategoryTheory.Prod.fst C D) h).symm
            · simpa using (limit.w (F ⋙ CategoryTheory.Prod.snd C D) h).symm } }
  exact ⟨⟨c, productConeIsLimit (limit.isLimit _) (limit.isLimit _)⟩⟩

private theorem pairPreservesFiniteLimits {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : C ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F.prod' G) := by
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  exact ⟨productConeIsLimit (isLimitOfPreserves F hc) (isLimitOfPreserves G hc)⟩

private def productLimitCone {C D J : Type*} [Category C] [Category D]
    [Category J] (F : J ⥤ C × D)
    [HasLimit (F ⋙ CategoryTheory.Prod.fst C D)]
    [HasLimit (F ⋙ CategoryTheory.Prod.snd C D)] : Cone F where
  pt := (limit (F ⋙ CategoryTheory.Prod.fst C D),
    limit (F ⋙ CategoryTheory.Prod.snd C D))
  π :=
    { app := fun j ↦ (limit.π _ j, limit.π _ j)
      naturality := by
        intro i j h
        apply Prod.ext
        · simpa using (limit.w (F ⋙ CategoryTheory.Prod.fst C D) h).symm
        · simpa using (limit.w (F ⋙ CategoryTheory.Prod.snd C D) h).symm }

private theorem productProjectionsPreserveFiniteLimits {C D : Type*}
    [Category C] [Category D] [HasFiniteLimits C] [HasFiniteLimits D] :
    PreservesFiniteLimits (CategoryTheory.Prod.fst C D) ∧
      PreservesFiniteLimits (CategoryTheory.Prod.snd C D) := by
  constructor <;> constructor <;> intro J _ _ <;> constructor <;> intro F
  · exact preservesLimit_of_preserves_limit_cone
      (productConeIsLimit (c := productLimitCone F) (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)
  · exact preservesLimit_of_preserves_limit_cone
      (productConeIsLimit (c := productLimitCone F) (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)

private theorem commaProjectionsPreserveFiniteLimits {A B T : Type*}
    [Category A] [Category B] [Category T] [HasFiniteLimits A] [HasFiniteLimits B]
    (L : A ⥤ T) (R : B ⥤ T) [PreservesFiniteLimits R] :
    PreservesFiniteLimits (Comma.fst L R) ∧ PreservesFiniteLimits (Comma.snd L R) := by
  constructor <;> constructor <;> intro J _ _ <;> constructor <;> intro F
  · exact preservesLimit_of_preserves_limit_cone
      (Comma.coneOfPreservesIsLimit F (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)
  · exact preservesLimit_of_preserves_limit_cone
      (Comma.coneOfPreservesIsLimit F (limit.isLimit _) (limit.isLimit _))
      (limit.isLimit _)

private theorem commaMapPreservesFiniteLimits
    {A B T A' B' T' : Type*}
    [Category A] [Category B] [Category T] [Category A'] [Category B'] [Category T']
    [HasFiniteLimits A] [HasFiniteLimits B]
    {L : A ⥤ T} {R : B ⥤ T} {L' : A' ⥤ T'} {R' : B' ⥤ T'}
    {F₁ : A ⥤ A'} {F₂ : B ⥤ B'} {F : T ⥤ T'}
    [PreservesFiniteLimits R] [PreservesFiniteLimits R']
    [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂]
    (α : F₁ ⋙ L' ⟶ L ⋙ F) (β : R ⋙ F ⟶ F₂ ⋙ R') :
    PreservesFiniteLimits (Comma.map α β) := by
  have := (commaProjectionsPreserveFiniteLimits L R).1
  have := (commaProjectionsPreserveFiniteLimits L R).2
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  exact ⟨Comma.fstSndJointlyReflectLimit
    (isLimitOfPreserves (Comma.fst L R ⋙ F₁) hc)
    (isLimitOfPreserves (Comma.snd L R ⋙ F₂) hc)⟩

private theorem imagePullback {C D : Type*} [Category C] [Category D]
    [HasFiniteLimits C] [HasFiniteLimits D] (F : C ⥤ D) [PreservesFiniteLimits F]
    {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    (S.pullback f).functorPushforward F = (S.functorPushforward F).pullback (F.map f) := by
  apply le_antisymm (Sieve.functorPushforward_pullback_le F f S)
  intro W g hg
  obtain ⟨Z, h, k, hh, hk⟩ := hg
  let t : W ⟶ F.obj (pullback h f) :=
    pullback.lift k g hk.symm ≫ inv (pullbackComparison F h f)
  have ht₂ : t ≫ F.map (pullback.snd h f) = g := by
    dsimp [t]
    rw [Category.assoc, ← pullbackComparison_comp_snd, IsIso.inv_hom_id_assoc,
      pullback.lift_snd]
  refine ⟨pullback h f, pullback.snd h f, t, ?_, ht₂.symm⟩
  change S (pullback.snd h f ≫ f)
  rw [← pullback.condition]
  exact S.downward_closed hh (pullback.fst h f)

private theorem continuousOfGenerators {C D : Type*} [Category C] [Category D]
    [HasFiniteLimits C] [HasFiniteLimits D] (F : C ⥤ D) [PreservesFiniteLimits F]
    (J : Precoverage C) (K : GrothendieckTopology D)
    (h : ∀ (X : C) (R : Presieve X), R ∈ J X →
      (Sieve.generate R).functorPushforward F ∈ K (F.obj X)) :
    F.IsContinuous J.toGrothendieck K := by
  apply Functor.le_inducedTopology_iff.mp
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro X R hR
  change Sieve.generate R ∈ F.inducedTopology K X
  apply Sheaf.mem_finestTopology_of_forall_isSheafFor
  rintro _ ⟨G, rfl⟩ Y f
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks,
    Presieve.isSheafFor_iff_generate, Sieve.generate_map_eq_functorPushforward,
    Sieve.generate_sieve, imagePullback]
  exact (isSheaf_iff_isSheaf_of_type _ _).1 G.property _
    (K.pullback_stable (F.map f) (h X R hR))

/-- Fixed-ring coefficients of a module over the constant commutative ring sheaf.
Use the existing canonical CommRingCat-to-RingCat coefficient identification and the
recorded constant-ring module restriction, retaining the original module action.
Source: Stacks 03CY; Lu--Zheng, definition after Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def fixedSheaf (S : Site.{u}) (A : Type u) [CommRing A] (M : S.modules A) :
    Sheaf S.topology (ModuleCat.{u} A) :=
  (constantRingModuleRestriction S.topology A).obj
    ((SheafOfModules.restrictScalars (realizationRingIso S.topology A).inv).obj M)

/-- The inverse of the existing transported-site equivalence is continuous.
Source: ILO XI §4.3; Stacks 00X6
(blueprint: lem-trf-psi-good-oriented-cohomology-strata).
Proof: etaleTopology is the topology induced by AsSmall.down. The inverse equivalence
AsSmall.up carries an etale cover to that induced cover. Applying AsSmall.down to its
image recovers the original cover, so the covering-sieve sheaf condition is unchanged. -/
theorem upContinuous (X : Scheme.{u}) :
    (AsSmall.up : X.Etale ⥤ EtaleSite.{u, u + 1} X).IsContinuous
      X.smallEtaleTopology (etaleTopology X) := by
  change (AsSmall.equiv (C := X.Etale)).functor.IsContinuous X.smallEtaleTopology
    ((AsSmall.equiv (C := X.Etale)).inverse.inducedTopology X.smallEtaleTopology)
  infer_instance

attribute [instance] upContinuous

/-- Read the existing constant-ring module sheaf on the original small etale site.
The AsSmall equivalence and fixedSheaf perform only canonical site and scalar transport.
Source: Stacks 03CY; ILO XI §4.3
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def etaleFixed (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    (L : (etaleDatum.{u, u + 1} X).modules A) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  ((AsSmall.up : X.Etale ⥤ EtaleSite.{u, u + 1} X).sheafPushforwardContinuous
    (ModuleCat.{u + 1} A) X.smallEtaleTopology (etaleTopology X)).obj
      (fixedSheaf (etaleDatum X) A L)

set_option backward.isDefEq.respectTransparency false in
private theorem constantScalarsComparison (S : Site.{u}) (A : Type u) [CommRing A] :
    toSheafify S.topology ((Functor.const S.objectsᵒᵖ).obj (RingCat.of A)) ≫
      (realizationRingIso S.topology A).inv.hom = realizationRingUnit S.topology A := by
  have hfac : realizationRingUnit S.topology A ≫
      (realizationRingIso S.topology A).hom.hom =
      toSheafify S.topology ((Functor.const S.objectsᵒᵖ).obj (RingCat.of A)) := by
    dsimp only [realizationRingIso, Iso.app_hom]
    rw [constantCommuteCompose_hom_app_hom]
    unfold realizationRingUnit
    rw [← Category.assoc, sheafComposeIso_inv_fac]
    exact (toSheafify_naturality S.topology
      (Functor.constComp S.objectsᵒᵖ (CommRingCat.of A)
        (forget₂ CommRingCat RingCat)).hom).symm.trans (by rfl)
  rw [← hfac, Category.assoc]
  have hi := congrArg (fun t ↦ t.hom) (realizationRingIso S.topology A).hom_inv_id
  change (realizationRingIso S.topology A).hom.hom ≫
    (realizationRingIso S.topology A).inv.hom = 𝟙 _ at hi
  rw [hi, Category.comp_id]

private def constantModulePresheaf {C : Type u} [SmallCategory C]
    (A : Type u) [CommRing A]
    (M : PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of A))) :
    Cᵒᵖ ⥤ ModuleCat.{u} A where
  obj := M.obj
  map := M.map
  map_id := by intro U; ext x; exact congrArg (fun t ↦ t x) (M.map_id U)
  map_comp := by intro U V W k l; ext x; exact M.map_comp_apply k l x

private def initialSectionsIso {C : Type u} [SmallCategory C]
    (A : Type u) [CommRing A]
    (M : PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of A)))
    (U : Cᵒᵖ) (hU : IsInitial U) :
    (PresheafOfModules.forgetToPresheafModuleCat U hU).obj M ≅
      constantModulePresheaf A M := by
  refine NatIso.ofComponents
    (fun V ↦ (ModuleCat.restrictScalarsId A).app (M.obj V)) ?_
  intro V W k
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
private def sectionsIsoFixedAt (S : Site.{u}) (A : Type u) [CommRing A]
    (M : S.modules A) (U : S.objectsᵒᵖ) (hU : IsInitial U) :
    (PresheafOfModules.forgetToPresheafModuleCat U hU).obj
        ((PresheafOfModules.restrictScalars (realizationRingUnit S.topology A)).obj M.val) ≅
      (fixedSheaf S A M).obj := by
  let P := (PresheafOfModules.restrictScalars (realizationRingUnit S.topology A)).obj M.val
  have he : constantModulePresheaf A P = (fixedSheaf S A M).obj := by
    change constantModulePresheaf A
        ((PresheafOfModules.restrictScalars (realizationRingUnit S.topology A)).obj M.val) =
      constantModulePresheaf A
        ((PresheafOfModules.restrictScalars
          (toSheafify S.topology ((Functor.const S.objectsᵒᵖ).obj (RingCat.of A)) ≫
            (realizationRingIso S.topology A).inv.hom)).obj M.val)
    rw [constantScalarsComparison S]
  exact initialSectionsIso A P U hU ≪≫ eqToIso he

private def sectionsIsoFixed (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (M : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ)) :
    orgogozoModuleSections X Λ M ≅ (fixedSheaf (etaleDatum X) (Coeff Λ) M).obj := by
  letI : HasFiniteLimits (etaleDatum.{u, u + 1} X).objects := etaleSite_hasFiniteLimits X
  exact sectionsIsoFixedAt (etaleDatum X) (Coeff Λ) M
    (op (⊤_ (etaleDatum.{u, u + 1} X).objects)) terminalIsTerminal.op

private def fixedFunctor (S : Site.{u}) (A : Type u) [CommRing A] :
    S.modules A ⥤ Sheaf S.topology (ModuleCat.{u} A) :=
  SheafOfModules.restrictScalars (realizationRingIso S.topology A).inv ⋙
    constantRingModuleRestriction S.topology A

private instance fixedFunctor_additive (S : Site.{u}) (A : Type u) [CommRing A] :
    (fixedFunctor S A).Additive where
  map_add := by intros; ext U x; rfl

private def etaleFixedFunctor (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (etaleDatum.{u, u + 1} X).modules A ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  fixedFunctor (etaleDatum X) A ⋙
    (AsSmall.up : X.Etale ⥤ EtaleSite.{u, u + 1} X).sheafPushforwardContinuous
      (ModuleCat.{u + 1} A) X.smallEtaleTopology (etaleTopology X)

private instance etaleFixedFunctor_additive (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] : (etaleFixedFunctor X A).Additive where
  map_add := by intros; ext U x; rfl

private def sectionsIsoSmall (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (M : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ)) :
    orgogozoModuleSections X Λ M ≅
      (AsSmall.down : EtaleSite.{u, u + 1} X ⥤ X.Etale).op ⋙
        (etaleFixed X (Coeff Λ) M).obj :=
  sectionsIsoFixed X Λ M ≪≫ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (AsSmall.equiv (C := X.Etale)).counitIso) _

/-- The already defined two-map oriented product, in the common coefficient universe.
This is an abbreviation of the published datum, with no new topology.
Source: ILO XI §1.1; Lu--Zheng, definition following Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
abbrev productSite {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :=
  CategoryTheory.OrientedPointCohomology.datum.{u, u} a b

/-- Canonical base-change associativity for the two outer entries of a triple.
The middle etale S-scheme stays fixed. The first arrow uses etaleBaseChangeComp and
the second arrow is the identity on its pullback along j.
Source: ILO XI §1.9; Lu--Zheng, definition following Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def restrictBeta {X S X' S' : Scheme.{u}} (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    (etaleBaseChange.{u, u + 1} f).prod' (𝟭 (EtaleSite S)) ⋙
        (etaleBaseChange i).prod (etaleBaseChange j) ⟶
      𝟭 (EtaleSite S) ⋙ (etaleBaseChange (i ≫ f)).prod' (etaleBaseChange j) where
  app V := ((etaleBaseChangeComp i f).inv.app V, 𝟙 _)
  naturality := fun V W h ↦ Prod.ext ((etaleBaseChangeComp i f).inv.naturality h)
    (by simp)

/-- Pull back the outer entries of (U to V from W) along i and j, keeping V.
Comma.map gives the actual action on objects and arrows, using canonical fibre-product
associativity. This is the site inverse image of the oriented stratum morphism.
Source: ILO XI §§1.6, 1.9; Lu--Zheng, definition following Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def restrictSite {X S X' S' : Scheme.{u}} (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    (vanishingDatum.{u, u + 1} f).objects ⥤ (productSite (i ≫ f) j).objects :=
  Comma.map
    ((Functor.rightUnitor ((etaleBaseChange i).prod (etaleBaseChange j)) ≪≫
      (Functor.leftUnitor ((etaleBaseChange i).prod (etaleBaseChange j))).symm).hom)
    (restrictBeta f i j)


/-- The canonical stratum site inverse image is continuous and left exact.
Source: ILO XI §§1.1, 1.6, 1.9
(blueprint: lem-trf-psi-good-oriented-cohomology-strata).
Proof: limits of triples are computed componentwise; scheme base change preserves
finite limits and the associativity comparisons identify the structural arrows.
Coverings of types (a) and (b) pull back to etale coverings. A type-(c) arrow remains
type (c), since its defining cartesian square remains cartesian after base change.
Thus all generating covers are preserved. The finite-limit cover-preservation criterion
of Stacks 00X6 gives continuity for their generated topologies. On the two projections
and the middle triple this functor gives the immersions and their orientation; hence,
by lem-trf-oriented-product-universal, its geometric morphism is the required lift. -/
theorem restrictSite_properties {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    (restrictSite f i j).IsContinuous (vanishingTopology.{u, u + 1} f)
      (productSite (i ≫ f) j).topology ∧ PreservesFiniteLimits (restrictSite f i j) := by
  have := productHasFiniteLimits (C := EtaleSite.{u, u + 1} X)
    (D := EtaleSite.{u, u + 1} S)
  have := pairPreservesFiniteLimits (etaleBaseChange.{u, u + 1} f)
    (𝟭 (EtaleSite.{u, u + 1} S))
  have := pairPreservesFiniteLimits (etaleBaseChange.{u, u + 1} (i ≫ f))
    (etaleBaseChange.{u, u + 1} j)
  have := (productProjectionsPreserveFiniteLimits
    (C := EtaleSite.{u, u + 1} X) (D := EtaleSite.{u, u + 1} S)).1
  have := (productProjectionsPreserveFiniteLimits
    (C := EtaleSite.{u, u + 1} X) (D := EtaleSite.{u, u + 1} S)).2
  have : PreservesFiniteLimits ((etaleBaseChange.{u, u + 1} i).prod
      (etaleBaseChange.{u, u + 1} j)) :=
    pairPreservesFiniteLimits
      (CategoryTheory.Prod.fst _ _ ⋙ etaleBaseChange i)
      (CategoryTheory.Prod.snd _ _ ⋙ etaleBaseChange j)
  have hlim : PreservesFiniteLimits (restrictSite f i j) :=
    commaMapPreservesFiniteLimits _ _
  have := hlim
  have : HasFiniteLimits (vanishingDatum.{u, u + 1} f).objects := by
    change HasFiniteLimits
      (Comma (𝟭 _) ((etaleBaseChange.{u, u + 1} f).prod' (𝟭 _)))
    infer_instance
  have := productHasFiniteLimits (C := EtaleSite.{u, u + 1} X')
    (D := EtaleSite.{u, u + 1} S')
  have : HasFiniteLimits (productSite (i ≫ f) j).objects := by
    change HasFiniteLimits
      (Comma (𝟭 _) ((etaleBaseChange.{u, u + 1} (i ≫ f)).prod'
        (etaleBaseChange.{u, u + 1} j)))
    infer_instance
  refine ⟨?_, hlim⟩
  apply continuousOfGenerators (restrictSite f i j)
    (OrientedProduct.generators (etaleTopology X).toPretopology
      (etaleTopology S).toPretopology (etaleBaseChange f) (𝟭 _))
  intro Z R hR
  rw [← Sieve.generate_map_eq_functorPushforward]
  rcases hR with ⟨I, Zi, r, rfl, ha | hb⟩ | ⟨Z', r, rfl, hi, hr⟩
  · rw [Presieve.map_ofArrows]
    apply (OrientedProduct.largeGenerators (etaleTopology X').toPretopology
      (etaleTopology S').toPretopology (etaleBaseChange (i ≫ f))
      (etaleBaseChange j)).generate_mem_toGrothendieck
    refine Or.inl ⟨I, _, _, rfl, Or.inl ⟨?_, ?_⟩⟩
    · change Sieve.generate (Presieve.ofArrows
        (fun a ↦ (etaleBaseChange i).obj (Zi a).left.1)
        (fun a ↦ (etaleBaseChange i).map (r a).left.1)) ∈ etaleTopology X' _
      rw [← Presieve.map_ofArrows, Sieve.generate_map_eq_functorPushforward]
      exact (CoverPreserving.of_isContinuous (etaleBaseChange i)
        (etaleTopology X) (etaleTopology X')).cover_preserve ha.1
    · intro a
      have := (ha.2 a).1
      have := (ha.2 a).2
      change IsIso (r a).right ∧ IsIso ((etaleBaseChange j).map (r a).left.2)
      exact ⟨inferInstance, inferInstance⟩
  · rw [Presieve.map_ofArrows]
    apply (OrientedProduct.largeGenerators (etaleTopology X').toPretopology
      (etaleTopology S').toPretopology (etaleBaseChange (i ≫ f))
      (etaleBaseChange j)).generate_mem_toGrothendieck
    refine Or.inl ⟨I, _, _, rfl, Or.inr ⟨?_, ?_⟩⟩
    · change Sieve.generate (Presieve.ofArrows
        (fun a ↦ (etaleBaseChange j).obj (Zi a).left.2)
        (fun a ↦ (etaleBaseChange j).map (r a).left.2)) ∈ etaleTopology S' _
      rw [← Presieve.map_ofArrows, Sieve.generate_map_eq_functorPushforward]
      exact (CoverPreserving.of_isContinuous (etaleBaseChange j)
        (etaleTopology S) (etaleTopology S')).cover_preserve hb.1
    · intro a
      have := (hb.2 a).1
      have := (hb.2 a).2
      change IsIso (r a).right ∧ IsIso ((etaleBaseChange i).map (r a).left.1)
      exact ⟨inferInstance, inferInstance⟩
  · rw [Presieve.map_singleton]
    apply (OrientedProduct.largeGenerators (etaleTopology X').toPretopology
      (etaleTopology S').toPretopology (etaleBaseChange (i ≫ f))
      (etaleBaseChange j)).generate_mem_toGrothendieck
    have := hi
    refine Or.inr ⟨_, _, rfl, ?_, ?_⟩
    · change IsIso ((etaleBaseChange i).map r.left.1)
      infer_instance
    · simpa [restrictSite, restrictBeta] using
        (etaleBaseChange j).map_isPullback hr
/-- Continuity supplied by the canonical stratum functor's property theorem.
Source: ILO XI §1.9 (blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
instance restrictSite_continuous {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    (restrictSite f i j).IsContinuous (vanishingTopology.{u, u + 1} f)
      (productSite (i ≫ f) j).topology := (restrictSite_properties f i j).1
/-- Left exactness supplied by the canonical stratum functor's property theorem.
Source: ILO XI §1.9 (blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
instance restrictSite_finiteLimits {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :
    PreservesFiniteLimits (restrictSite f i j) := (restrictSite_properties f i j).2

/-- Finite limits on the existing vanishing site's comma category.
Source: ILO XI §1.1 (blueprint: lem-trf-psi-good-oriented-cohomology-strata).
Proof: take finite limits in each of the three etale entries. Base change along f and
the identity preserve these limits, so the two structural arrows into the middle entry
induce the structural arrows of the limit triple. Its three projections determine
unique compatible maps from every cone, proving the comma universal property. -/
theorem vanishing_finiteLimits {X S : Scheme.{u}} (f : X ⟶ S) :
    HasFiniteLimits (VanishingSite.{u, u + 1} f) := by
  change HasFiniteLimits
    (Comma (𝟭 _) ((etaleBaseChange.{u, u + 1} f).prod' (𝟭 _)))
  have := productHasFiniteLimits (C := EtaleSite.{u, u + 1} X)
    (D := EtaleSite.{u, u + 1} S)
  have := pairPreservesFiniteLimits (etaleBaseChange.{u, u + 1} f)
    (𝟭 (EtaleSite.{u, u + 1} S))
  infer_instance
attribute [instance] vanishing_finiteLimits

/-- The existing finite-limit structure on the published two-map oriented triple site.
Source: ILO XI §1.1 (blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
instance product_finiteLimits {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    HasFiniteLimits (productSite a b).objects :=
  CategoryTheory.OrientedPointCohomology.triples_finiteLimits a b

/-- The canonical oriented stratum restriction, lifted to constant-ring modules.
Use siteMorphism and the existing canonical moduleMorphism, whose modulePull is exact.
Source: ILO XI §1.9; Stacks 03D2; Lu--Zheng, definition following Theorem 4.27
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
def restrictionModules {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (i : X' ⟶ X) (j : S' ⟶ S) :=
  letI := (restrictSite_properties f i j).1
  letI := (restrictSite_properties f i j).2
  moduleMorphism (vanishingDatum.{u, u + 1} f) (productSite (i ≫ f) j)
    (siteMorphism (vanishingTopology.{u, u + 1} f) (productSite (i ≫ f) j).topology
      (restrictSite f i j))

/-- The sheaf L in degree zero, using the same standard localization as nearbyCycles.
Coeff is the recorded canonical ULift of Lambda; no coefficient ring is changed.
Source: Lu--Zheng, Theorem 4.27(2), degree-zero specialization
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
abbrev degreeZero (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (L : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ)) :
    EtaleDerived X Λ :=
  (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj L

/-- The q-th cohomology sheaf of the recorded nearby-cycle functor on L[0].
Source: Lu--Zheng, Theorem 4.27(2)
(blueprint: lem-trf-psi-good-oriented-cohomology-strata). -/
abbrev cohomology {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [CommRing Λ]
    (L : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ)) (q : ℤ) :=
  (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).obj
    ((nearbyCycles f Λ).obj (degreeZero X Λ L))


private def stratificationWithConstructible {X : Scheme.{u}}
    (A : X.FiniteLocallyClosedStratification)
    (hA : ∀ a : Fin A.n, Topology.IsConstructible (A.stratum a)) :
    Scheme.Stratification X where
  n := A.n
  stratum := A.stratum
  isLocallyClosed_stratum := A.isLocallyClosed_stratum
  iUnion_stratum_eq_univ := A.iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := A.pairwise_disjoint_stratum
  isConstructible_stratum := hA
  domain := A.domain
  immersion := A.immersion
  isImmersion := A.isImmersion
  range_immersion := A.range_immersion

private theorem constructibleVanishing_of_iso {X S : Scheme.{u}} (f : X ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {F G : (vanishingDatum.{u, u + 1} f).modules (Coeff.{u, u + 1} Λ)}
    (e : F ≅ G) (h : OrientedConstructibleSheaf.IsConstructibleVanishing f Λ G) :
    OrientedConstructibleSheaf.IsConstructibleVanishing f Λ F := by
  obtain ⟨A, B, hA, hB, h⟩ := h
  refine ⟨A, B, hA, hB, ?_⟩
  intro a b U
  obtain ⟨R, hR, h⟩ := h a b U
  refine ⟨R, hR, ?_⟩
  intro V k hk
  obtain ⟨M, hM, ⟨eM⟩⟩ := h V k hk
  refine ⟨M, hM, ⟨(SheafOfModules.overFunctor _ V).mapIso ?_ ≪≫ eM⟩⟩
  exact (OrientedConstructibleSheaf.stratumRestriction f (𝟙 S)
    (A.immersion a) (B.immersion b) Λ).mapIso
      ((OrientedConstructibleSheaf.vanishingModuleTransport f Λ).mapIso e)

private theorem degreeZero_constructible (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (L : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ))
    (hc : Scheme.IsConstructibleEtaleModuleSheaf (etaleFixed X (Coeff Λ) L)) :
    IsBoundedConstructible X Λ (degreeZero X Λ L) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, ?_⟩
  intro q
  let M := (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).obj
    (degreeZero X Λ L)
  refine ⟨etaleFixed X (Coeff Λ) M, ?_, ⟨sectionsIsoSmall X Λ M⟩⟩
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  by_cases hq : q = 0
  · subst q
    let e := (etaleFixedFunctor X (Coeff Λ)).mapIso
      ((@DerivedCategory.singleFunctorCompHomologyFunctorIso _ _ _
        (HasDerivedCategory.standard _) 0).app L)
    have hc' : Scheme.IsConstructibleSheaf
        ((etaleFixedFunctor X (Coeff Λ)).obj L) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp hc
    exact @Scheme.IsConstructibleSheaf.of_iso X (ModuleCat.{u + 1} (Coeff Λ))
      inferInstance inferInstance inferInstance
      (fun M N : ModuleCat.{u + 1} (Coeff Λ) ↦ M →ₗ[Coeff Λ] N)
      (fun M : ModuleCat.{u + 1} (Coeff Λ) ↦ M) inferInstance inferInstance
      ((etaleFixedFunctor X (Coeff Λ)).obj L) _ e.symm hc'
  · have hz : IsZero M := by
      rcases lt_or_gt_of_ne hq with h | h
      · exact DerivedCategory.isZero_of_isGE (degreeZero X Λ L) 0 q h
      · exact DerivedCategory.isZero_of_isLE (degreeZero X Λ L) 0 q h
    exact Scheme.IsConstructibleSheaf.of_isZero
      ((etaleFixedFunctor X (Coeff Λ)).map_isZero hz)

private theorem psiGood_cohomology_constructible {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (m : ℕ) (hm : 1 ≤ m) (hΛ : (m : Λ) = 0) (hS : IsUnit (m : Γ(S, ⊤)))
    (K : EtaleDerived X Λ) (hK : IsBoundedConstructible X Λ K)
    (hgood : IsPsiGood f Λ K) (q : ℤ) (hq : 0 ≤ q) :
    OrientedConstructibleSheaf.IsConstructibleVanishing f Λ
      ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).obj
        ((nearbyCycles f Λ).obj K)) := by
  obtain ⟨T, p, hp, hs, h⟩ :=
    exists_proper_surjective_constructible f Λ m hm hΛ hS K hK q hq
  have := hp
  have := hs
  let v := squareModules f (pullback.snd f p) (pullback.fst f p) p
    (pullback.condition (f := f) (g := p))
  have := hgood T p
  let e := ((v.modulePull (Coeff Λ)).mapDerivedCategoryHomologyFunctorIso q).app
    ((nearbyCycles f Λ).obj K) ≪≫
      (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).mapIso
        (asIso (baseChange f (pullback.snd f p) (pullback.fst f p) p
          (pullback.condition (f := f) (g := p)) Λ K))
  exact constructibility_descent f Λ p _
    (constructibleVanishing_of_iso (pullback.snd f p) Λ e h)

/-- Psi-good nearby-cycle cohomology admits finite constructible locally closed strata
on both factors, with finite constant module values on a covering of each oriented
stratum. The strata may depend on q; no uniform vanishing bound is claimed.

Source: Lu--Zheng, Duality and nearby cycles over general bases, Theorem 4.27(2)
and the following constructibility definition, v7 author PDF
(blueprint: lem-trf-psi-good-oriented-cohomology-strata).

Proof plan, following the five steps of the node:
1. Place the constructible sheaf L in degree zero. It is bounded constructible with
amplitude [0,0], by def-weil-pbc-constructible-complexes.
2. Apply lem-trf-psi-proper-surjective-constructibility to this bounded input and q.
It supplies a proper surjective T to S on which the nearby cycles of the base-changed
family have constructible q-th cohomology.
3. By def-trf-oriented-nearby-cycles, Psi-goodness makes the canonical base-change map
an isomorphism. The exact constant-coefficient inverse image commutes with cohomology.
Consequently the inverse image of G_q is isomorphic to that constructible sheaf.
Transport its strata and finite constant trivializations across this isomorphism.
4. Apply lem-trf-psi-constructibility-descent along the proper surjective T to S.
This gives constructibility of G_q on V_f.
5. Apply lem-trf-constructible-vanishing-canonical-strata to G_q. Its hypothesis on
inverse image is Mathlib's comparison of sheafPullback with sheafified left Kan extension.
The lemma compares identity-base-change normalization and the stratum Kan extension
with the canonical geometric module pullback. It then reads the finite locally closed
stratifications and their finite constant trivializations on covering sieves of the
terminal triples, in the fixed-ring slice presentation used in the conclusion. -/
theorem exists_constructible_cohomology_strata {X S : Scheme.{u}}
    [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (m : ℕ) (_hm : 1 ≤ m) (_hΛ : (m : Λ) = 0) (_hS : IsUnit (m : Γ(S, ⊤)))
    (L : (etaleDatum.{u, u + 1} X).modules (Coeff.{u, u + 1} Λ))
    (_hc : Scheme.IsConstructibleEtaleModuleSheaf
      (etaleFixed X (Coeff Λ) L)) (_hgood : IsPsiGood f Λ (degreeZero X Λ L))
    (q : ℤ) (_hq : 0 ≤ q) :
    ∃ (A : Scheme.Stratification X) (B : Scheme.Stratification S),
      (∀ a : Fin A.n, Topology.IsConstructible (A.stratum a)) ∧
      (∀ b : Fin B.n, Topology.IsConstructible (B.stratum b)) ∧
      ∀ (a : Fin A.n) (b : Fin B.n),
        ∃ R : (productSite (A.immersion a ≫ f) (B.immersion b)).topology.Cover
          (⊤_ (productSite (A.immersion a ≫ f) (B.immersion b)).objects),
        ∀ (Z : (productSite (A.immersion a ≫ f) (B.immersion b)).objects)
          (r : Z ⟶ ⊤_ (productSite (A.immersion a ≫ f) (B.immersion b)).objects), R r →
          ∃ M : ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ), Finite M ∧
            Nonempty
              ((fixedSheaf (productSite (A.immersion a ≫ f) (B.immersion b)) (Coeff Λ)
                (((restrictionModules f (A.immersion a) (B.immersion b)).modulePull
                  (Coeff Λ)).obj (cohomology f Λ L q))).over Z ≅
                (constantSheaf
                  ((productSite (A.immersion a ≫ f) (B.immersion b)).topology.over Z)
                  (ModuleCat.{u + 1} (Coeff.{u, u + 1} Λ))).obj M) := by
  have hK := degreeZero_constructible X Λ L _hc
  have hG := psiGood_cohomology_constructible f Λ m _hm _hΛ _hS
    (degreeZero X Λ L) hK _hgood q _hq
  obtain ⟨A, B, hA, hB, h⟩ := hG
  refine ⟨stratificationWithConstructible A hA, stratificationWithConstructible B hB,
    hA, hB, ?_⟩
  intro a b
  apply OrientedConstructibleSheaf.canonical_stratum_trivializations f
    (A.immersion a) (B.immersion b) Λ
    (restrictionModules f (A.immersion a) (B.immersion b)) ?_
    (cohomology f Λ L q) (h a b)
  exact ⟨Functor.sheafPullbackConstruction.sheafPullbackIso
    (restrictSite f (A.immersion a) (B.immersion b))
    (Type (u + 1)) (vanishingTopology f)
    (productSite (A.immersion a ≫ f) (B.immersion b)).topology⟩

end AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata
