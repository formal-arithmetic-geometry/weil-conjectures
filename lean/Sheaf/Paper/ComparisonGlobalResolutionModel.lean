/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.ComparisonPullbackExact
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono

/-!
# A normalized resolution model for global site comparison

Source: relative Kummer proof, opening paragraph, and Stacks Tags 099R, 099W,
013K, 070J, 070Y, 079P, 0DVC and 09T5
(blueprint: lem-pur-comparison-global-resolution-model).

The fixed-ring module-sheaf presentation is the one used by the recorded global
comparison. It is canonically equivalent to the coefficient-ring-sheaf presentation.
The computing isomorphisms below are determined by equations with the supplied
augmentations and the canonical right-derived comparison units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- The sheaf F in degree zero, retaining its explicit bounded-below representative.
Source: Stacks Tag 013K (blueprint: lem-pur-comparison-global-resolution-model). -/
def comparisonResolutionSingle {U : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  ⟨(CochainComplex.singleFunctor _ 0).obj F, ⟨0, inferInstance⟩⟩

/-- The two nonnegative injective resolutions, with their given augmentations.
Source: Stacks Tags 013K, 070J and 079P, applied twice as in the node's proof
(blueprint: lem-pur-comparison-global-resolution-model). -/
structure ComparisonGlobalResolution (U : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) where
  I : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  J : CochainComplex.Plus (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))
  nonnegativeI : I.obj.IsStrictlyGE 0
  nonnegativeJ : J.obj.IsStrictlyGE 0
  injectiveI : ∀ n : ℤ, Injective (I.obj.X n)
  injectiveJ : ∀ n : ℤ, Injective (J.obj.X n)
  kInjectiveI : I.obj.IsKInjective
  kInjectiveJ : J.obj.IsKInjective
  i : comparisonResolutionSingle F ⟶ I
  t : (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapCochainComplexPlus.obj I ⟶ J
  quasiIsoI : QuasiIso i.hom
  quasiIsoT : QuasiIso t.hom

namespace ComparisonGlobalResolution

variable {U : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
  {F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
  (R : ComparisonGlobalResolution U Λ F)

/-- The adjoint h of the supplied t, using the actual comparison adjunction termwise.
Source: Stacks Tag 0DVC (blueprint: lem-pur-comparison-global-resolution-model). -/
def adjoint : R.I.obj ⟶
    ((comparisonLowerStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex (.up ℤ)).obj
      R.J.obj :=
  ((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex (.up ℤ)).homEquiv
    R.I.obj R.J.obj R.t.hom

/-- The source complex of global sections of the etale resolution.
Source: Stacks Tag 099R (blueprint: lem-pur-comparison-global-resolution-model). -/
def sourceSections : CochainComplex.Plus (ModuleCat.{u + 1} Λ) :=
  (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).mapCochainComplexPlus.obj R.I

/-- The target complex of global sections of the pro-etale resolution.
Source: Stacks Tag 099R (blueprint: lem-pur-comparison-global-resolution-model). -/
def targetSections : CochainComplex.Plus (ModuleCat.{u + 1} Λ) :=
  (sheafToPresheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ) ⋙
    (evaluation _ _).obj
      (op ((Scheme.toProEt U).obj (Scheme.Etale.mk (𝟙 U))))).mapCochainComplexPlus.obj R.J

/-- Evaluation of h at the final object; restriction identifies (N J)(U) with J(U).
Source: Stacks Tags 099R and 099W
(blueprint: lem-pur-comparison-global-resolution-model). -/
def sectionMap : R.sourceSections ⟶ R.targetSections :=
  ⟨((sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
            (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).mapHomologicalComplex (.up ℤ)).map
      R.adjoint⟩

/-- The identification beta = Q(t A(i)), including exact pullback's localization factor.
Source: Stacks Tag 04JC and localization
(blueprint: lem-pur-comparison-global-resolution-model). -/
def targetIdentification :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
      (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)) ⟶
    DerivedCategory.Plus.Q.obj R.J :=
  (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlusFactorsh.hom.app
      ((HomotopyCategory.Plus.quotient _).obj (comparisonResolutionSingle F)) ≫
    DerivedCategory.Plus.Q.map
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapCochainComplexPlus.map R.i ≫ R.t)

end ComparisonGlobalResolution

/-- The class of a global cocycle in the localized section complex. Only the canonical
homology factorization isomorphisms occur. Source: Stacks Tag 070Y
(blueprint: lem-pur-comparison-global-resolution-model). -/
def comparisonResolutionCycleClass {Λ : Type (u + 1)} [CommRing Λ]
    (K : CochainComplex.Plus (ModuleCat.{u + 1} Λ)) (q : ℤ) (z : K.obj.cycles q) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      (DerivedCategory.Plus.Q.obj K) :=
  (DerivedCategory.homologyFunctorFactorsh _ q).inv.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K.obj)
    ((HomotopyCategory.homologyFunctorFactors _ (.up ℤ) q).inv.app K.obj
      (K.obj.homologyπ q z))

/-- The actual derived-unit global comparison on the specified degree-zero model,
with the derived identity removed by its canonical isomorphism.
Source: Stacks Tag 099W and the recorded normalized global comparison
(blueprint: lem-pur-comparison-global-resolution-model). -/
def comparisonResolutionGlobalMap (U : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv.app
      ((sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
          (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))) ≫
    (finiteComparisonGlobalSections U Λ).app
      (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F))

set_option backward.isDefEq.respectTransparency.types false in
private theorem resolution_Q_isIso
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex.Plus C} (f : K ⟶ L) [QuasiIso f.hom] :
    IsIso (DerivedCategory.Plus.Q.map f) := by
  apply Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
  apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
  change QuasiIso f.hom
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
private theorem cycleClass_naturality {Λ : Type (u + 1)} [CommRing Λ]
    {K L : CochainComplex.Plus (ModuleCat.{u + 1} Λ)} (f : K ⟶ L)
    (q : ℤ) (z : K.obj.cycles q) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map
        (DerivedCategory.Plus.Q.map f) (comparisonResolutionCycleClass K q z) =
      comparisonResolutionCycleClass L q (HomologicalComplex.cyclesMap f.hom q z) := by
  have h₁ := (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u + 1} Λ) q).inv.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map f.hom)
  have h₂ := (HomotopyCategory.homologyFunctorFactors
    (ModuleCat.{u + 1} Λ) (.up ℤ) q).inv.naturality f.hom
  have h₃ := HomologicalComplex.homologyπ_naturality f.hom q
  dsimp only [Functor.comp_map] at h₁ h₂
  have h : K.obj.homologyπ q ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u + 1} Λ) (.up ℤ) q).inv.app
          K.obj ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u + 1} Λ) q).inv.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj K.obj) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q).map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f.hom)) =
      HomologicalComplex.cyclesMap f.hom q ≫ L.obj.homologyπ q ≫
        (HomotopyCategory.homologyFunctorFactors (ModuleCat.{u + 1} Λ) (.up ℤ) q).inv.app
          L.obj ≫
        (DerivedCategory.homologyFunctorFactorsh (ModuleCat.{u + 1} Λ) q).inv.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj L.obj) := by
    erw [← h₁, ← reassoc_of% h₂, reassoc_of% h₃]
  have hz := ConcreteCategory.congr_hom h z
  simp only [ModuleCat.comp_apply] at hz
  exact hz

set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChange_unit
    {B B' C : Type*} [Category* B] [Category* B'] [Category* C]
    [Abelian B] [Abelian B'] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
    [EnoughInjectives B] [EnoughInjectives B']
    (G : B ⥤ C) (G' : B' ⥤ C) (A : B ⥤ B')
    [G.Additive] [G'.Additive] [A.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    (e : G ⋙ 𝟭 C ⟶ A ⋙ G') (K : HomotopyCategory.Plus B) :
    G.rightDerivedFunctorPlusUnit.app K ≫
        (Functor.mapDerivedCategoryPlusIdIso C).inv.app
          (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
        (Functor.rightDerivedFunctorPlusBaseChange e).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) ≫
        G'.rightDerivedFunctorPlusUnit.app (A.mapHomotopyCategoryPlus.obj K) ≫
        G'.rightDerivedFunctorPlus.map (A.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have h := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac e) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at h
  have hn := (Functor.mapDerivedCategoryPlusIdIso C).inv.naturality
    (G.rightDerivedFunctorPlusUnit.app K)
  dsimp only [Functor.id_map] at hn
  erw [← Category.assoc, hn, Category.assoc, h]
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app,
    Category.id_comp, Category.comp_id]
  rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  simp

set_option backward.isDefEq.respectTransparency.types false in
private theorem resolution_exists (U : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (ComparisonGlobalResolution U Λ F) := by
  let A := comparisonUpperStar (ModuleCat.{u + 1} Λ) U
  have : (comparisonResolutionSingle F).obj.IsStrictlyGE 0 := by
    dsimp [comparisonResolutionSingle]
    infer_instance
  obtain ⟨I, i, hI, hinjI, _, hi⟩ :=
    CochainComplex.exists_mono_quasiIso_injective_boundedBelow _ 0
      (comparisonResolutionSingle F).obj
      (fun n hn ↦ (comparisonResolutionSingle F).obj.isZero_of_isStrictlyGE 0 n hn)
  have hI' : I.IsStrictlyGE 0 := (I.isStrictlyGE_iff 0).mpr hI
  let I' : CochainComplex.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨I, ⟨0, hI'⟩⟩
  have : I.IsStrictlyGE 0 := hI'
  have : ∀ n : ℤ, Injective (I.X n) := hinjI
  have : (A.mapCochainComplexPlus.obj I').obj.IsStrictlyGE 0 := by
    change CochainComplex.IsStrictlyGE ((A.mapHomologicalComplex (.up ℤ)).obj I) 0
    infer_instance
  obtain ⟨J, t, hJ, hinjJ, _, ht⟩ :=
    CochainComplex.exists_mono_quasiIso_injective_boundedBelow _ 0
      (A.mapCochainComplexPlus.obj I').obj
      (fun n hn ↦ (A.mapCochainComplexPlus.obj I').obj.isZero_of_isStrictlyGE 0 n hn)
  have hJ' : J.IsStrictlyGE 0 := (J.isStrictlyGE_iff 0).mpr hJ
  have : J.IsStrictlyGE 0 := hJ'
  have : ∀ n : ℤ, Injective (J.X n) := hinjJ
  exact ⟨{ I := I', J := ⟨J, ⟨0, hJ'⟩⟩, nonnegativeI := hI', nonnegativeJ := hJ'
           injectiveI := hinjI, injectiveJ := hinjJ
           kInjectiveI := CochainComplex.isKInjective_of_injective I 0
           kInjectiveJ := CochainComplex.isKInjective_of_injective J 0
           i := ⟨i⟩, t := ⟨t⟩, quasiIsoI := hi, quasiIsoT := ht }⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- There exist two nonnegative termwise injective K-injective resolutions, and every
such pair computes the specified global comparison, including its cocycle formula.
The equations for eI and eJ uniquely specify the computing isomorphisms using i and
beta = Q(t A(i)); in particular the target identification is not freely chosen.
Source: relative Kummer proof, opening paragraph; Stacks Tags 099R and 099W
(blueprint: lem-pur-comparison-global-resolution-model).

Proof:
1. The ring-sheaf Grothendieck theorem and enough-injectives theorem give enough
injectives on both sites. Apply lem-weil-pbc-complex-injective-resolution-mono at
lower bound zero to F[0], and then to A(I). Exactness of A makes its augmentation
quasi-isomorphic and its complex nonnegative. The bounded-below injectives theorem
makes both resolutions K-injective. This proves existence.
2. For any such pair, exactness carries i to a quasi-isomorphism. Localization
therefore inverts i and t A(i); its exact-functor comparison identifies the latter
with beta. This gives precisely the target identification in the statement.
3. The termwise adjunction of lem-weil-pbc-termwise-adjunction-homotopy gives
h = N(t) eta_I. Restriction along the inclusion evaluates at the same final
object, with the same coefficient action and differential. Thus evaluation is w.
4. Since A is exact, N preserves injectives by
lem-sp-right-adjoint-preserves-injectives. Hence N(J) is also nonnegative termwise
injective. Apply lem-weil-pbc-right-derived-plus-injective to N and to the two
section functors. Their units are invertible on these computing resolutions.
Inverting the localized augmentations uniquely gives eI and eJ with the displayed
normalizations.
5. Apply lem-pur-comparison-unit-injective-model to I and t. It says
RN(Qt) eta_QI = alpha_J Qh. Naturality at Qi gives
RN(beta) eta_F[0] = alpha_J Qh Qi, with the exact-pullback factor inserted.
6. Apply derived etale sections. Naturality of its computing unit and the terminal
identification of lem-weil-pbc-derived-sections-pushforward identify this with Qw.
The comparison of lem-weil-pbc-comparison-global-cohomology is this derived unit
followed by the terminal identification. The two normalization equations therefore
give Qw eJ = eI c, for the given i and beta, for every resolution pair.
7. A chain map carries cycles to cycles and boundaries to boundaries. Applying
homology to the equation in Step 6 gives the displayed formula for every q >= 0
and every cocycle z. Evaluation of h = N(t) eta_I gives h(z) = t(A(z)). The
unit's Kan-extension class indexed by (U,id) followed by sheafification is exactly
the pulled-back terminal section; comparisonConstantRingMap identifies its unit
with 1 by lem-sf-comparison-pullback-exact. This includes q = 0, with zero incoming
degree. No step uses preservation of injectives by A. -/
theorem comparisonGlobalResolutionModel (U : Scheme.{u}) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty (ComparisonGlobalResolution U Λ F) ∧
      ∀ R : ComparisonGlobalResolution U Λ F,
        IsIso R.targetIdentification ∧
        ∃ (eI : DerivedCategory.Plus.Q.obj R.sourceSections ≅
            (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).rightDerivedFunctorPlus.obj
                (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)))
          (eJ : DerivedCategory.Plus.Q.obj R.targetSections ≅
            (sheafToPresheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj
                (op ((Scheme.toProEt U).obj (Scheme.Etale.mk (𝟙 U))))).rightDerivedFunctorPlus.obj
                  ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
                    (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)))),
          (eI.hom ≫
            (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).rightDerivedFunctorPlus.map
                (DerivedCategory.Plus.Q.map R.i) =
            (sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))).rightDerivedFunctorPlusUnit.app
                ((HomotopyCategory.Plus.quotient _).obj R.I)) ∧
          (eJ.hom ≫
            (sheafToPresheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj
                (op ((Scheme.toProEt U).obj (Scheme.Etale.mk (𝟙 U))))).rightDerivedFunctorPlus.map
                  R.targetIdentification =
            (sheafToPresheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ) ⋙
              (evaluation _ _).obj
                (op ((Scheme.toProEt U).obj
                  (Scheme.Etale.mk (𝟙 U))))).rightDerivedFunctorPlusUnit.app
                  ((HomotopyCategory.Plus.quotient _).obj R.J)) ∧
          (DerivedCategory.Plus.Q.map R.sectionMap ≫ eJ.hom =
            eI.hom ≫ comparisonResolutionGlobalMap U Λ F) ∧
          ∀ (q : ℕ) (z : R.sourceSections.obj.cycles (q : ℤ)),
            ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map
              (comparisonResolutionGlobalMap U Λ F))
                (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map eI.hom)
                  (comparisonResolutionCycleClass R.sourceSections q z)) =
            ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map eJ.hom)
              (comparisonResolutionCycleClass R.targetSections q
                (HomologicalComplex.cyclesMap R.sectionMap.hom q z)) ∧
            (R.adjoint.f q).hom.app (op (Scheme.Etale.mk (𝟙 U)))
                (R.sourceSections.obj.iCycles q z) =
              (R.t.hom.f q).hom.app
                (op ((Scheme.toProEt U).obj (Scheme.Etale.mk (𝟙 U))))
                ((((comparisonAdjunction (ModuleCat.{u + 1} Λ) U).unit.app
                  (R.I.obj.X q)).hom.app (op (Scheme.Etale.mk (𝟙 U))))
                    (R.sourceSections.obj.iCycles q z)) := by
  refine ⟨resolution_exists U Λ F, ?_⟩
  intro R
  have : QuasiIso R.i.hom := R.quasiIsoI
  have : QuasiIso R.t.hom := R.quasiIsoT
  have : IsIso R.targetIdentification := by
    dsimp only [ComparisonGlobalResolution.targetIdentification]
    rw [Functor.map_comp]
    have : IsIso (DerivedCategory.Plus.Q.map R.i) := by
      exact resolution_Q_isIso R.i
    have : IsIso (DerivedCategory.Plus.Q.map R.t) := by
      exact resolution_Q_isIso R.t
    have : IsIso (DerivedCategory.Plus.Q.map
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapCochainComplexPlus.map R.i)) := by
      have : QuasiIso
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapCochainComplexPlus.map R.i).hom := by
        change QuasiIso
          (((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapHomologicalComplex (.up ℤ)).map
            R.i.hom)
        infer_instance
      exact resolution_Q_isIso _
    infer_instance
  refine ⟨this, ?_⟩
  let G := sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 U)))
  let G' := sheafToPresheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ) ⋙
    (evaluation _ _).obj (op ((Scheme.toProEt U).obj (Scheme.Etale.mk (𝟙 U))))
  let A := comparisonUpperStar (ModuleCat.{u + 1} Λ) U
  let KI := (HomotopyCategory.Plus.quotient _).obj R.I
  let KJ := (HomotopyCategory.Plus.quotient _).obj R.J
  have : ∀ n : ℤ, Injective (R.I.obj.X n) := R.injectiveI
  have : ∀ n : ℤ, Injective (R.J.obj.X n) := R.injectiveJ
  have : IsIso (G.rightDerivedFunctorPlusUnit.app KI) := by dsimp [KI]; infer_instance
  have : IsIso (G'.rightDerivedFunctorPlusUnit.app KJ) := by dsimp [KJ]; infer_instance
  have : IsIso (DerivedCategory.Plus.Q.map R.i) := resolution_Q_isIso R.i
  have : IsIso (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map R.i)) :=
    inferInstance
  have : IsIso (G'.rightDerivedFunctorPlus.map R.targetIdentification) := inferInstance
  -- Pin the computing isomorphisms to the given augmentations.
  let eI := asIso (G.rightDerivedFunctorPlusUnit.app KI) ≪≫
    (asIso (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map R.i))).symm
  let eJ := asIso (G'.rightDerivedFunctorPlusUnit.app KJ) ≪≫
    (asIso (G'.rightDerivedFunctorPlus.map R.targetIdentification)).symm
  have hw : DerivedCategory.Plus.Q.map R.sectionMap ≫ eJ.hom =
      eI.hom ≫ comparisonResolutionGlobalMap U Λ F := by
    -- Compute the recorded base-change map on the supplied resolution.
    have hu := baseChange_unit G G' A (finiteComparisonGlobalSectionsUnit U Λ) KI
    have ht := G'.rightDerivedFunctorPlusUnit.naturality
      ((HomotopyCategory.Plus.quotient _).map R.t)
    change DerivedCategory.Plus.Q.map (G'.mapCochainComplexPlus.map R.t) ≫
        G'.rightDerivedFunctorPlusUnit.app KJ =
      G'.rightDerivedFunctorPlusUnit.app (A.mapHomotopyCategoryPlus.obj KI) ≫
        G'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map R.t) at ht
    let wunit : R.sourceSections ⟶
        G'.mapCochainComplexPlus.obj (A.mapCochainComplexPlus.obj R.I) :=
      ⟨(NatTrans.mapHomologicalComplex (finiteComparisonGlobalSectionsUnit U Λ)
        (.up ℤ)).app R.I.obj⟩
    have he : DerivedCategory.Plus.Qh.map
        ((NatTrans.mapHomotopyCategoryPlus (finiteComparisonGlobalSectionsUnit U Λ)).app KI) =
          DerivedCategory.Plus.Q.map wunit := by
      apply DerivedCategory.Plus.ι.map_injective
      change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι _).map
          ((NatTrans.mapHomotopyCategoryPlus (finiteComparisonGlobalSectionsUnit U Λ)).app
            KI)) =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map wunit.hom)
      rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
      rfl
    have hw₀ : DerivedCategory.Plus.Q.map R.sectionMap =
        DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus (finiteComparisonGlobalSectionsUnit U Λ)).app
              KI) ≫
          DerivedCategory.Plus.Q.map (G'.mapCochainComplexPlus.map R.t) := by
      erw [he, ← Functor.map_comp]
      congr 1
    have hcalc : DerivedCategory.Plus.Q.map R.sectionMap ≫
          G'.rightDerivedFunctorPlusUnit.app KJ =
        G.rightDerivedFunctorPlusUnit.app KI ≫
          (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv.app
            (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj R.I)) ≫
          (finiteComparisonGlobalSections U Λ).app (DerivedCategory.Plus.Q.obj R.I) ≫
          G'.rightDerivedFunctorPlus.map
            (A.mapDerivedCategoryPlusFactorsh.hom.app KI ≫
              DerivedCategory.Plus.Q.map R.t) := by
      dsimp only [finiteComparisonGlobalSections]
      erw [reassoc_of% hu]
      simp only [Functor.map_comp]
      erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        G'.rightDerivedFunctorPlus.map_id, Category.id_comp]
      erw [hw₀, Category.assoc, ht]
    -- Transport that calculation from I to F[0] using the given i.
    let c : G.rightDerivedFunctorPlus ⟶ A.mapDerivedCategoryPlus ⋙
        G'.rightDerivedFunctorPlus :=
      Functor.whiskerLeft G.rightDerivedFunctorPlus
          (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv ≫
        finiteComparisonGlobalSections U Λ
    have hc := c.naturality (DerivedCategory.Plus.Q.map R.i)
    dsimp only [Functor.comp_map] at hc
    have hn : inv (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map R.i)) ≫
          c.app (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)) ≫
          G'.rightDerivedFunctorPlus.map
            (A.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Q.map R.i)) =
        c.app (DerivedCategory.Plus.Q.obj R.I) := by
      rw [← hc, IsIso.inv_hom_id_assoc]
    -- Naturality inserts the exact-pullback factor at I into beta.
    have hβ : R.targetIdentification =
        A.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Q.map R.i) ≫
          A.mapDerivedCategoryPlusFactorsh.hom.app KI ≫ DerivedCategory.Plus.Q.map R.t := by
      have hf := A.mapDerivedCategoryPlusFactorsh.hom.naturality
        ((HomotopyCategory.Plus.quotient _).map R.i)
      change A.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Q.map R.i) ≫
          A.mapDerivedCategoryPlusFactorsh.hom.app KI =
        A.mapDerivedCategoryPlusFactorsh.hom.app
            ((HomotopyCategory.Plus.quotient _).obj (comparisonResolutionSingle F)) ≫
          DerivedCategory.Plus.Q.map (A.mapCochainComplexPlus.map R.i) at hf
      dsimp only [ComparisonGlobalResolution.targetIdentification]
      rw [Functor.map_comp, ← Category.assoc]
      exact (congrArg (fun f ↦ f ≫ DerivedCategory.Plus.Q.map R.t) hf.symm).trans
        (Category.assoc _ _ _)
    -- Cancel the target augmentation after using both normalizations.
    apply (cancel_mono (G'.rightDerivedFunctorPlus.map R.targetIdentification)).mp
    simp only [eI, eJ, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    change _ = G.rightDerivedFunctorPlusUnit.app KI ≫
      inv (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map R.i)) ≫
        c.app (DerivedCategory.Plus.Q.obj (comparisonResolutionSingle F)) ≫
          G'.rightDerivedFunctorPlus.map R.targetIdentification
    erw [hβ, Functor.map_comp, Functor.map_comp]
    erw [reassoc_of% hn]
    simpa only [c, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.map_comp, Category.assoc] using hcalc
  refine ⟨eI, eJ, ?_, ?_, hw, ?_⟩
  · change eI.hom ≫ G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map R.i) =
      G.rightDerivedFunctorPlusUnit.app KI
    simp [eI]
  · change eJ.hom ≫ G'.rightDerivedFunctorPlus.map R.targetIdentification =
      G'.rightDerivedFunctorPlusUnit.app KJ
    simp [eJ]
  · intro q z
    constructor
    · have hh := congrArg
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map hw
      simp only [Functor.map_comp] at hh
      have hz := ConcreteCategory.congr_hom hh
        (comparisonResolutionCycleClass R.sourceSections q z)
      simp only [ModuleCat.comp_apply, cycleClass_naturality] at hz
      exact hz.symm
    · rfl

end AlgebraicGeometry.ProEtale
