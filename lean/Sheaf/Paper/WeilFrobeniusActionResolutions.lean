/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.CategoryTheory.TwistedActionRingedSite
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.ContinuousLocallyFreePullback
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Frobenius action sites and unbounded resolutions

Source: latest blueprint, cor-coef-verdier-weil-equivariance, internal-Hom/evaluation
paragraph; native action-site refinement, steps 1--7; Stacks 015F, 06YS, 079P, 0G7E,
and 08BJ (blueprint: lem-sf-weil-frobenius-action-resolutions).

The small site is the existing bounded pro-etale category with lifted hom types.
It retains every bounded object, and hence all integer translates. Coefficients
and K-flatness reuse the recorded section-ring and module-sheaf interfaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u wA wB
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures.WeilFrobeniusAction

/-- Postcomposition on the actual bounded weakly etale site.
Source: native action-site proof, step 1
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def postcompose {T : Scheme.{u}} (g : T ≅ T) : T.ProEt ≌ T.ProEt :=
  MorphismProperty.Comma.mapRightIso (P := @WeaklyEtale) (Q := ⊤) (W := ⊤)
    (𝟭 Scheme.{u}) ((Functor.const _).mapIso g)

/-- A small model containing every bounded object and every integer translate.
Source: native action-site proof, step 1; the size convention
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev Site (T : Scheme.{u}) := AsSmall.{u + 1} T.ProEt

/-- The topology transported from the recorded small pro-etale site.
Source: native action-site proof, steps 1--2
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev topology (T : Scheme.{u}) : GrothendieckTopology (Site T) :=
  AsSmall.down.inducedTopology (Scheme.ProEt.topology T)

/-- Inverse Frobenius translation, so inverse reindexing is geometric Frobenius pullback.
Source: native action-site proof, step 1
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def translation {T : Scheme.{u}} (g : T ≅ T) : Site T ≌ Site T :=
  AsSmall.equiv.symm.trans ((postcompose g.symm).trans AsSmall.equiv)

/-- The finite-subextension coefficient ring, reconstructed from its existing
sheafification and restricted to the small model.
Source: native action-site proof, step 2; Bhatt--Scholze 6.8
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def coefficient (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    Sheaf (topology T) CommRingCat.{u + 1} :=
  (AsSmall.down.sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology T) (Scheme.ProEt.topology T)).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l))

/-- The generating finite-field-valued continuous sections of the sheafified ring.
Source: native action-site proof, step 2
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def generator (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (U : Site T)
    (f : PadicAlgCl.finiteIntermediateFieldValued l (AsSmall.down.obj U).left) :
    (coefficient T l).obj.obj (op U) :=
  (toSheafify (Scheme.ProEt.topology T)
    (ProEtale.padicAlgClRingPresheaf T l ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})).app
      (op (AsSmall.down.obj U)) (ULift.up f)

/-- The existing module-sheaf category over this coefficient ring.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev Modules (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :=
  TwistedActionRingedSite.Modules (coefficient T l)

/-- Return to the original site, with its unchanged ring and module sections.
Source: native action-site proof, step 2
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def ambientModules (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    Modules T l ⥤ Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (ProEtale.padicAlgClSheaf T l) := by
  have : (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T) (topology T) := by
    change (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T)
      ((AsSmall.equiv : T.ProEt ≌ Site T).inverse.inducedTopology (Scheme.ProEt.topology T))
    infer_instance
  have : AsSmall.up.IsContinuous (Scheme.ProEt.topology T) (topology T) :=
    inferInstanceAs ((AsSmall.equiv : T.ProEt ≌ Site T).functor.IsContinuous
      (Scheme.ProEt.topology T) (topology T))
  exact SheafOfModules.pushforward (F := AsSmall.up)
    (𝟙 ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l)))) ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l)).inverse

/-- The finite locally closed stratification with locally finite free restrictions,
expressed on the original site by the recorded scheme-cover predicate
`AlgebraicGeometry.ProEtale.CondensedRing.LocallyFree`, owned by
`def-sf-proetale-locally-finite-free-module`.
Source: native action-site proof, step 5; Bhatt--Scholze 6.8
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def Constructible (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (M : Modules T l) : Prop :=
  ∃ S : Scheme.FiniteLocallyClosedStratification T, ∀ i : Fin S.n,
    ProEtale.CondensedRing.LocallyFree
      ((ProEtale.upperStar Ab.{u + 1} (S.immersion i)).obj (ProEtale.padicAlgClSheaf T l))
      (((ProEtale.upperStar Ab.{u + 1} (S.immersion i)).mapMod
        (ProEtale.padicAlgClSheaf T l)).obj ((ambientModules T l).obj M))

/-- The normalized ordinary Frobenius action-site realization.
Source: native action-site proof, steps 1--3
(blueprint: lem-sf-weil-frobenius-action-resolutions).
No realization is selected from a mere existence statement. Its presentation is
exactly the recorded twisted ringed-site presentation, including tensor, Hom,
symmetry, evaluation, created limits/colimits, and normalized orbit induction. -/
structure Realization (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (g : T ≅ T) where
  /-- The concrete restriction model has exactly the original module category. -/
  ambientEquivalence : (ambientModules T l).IsEquivalence
  /-- The comparison with original modules is additive. -/
  ambientAdditive : (ambientModules T l).Additive
  /-- Covering sieves are preserved by the translation. -/
  covering : CoverPreserving (topology T) (topology T) (translation g).functor
  /-- Covering sieves are preserved by its inverse. -/
  inverseCovering : CoverPreserving (topology T) (topology T) (translation g).inverse
  /-- Postcomposition and its inverse preserve the topology. -/
  [continuous : (translation g).functor.IsContinuous (topology T) (topology T)]
  /-- The inverse translation preserves the topology. -/
  [inverseContinuous : (translation g).inverse.IsContinuous (topology T) (topology T)]
  /-- The chosen coefficient identification. -/
  a : ((translation g).inverse.sheafPushforwardContinuous CommRingCat.{u + 1}
    (topology T) (topology T)).obj (coefficient T l) ≅ coefficient T l
  /-- On generating functions, postcomposition leaves the domain and function unchanged.
  In particular the very same finite coefficient field is preserved. -/
  functions (U : Site T)
      (f : PadicAlgCl.finiteIntermediateFieldValued l (AsSmall.down.obj U).left) :
    a.hom.hom.app (op U) (generator T l ((translation g).inverse.obj U) f) =
      generator T l U f
  /-- The explicitly defined pullback is an additive autoequivalence. -/
  [sigmaEquivalence : (TwistedActionRingedSite.sigma
    (topology T) (translation g) (coefficient T l) a).IsEquivalence]
  /-- Additivity is on the original module maps. -/
  [sigmaAdditive : (TwistedActionRingedSite.sigma
    (topology T) (translation g) (coefficient T l) a).Additive]
  /-- The full ordinary presentation, including all canonical comparisons. -/
  presentation : TwistedActionRingedSite.Presentation
    (topology T) (translation g) (coefficient T l) a

/-- The normalized pullback, with its topology witnesses fixed by the realization.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev pullback {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) : Modules T l ⥤ Modules T l :=
  letI := D.continuous
  letI := D.inverseContinuous
  TwistedActionRingedSite.sigma (topology T) (translation g) (coefficient T l) D.a

/-- Pullback is the autoequivalence asserted in the realization.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
instance pullbackEquivalence {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) : (pullback D).IsEquivalence := D.sigmaEquivalence

/-- Pullback is additive on ordinary module maps.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
instance pullbackAdditive {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) : (pullback D).Additive := D.sigmaAdditive

/-- The recorded fixed-pair category for the explicit module pullback.
Source: native action-site proof, step 3
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev Pairs {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) :=
  Endofunctor.IsoAlgebra (pullback D)

/-- Forget only the invertible Frobenius structure.
Source: native action-site proof, steps 3--4
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev forget {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) : Pairs D ⥤ Modules T l :=
  Endofunctor.IsoAlgebra.forget (pullback D)

/-- The actual inverse action-site equivalence applied termwise to complexes.
Source: native action-site proof, step 6
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
abbrev onActionSite {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) :=
  letI := D.continuous
  letI := D.inverseContinuous
  D.presentation.modules.inverse.mapHomologicalComplex (ComplexShape.up ℤ)

/-- K-flatness in fixed pairs, transported by the specified additive tensor equivalence.
Source: native action-site proof, step 6; Stacks 06YN
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def KFlat {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) (K : CochainComplex (Pairs D) ℤ) : Prop :=
  letI := D.continuous
  letI := D.inverseContinuous
  letI := D.presentation.category
  CochainComplex.IsKFlatIndependentCoefficients
    (J := D.presentation.topology) (R := D.presentation.coefficient) ((onActionSite D).obj K)

/-- Flat terms in fixed pairs, under the same normalized tensor equivalence.
Source: native action-site proof, step 6; Stacks 03ER
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
def FlatTerms {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) (K : CochainComplex (Pairs D) ℤ) : Prop :=
  letI := D.continuous
  letI := D.inverseContinuous
  letI := D.presentation.category
  ∀ n : ℤ, SheafOfModules.IsFlatOnSite
    (J := D.presentation.topology) (R := D.presentation.coefficient)
    (((onActionSite D).obj K).X n)

/-- All derived and unbounded resolution assertions, on actual fixed-pair complexes.
Source: native action-site proof, steps 4--7
(blueprint: lem-sf-weil-frobenius-action-resolutions). -/
structure ResolutionAssertions {T : Scheme.{u}} {l : ℕ} [Fact l.Prime] {g : T ≅ T}
    (D : Realization T l g) [HasDerivedCategory.{wA} (Modules T l)]
    [HasDerivedCategory.{wB} (Pairs D)] where
  /-- Termwise forgetting localizes to a triangulated conservative functor. -/
  derived : (forget D).mapDerivedCategory.IsTriangulated ∧
    (forget D).mapDerivedCategory.ReflectsIsomorphisms
  /-- The cohomology identifications are natural on all localized morphisms. -/
  cohomology : ∀ n : ℤ, Nonempty ((forget D).mapDerivedCategory ⋙
    DerivedCategory.homologyFunctor _ n ≅
      DerivedCategory.homologyFunctor _ n ⋙ forget D)
  /-- Bounded constructibility has exactly the same meaning after forgetting. -/
  constructible : ∀ K : DerivedCategory (Pairs D),
    DerivedCategory.TStructure.t.bounded K →
    (∀ n : ℤ, Constructible T l ((forget D).obj
      ((DerivedCategory.homologyFunctor _ n).obj K))) →
    DerivedCategory.TStructure.t.bounded ((forget D).mapDerivedCategory.obj K) ∧
      ∀ n : ℤ, Constructible T l ((DerivedCategory.homologyFunctor _ n).obj
        ((forget D).mapDerivedCategory.obj K))
  /-- Every unbounded complex has a flat-term K-flat resolution. -/
  flat_resolution : ∀ K : CochainComplex (Pairs D) ℤ,
    ∃ (L : CochainComplex (Pairs D) ℤ) (f : L ⟶ K),
      QuasiIso f ∧ KFlat D L ∧ FlatTerms D L ∧
        QuasiIso (((forget D).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  /-- A single functorial K-injective replacement and its natural augmentation. -/
  injective_resolution : ∃ (I : CochainComplex (Pairs D) ℤ ⥤ CochainComplex (Pairs D) ℤ)
    (η : 𝟭 (CochainComplex (Pairs D) ℤ) ⟶ I),
    ∀ K : CochainComplex (Pairs D) ℤ,
      QuasiIso (η.app K) ∧ (I.obj K).IsKInjective ∧
        QuasiIso (((forget D).mapHomologicalComplex (ComplexShape.up ℤ)).map (η.app K))
  /-- Forgetting preserves K-flatness together with termwise flatness. -/
  preserves_flat : ∀ K : CochainComplex (Pairs D) ℤ, KFlat D K → FlatTerms D K →
    CochainComplex.IsKFlatIndependentCoefficients (R := coefficient T l)
      (((forget D).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u + 1, u + 1, u + 1}
      (J := topology T) (R := coefficient T l) ((forget D).obj (K.X n))
  /-- Forgetting preserves all K-injective complexes, not just chosen replacements. -/
  preserves_injective : ∀ K : CochainComplex (Pairs D) ℤ, K.IsKInjective →
    CochainComplex.IsKInjective
      (((forget D).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  /-- Exactness preserves every quasi-isomorphism and hence every resolution arrow. -/
  quasiIso : ∀ (K L : CochainComplex (Pairs D) ℤ) (f : K ⟶ L), QuasiIso f →
    QuasiIso (((forget D).mapHomologicalComplex (ComplexShape.up ℤ)).map f)

private theorem presieve_map_comp {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E)
    {X : C} (R : Presieve X) : (R.map F).map G = R.map (F ⋙ G) := by
  funext Y f
  apply propext
  constructor
  · rintro ⟨⟨h⟩⟩
    exact ⟨h⟩
  · rintro ⟨h⟩
    exact ⟨⟨h⟩⟩

private theorem postcompose_continuous {T : Scheme.{u}} (g : T ≅ T) :
    (postcompose g).functor.IsContinuous (Scheme.ProEt.topology T)
      (Scheme.ProEt.topology T) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (postcompose g).functor
    (Scheme.ProEt.precoverage T) (Scheme.ProEt.precoverage T)
  intro X R hR
  change (R.map (postcompose g).functor).map (Scheme.ProEt.forget T ⋙ Over.forget T) ∈
    Scheme.proetalePrecoverage _
  change R.map (Scheme.ProEt.forget T ⋙ Over.forget T) ∈
    Scheme.proetalePrecoverage _ at hR
  rw [presieve_map_comp]
  exact hR

private theorem translation_continuous {T : Scheme.{u}} (g : T ≅ T) :
    (translation g).functor.IsContinuous (topology T) (topology T) ∧
    (translation g).inverse.IsContinuous (topology T) (topology T) := by
  have : (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T) (topology T) := by
    change (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T)
      ((AsSmall.equiv : T.ProEt ≌ Site T).inverse.inducedTopology (Scheme.ProEt.topology T))
    infer_instance
  have : AsSmall.up.IsContinuous (Scheme.ProEt.topology T) (topology T) :=
    inferInstanceAs ((AsSmall.equiv : T.ProEt ≌ Site T).functor.IsContinuous _ _)
  have : AsSmall.down.IsContinuous (topology T) (Scheme.ProEt.topology T) := inferInstance
  have := postcompose_continuous g
  have := postcompose_continuous g.symm
  have : (postcompose g.symm).inverse.IsContinuous (Scheme.ProEt.topology T)
      (Scheme.ProEt.topology T) := postcompose_continuous g
  have h₁ : ((postcompose g.symm).trans
      (AsSmall.equiv : T.ProEt ≌ Site T)).functor.IsContinuous
      (Scheme.ProEt.topology T) (topology T) :=
    Functor.isContinuous_comp (postcompose g.symm).functor AsSmall.up
    (Scheme.ProEt.topology T) (Scheme.ProEt.topology T) (topology T)
  have h₂ : ((postcompose g.symm).trans
      (AsSmall.equiv : T.ProEt ≌ Site T)).inverse.IsContinuous
      (topology T) (Scheme.ProEt.topology T) :=
    Functor.isContinuous_comp AsSmall.down (postcompose g.symm).inverse
    (topology T) (Scheme.ProEt.topology T) (Scheme.ProEt.topology T)
  exact ⟨Functor.isContinuous_comp AsSmall.down _ _ (Scheme.ProEt.topology T) _,
    Functor.isContinuous_comp _ AsSmall.up _ (Scheme.ProEt.topology T) _⟩

private theorem small_up_continuous {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) : AsSmall.up.IsContinuous J
      (AsSmall.down.inducedTopology J : GrothendieckTopology (AsSmall.{u + 1} C)) := by
  have : (AsSmall.equiv : C ≌ AsSmall.{u + 1} C).functor.IsDenseSubsite J
      ((AsSmall.equiv : C ≌ AsSmall.{u + 1} C).inverse.inducedTopology J) := inferInstance
  exact inferInstanceAs ((AsSmall.equiv : C ≌ AsSmall.{u + 1} C).functor.IsContinuous J
    ((AsSmall.equiv : C ≌ AsSmall.{u + 1} C).inverse.inducedTopology J))

private theorem small_restriction_equivalence {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u + 1}) :
    let K := AsSmall.down.inducedTopology J
    let _ : AsSmall.up.IsContinuous J K :=
      small_up_continuous J
    (SheafOfModules.pushforward.{u + 1} (F := AsSmall.up)
      (R := (AsSmall.down.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R)
      (𝟙 R)).IsEquivalence := by
  let K := AsSmall.down.inducedTopology J
  have : (AsSmall.equiv : C ≌ AsSmall.{u + 1} C).functor.IsDenseSubsite J K := by
    change (AsSmall.equiv : C ≌ AsSmall.{u + 1} C).functor.IsDenseSubsite J
      ((AsSmall.equiv : C ≌ AsSmall.{u + 1} C).inverse.inducedTopology J)
    infer_instance
  have : AsSmall.up.IsContinuous J K :=
    inferInstanceAs ((AsSmall.equiv : C ≌ AsSmall.{u + 1} C).functor.IsContinuous J K)
  have : AsSmall.down.IsContinuous K J := inferInstance
  have : (AsSmall.equiv : C ≌ AsSmall.{u + 1} C).inverse.IsContinuous K J :=
    inferInstanceAs (AsSmall.down.IsContinuous K J)
  let S := (AsSmall.down.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R
  let E := SheafOfModules.pushforwardPushforwardEquivalence.{u + 1}
    (AsSmall.equiv : C ≌ AsSmall.{u + 1} C) (J := J) (K := K)
    (R := S) (S := R) (𝟙 R) (𝟙 S)
    (by
      ext U x
      change R.obj.map (𝟙 _) x = x
      rw [CategoryTheory.Functor.map_id]
      rfl)
    (by
      ext U x
      change R.obj.map (𝟙 _) x = x
      rw [CategoryTheory.Functor.map_id]
      rfl)
  exact E.isEquivalence_functor

private theorem ambient_equivalence (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    (ambientModules T l).IsEquivalence := by
  have : (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T) (topology T) := by
    change (AsSmall.equiv : T.ProEt ≌ Site T).functor.IsDenseSubsite
      (Scheme.ProEt.topology T)
      ((AsSmall.equiv : T.ProEt ≌ Site T).inverse.inducedTopology (Scheme.ProEt.topology T))
    infer_instance
  have : AsSmall.up.IsContinuous (Scheme.ProEt.topology T) (topology T) :=
    inferInstanceAs ((AsSmall.equiv : T.ProEt ≌ Site T).functor.IsContinuous _ _)
  let R := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l))
  have : (SheafOfModules.pushforward.{u + 1} (F := AsSmall.up)
      (R := (AsSmall.down.sheafPushforwardContinuous RingCat.{u + 1}
        (topology T) (Scheme.ProEt.topology T)).obj R) (𝟙 R)).IsEquivalence :=
    small_restriction_equivalence (Scheme.ProEt.topology T) R
  exact inferInstanceAs ((SheafOfModules.pushforward.{u + 1} (F := AsSmall.up)
    (R := (AsSmall.down.sheafPushforwardContinuous RingCat.{u + 1}
      (topology T) (Scheme.ProEt.topology T)).obj R) (𝟙 R) ⋙
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l)).inverse).IsEquivalence)

private theorem postcompose_cocontinuous {T : Scheme.{u}} (g : T ≅ T) :
    (postcompose g).functor.IsCocontinuous
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology T) := by
  let _ := postcompose_continuous g.symm
  have : (postcompose g).inverse.IsContinuous
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology T) := postcompose_continuous g.symm
  exact ((postcompose g).toAdjunction.isCocontinuous_iff_coverPreserving
      (Scheme.ProEt.topology T) (Scheme.ProEt.topology T)).mpr
    (CoverPreserving.of_isContinuous _ _ _)

private theorem compatibility_monoid
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F : C ⥤ C) [F.IsContinuous J J] [F.IsCocontinuous J J]
    (Q : Cᵒᵖ ⥤ RingCat.{u + 1}) :
    let _ := Sheaf.monoidalCategory J Ab.{u + 1}
    let A := Mon.mk (Q ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})
    let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj F.op
    let L := presheafToSheaf J Ab.{u + 1}
    let S := F.sheafPushforwardContinuous Ab.{u + 1} J J
    ∃ b : L.mapMon.obj (W.mapMon.obj A) ≅ S.mapMon.obj (L.mapMon.obj A),
      b.hom.hom = (F.pushforwardContinuousSheafificationCompatibility
        Ab.{u + 1} J J).hom.app A.X := by
  let _ := Sheaf.monoidalCategory J Ab.{u + 1}
  let _ := Sheaf.braidedCategory J Ab.{u + 1}
  let P := Q ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}
  let R := Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} J Q
  let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj F.op
  let U := sheafToPresheaf J Ab.{u + 1}
  let S := F.sheafPushforwardContinuous Ab.{u + 1} J J
  let e := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    F Ab.{u + 1} J J
  let A := Mon.mk P
  let B := (presheafToSheaf J Ab.{u + 1}).mapMon.obj A
  let h : W.mapMon.obj A ⟶ U.mapMon.obj (S.mapMon.obj B) :=
    W.mapMon.map ((sheafificationAdjunction J Ab.{u + 1}).mapMon.unit.app A) ≫
      (Functor.mapMonCompIso (F := U) (G := W)).inv.app B ≫
      (Functor.mapMonNatIso e).hom.app B ≫
      (Functor.mapMonCompIso (F := S) (G := U)).hom.app B
  let b := ((sheafificationAdjunction J Ab.{u + 1}).mapMon.homEquiv
    (W.mapMon.obj A) (S.mapMon.obj B)).symm h
  have hb : toSheafify J (W.obj P) ≫ b.hom.hom =
      Functor.whiskerLeft F.op (toSheafify J P) := by
    have hh := ((sheafificationAdjunction J Ab.{u + 1}).mapMon.homEquiv
      (W.mapMon.obj A) (S.mapMon.obj B)).apply_symm_apply h
    have hh' := congrArg (fun f ↦ f.hom) hh
    change toSheafify J (W.obj P) ≫ b.hom.hom = _ at hh'
    rw [hh']
    change _ ≫ e.hom.app R ≫ 𝟙 _ = _
    rw [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
      Category.comp_id, Category.comp_id]
    rfl
  have heq : b.hom =
      (F.pushforwardContinuousSheafificationCompatibility Ab.{u + 1} J J).hom.app P := by
    apply (sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _ |>.injective
    change toSheafify J (W.obj P) ≫ b.hom.hom = _
    rw [hb]
    exact (F.toSheafify_pullbackSheafificationCompatibility Ab.{u + 1} J J P).symm
  have : IsIso b.hom := by rw [heq]; infer_instance
  have : IsIso ((Mon.forget _).map b) := inferInstanceAs (IsIso b.hom)
  have : IsIso b := isIso_of_reflects_iso b (Mon.forget _)
  exact ⟨asIso b, heq⟩


private theorem sectionRingIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F : C ⥤ C) [F.IsContinuous J J]
    (A : Mon (Sheaf J Ab.{u + 1})) [IsCommMonObj A.X]
    (c : A ≅ (F.sheafPushforwardContinuous Ab.{u + 1} J J).mapMon.obj A) :
    ∃ e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A.X ≅
      (F.sheafPushforwardContinuous CommRingCat.{u + 1} J J).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A.X),
    ∀ (V : Cᵒᵖ) (x : A.X.obj.obj V), e.hom.hom.app V x = c.hom.hom.hom.app V x := by
  let _ := Sheaf.monoidalCategory J Ab.{u + 1}
  let U := sheafToPresheaf J Ab.{u + 1}
  let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj F.op
  let S := F.sheafPushforwardContinuous Ab.{u + 1} J J
  let e := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    F Ab.{u + 1} J J
  let z : U.mapMon.obj (S.mapMon.obj A) ≅
      W.mapMon.obj (U.mapMon.obj A) :=
    (Functor.mapMonCompIso (F := S) (G := U)).symm.app A ≪≫
      (Functor.mapMonNatIso e).symm.app A ≪≫
      (Functor.mapMonCompIso (F := U) (G := W)).app A
  let m : U.mapMon.obj A ⟶ W.mapMon.obj (U.mapMon.obj A) :=
    U.mapMon.map c.hom ≫ z.hom
  have hm : m.hom = c.hom.hom.hom := by
    have hm₀ : m.hom = c.hom.hom.hom ≫ z.hom.hom := rfl
    rw [hm₀]
    have hz : z.hom.hom = 𝟙 _ ≫ e.inv.app A.X ≫ 𝟙 _ := rfl
    rw [hz, Category.id_comp, Category.comp_id]
    have heh : e.hom.app A.X = 𝟙 _ :=
      Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app
        F Ab.{u + 1} J J A.X
    have hh := e.inv_hom_id_app A.X
    rw [heh, Category.comp_id] at hh
    rw [hh]
    exact Category.comp_id c.hom.hom.hom
  let q := (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ Ab.{u + 1}).functor.map m
  let φ : InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u} J A.X ⟶
      F.op ⋙ InternalAbelianSheafModule.sectionRings.{u + 1, u + 1, u} J A.X :=
    { app := fun V ↦ ConcreteCategory.ofHom (C := CommRingCat)
        (InternalAbelianSheafModule.ringHom (q.app V).hom)
      naturality := fun V V' f ↦ by
        ext x
        exact ConcreteCategory.congr_hom (m.hom.naturality f) x }
  have hφ (V : Cᵒᵖ) : (φ.app V).hom.toAddMonoidHom = (c.hom.hom.hom.app V).hom :=
    congrArg (fun a ↦ (a.app V).hom) hm
  let f : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A.X ⟶
      (F.sheafPushforwardContinuous CommRingCat.{u + 1} J J).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A.X) := ⟨φ⟩
  have hφ' (V : Cᵒᵖ) (x : A.X.obj.obj V) : φ.app V x = c.hom.hom.hom.app V x :=
    congrArg (fun a ↦ a x) (hφ V)
  have : IsIso φ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hb := (ConcreteCategory.bijective_of_isIso (c.hom.hom.hom.app V))
    constructor
    · intro x y h
      apply hb.1
      exact (hφ' V x).symm.trans ((congrArg id h).trans (hφ' V y))
    · intro y
      obtain ⟨x, hx⟩ := hb.2 y
      exact ⟨x, (hφ' V x).trans hx⟩
  have : IsIso ((sheafToPresheaf J CommRingCat.{u + 1}).map f) :=
    inferInstanceAs (IsIso φ)
  have : IsIso f := isIso_of_reflects_iso f (sheafToPresheaf J CommRingCat.{u + 1})
  exact ⟨asIso f, hφ'⟩

private theorem invariant_coefficient_iso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F : C ⥤ C) [F.IsContinuous J J] [F.IsCocontinuous J J]
    (Q : Cᵒᵖ ⥤ RingCat.{u + 1})
    [IsCommMonObj (Q ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})]
    (p : Mon.mk (Q ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ≅
      ((Functor.whiskeringLeft _ _ Ab.{u + 1}).obj F.op).mapMon.obj
        (Mon.mk (Q ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}))) :
    ∃ e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J
        (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} J Q) ≅
      (F.sheafPushforwardContinuous CommRingCat.{u + 1} J J).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J
          (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} J Q)),
    ∀ (V : Cᵒᵖ) (x : Q.obj V),
      e.hom.hom.app V ((toSheafify J (Q ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})).app V x) =
        (toSheafify J (Q ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})).app (F.op.obj V)
          (p.hom.hom.app V x) := by
  let _ := Sheaf.monoidalCategory J Ab.{u + 1}
  let P := Q ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}
  let A := Mon.mk P
  let L := presheafToSheaf J Ab.{u + 1}
  obtain ⟨b, hb⟩ := compatibility_monoid J F Q
  let c := L.mapMon.mapIso p ≪≫ b
  have : IsCommMonObj (L.mapMon.obj A).X :=
    inferInstanceAs (IsCommMonObj (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} J Q))
  obtain ⟨e, he⟩ := sectionRingIso J F (L.mapMon.obj A) c
  refine ⟨e, fun V x ↦ ?_⟩
  have hc : c.hom.hom = L.map p.hom.hom ≫ b.hom.hom := rfl
  have hn : toSheafify J P ≫ c.hom.hom.hom =
      p.hom.hom ≫ Functor.whiskerLeft F.op (toSheafify J P) := by
    have hc' : c.hom.hom.hom =
        sheafifyMap J p.hom.hom ≫ b.hom.hom.hom :=
      congrArg (fun f ↦ f.hom) hc
    have hb' := congrArg (fun f ↦ f.hom) hb
    rw [hc', ← Category.assoc, ← toSheafify_naturality, Category.assoc, hb']
    exact congrArg (fun f ↦ p.hom.hom ≫ f)
      (F.toSheafify_pullbackSheafificationCompatibility Ab.{u + 1} J J P)
  exact (he V ((toSheafify J P).app V x)).trans
    (ConcreteCategory.congr_hom (congr_app hn V) x)

private theorem coefficient_iso {T : Scheme.{u}} (g : T ≅ T)
    (l : ℕ) [Fact l.Prime] :
    let _ := postcompose_continuous g
    ∃ e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l) ≅
      ((postcompose g).functor.sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.ProEt.topology T) (Scheme.ProEt.topology T)).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l)),
    ∀ (U : T.ProEtᵒᵖ) (x : (ProEtale.padicAlgClRingPresheaf T l).obj U),
      e.hom.hom.app U ((toSheafify (Scheme.ProEt.topology T)
        (ProEtale.padicAlgClRingPresheaf T l ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})).app U x) =
      (toSheafify (Scheme.ProEt.topology T)
        (ProEtale.padicAlgClRingPresheaf T l ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1})).app
          ((postcompose g).functor.op.obj U) x := by
  let _ := postcompose_continuous g
  let _ := postcompose_cocontinuous g
  let J := Scheme.ProEt.topology T
  let F := (postcompose g).functor
  let P := ProEtale.padicAlgClRingPresheaf T l ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}
  let _ := Sheaf.monoidalCategory J Ab.{u + 1}
  let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj F.op
  let A := Mon.mk P
  let p : A ≅ W.mapMon.obj A := Mon.mkIso (Iso.refl _)
    (by ext U x; rfl) (by
      simp only [Iso.refl_hom, MonoidalCategory.id_tensorHom_id, Category.comp_id,
        Category.id_comp])
  have : IsCommMonObj P :=
    (ProEtale.padicAlgClRingPresheaf T l).isCommMonObj_compForget₂
      (fun U (a b : ULift.{u + 1}
        (PadicAlgCl.finiteIntermediateFieldValued l U.unop.left)) ↦ mul_comm a b)
  obtain ⟨e, he⟩ := invariant_coefficient_iso J F
    (ProEtale.padicAlgClRingPresheaf T l) p
  exact ⟨e, fun V x ↦ he V x⟩

private theorem translation_coefficient {T : Scheme.{u}} (g : T ≅ T)
    (l : ℕ) [Fact l.Prime] :
    let _ := (translation_continuous g).1
    let _ := (translation_continuous g).2
    ∃ a : ((translation g).inverse.sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology T) (topology T)).obj (coefficient T l) ≅ coefficient T l,
      ∀ (U : Site T)
        (f : PadicAlgCl.finiteIntermediateFieldValued l (AsSmall.down.obj U).left),
      a.hom.hom.app (op U) (generator T l ((translation g).inverse.obj U) f) =
        generator T l U f := by
  let _ := (translation_continuous g).1
  let _ := (translation_continuous g).2
  let _ := postcompose_continuous g
  obtain ⟨e, he⟩ := coefficient_iso g l
  let r : coefficient T l ≅
      ((translation g).inverse.sheafPushforwardContinuous CommRingCat.{u + 1}
        (topology T) (topology T)).obj (coefficient T l) :=
    { hom := ⟨Functor.whiskerLeft AsSmall.down.op e.hom.hom⟩
      inv := ⟨Functor.whiskerLeft AsSmall.down.op e.inv.hom⟩
      hom_inv_id := by
        ext U x
        exact ConcreteCategory.congr_hom (congr_app (congrArg (fun f ↦ f.hom)
          e.hom_inv_id) (AsSmall.down.op.obj U)) x
      inv_hom_id := by
        ext U x
        exact ConcreteCategory.congr_hom (congr_app (congrArg (fun f ↦ f.hom)
          e.inv_hom_id) (AsSmall.down.op.obj U)) x }
  refine ⟨r.symm, fun U f ↦ ?_⟩
  have h : r.hom.hom.app (op U) (generator T l U f) =
      generator T l ((translation g).inverse.obj U) f :=
    he (op (AsSmall.down.obj U)) (ULift.up f)
  rw [← h]
  exact ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f ↦ f.hom) r.hom_inv_id) (op U)) (generator T l U f)

private theorem section_inverse_additive
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R).inverse.Additive :=
  by
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J R
  have : E.functor.Additive := { map_add := by intros; ext U x; rfl }
  infer_instance

private theorem small_ambient_additive
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (S : Sheaf J Ab.{u + 1}) [MonObj S] [IsCommMonObj S] :
    let _ := small_up_continuous J
    let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J S
    let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
    let K := (AsSmall.down.inducedTopology J : GrothendieckTopology (AsSmall.{u + 1} C))
    (SheafOfModules.pushforward.{u + 1} (F := AsSmall.up)
      (R := (AsSmall.down.sheafPushforwardContinuous RingCat K J).obj B) (𝟙 B) ⋙
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        J S).inverse).Additive := by
  let _ := small_up_continuous J
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J S
  let B := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let K := (AsSmall.down.inducedTopology J : GrothendieckTopology (AsSmall.{u + 1} C))
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J S
  have : E.inverse.Additive := section_inverse_additive J S
  let P := SheafOfModules.pushforward.{u + 1} (F := AsSmall.up)
    (R := (AsSmall.down.sheafPushforwardContinuous RingCat K J).obj B) (𝟙 B)
  have : P.Additive := { map_add := by intros; ext U x; rfl }
  exact inferInstanceAs (P ⋙ E.inverse).Additive

private theorem ambient_additive (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] :
    (ambientModules T l).Additive :=
  small_ambient_additive (Scheme.ProEt.topology T) (ProEtale.padicAlgClSheaf T l)

private theorem exists_realization (T : Scheme.{u}) (l : ℕ) [Fact l.Prime] (g : T ≅ T) :
    Nonempty (Realization T l g) := by
  let _ := (translation_continuous g).1
  let _ := (translation_continuous g).2
  obtain ⟨a, ha⟩ := translation_coefficient g l
  obtain ⟨P⟩ := TwistedActionRingedSite.presentation (topology T) (translation g)
    (coefficient T l) a
  have : (TwistedActionRingedSite.sigma (topology T) (translation g)
      (coefficient T l) a).IsEquivalence := by
    rw [← P.translation_eq]
    infer_instance
  have : (TwistedActionRingedSite.sigma (topology T) (translation g)
      (coefficient T l) a).Additive := by
    constructor
    intro M N f h
    ext U x
    rfl
  exact ⟨{
    ambientEquivalence := ambient_equivalence T l
    ambientAdditive := ambient_additive T l
    covering := CoverPreserving.of_isContinuous _ _ _
    inverseCovering := CoverPreserving.of_isContinuous _ _ _
    a := a
    functions := ha
    presentation := P }⟩

private theorem constructible_of_iso {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {M N : Modules T l} (e : M ≅ N) (h : Constructible T l M) : Constructible T l N := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun i ↦ ?_⟩
  exact ProEtale.CondensedRing.locallyFree_of_iso
    (((ProEtale.upperStar Ab.{u + 1} (S.immersion i)).mapMod
      (ProEtale.padicAlgClSheaf T l)).mapIso ((ambientModules T l).mapIso e)) (hS i)

private theorem derived_conservative {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) [HasDerivedCategory.{wA} (Modules T l)]
    [HasDerivedCategory.{wB} (Pairs D)] :
    (forget D).mapDerivedCategory.ReflectsIsomorphisms := by
  constructor
  intro X Y f hf
  have : IsIso ((forget D).mapDerivedCategory.map f) := hf
  rw [DerivedCategory.isIso_iff]
  intro n
  have h : IsIso ((DerivedCategory.homologyFunctor _ n ⋙ forget D).map f) :=
    (NatIso.isIso_map_iff
    ((forget D).mapDerivedCategoryHomologyFunctorIso n) f).mpr
      (show IsIso (((forget D).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor _ n).map f) from
          (show IsIso ((DerivedCategory.homologyFunctor _ n).map
            ((forget D).mapDerivedCategory.map f)) from inferInstance))
  have : IsIso ((forget D).map ((DerivedCategory.homologyFunctor _ n).map f)) := h
  exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor _ n).map f) (forget D)

private theorem preserves_injective {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) (K : CochainComplex (Pairs D) ℤ)
    (hK : K.IsKInjective) :
    CochainComplex.IsKInjective
      (((forget D).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  let _ := D.continuous
  let _ := D.inverseContinuous
  let I : Modules T l ⥤ Pairs D := D.presentation.induction
  have : PreservesFiniteLimits I := D.presentation.induction_limits
  have : PreservesFiniteColimits I := D.presentation.induction_colimits
  have : I.Additive := by
    constructor
    intro M N f g
    apply (forget D).map_injective
    exact D.presentation.induction_add f g
  have adj : I ⊣ forget D := D.presentation.inductionAdjunction
  let _ := adj.preservesKInjectiveComplexes
  let _ := hK
  infer_instance

private theorem action_additive {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) :
    let _ := D.continuous
    let _ := D.inverseContinuous
    D.presentation.modules.functor.Additive := by
  let _ := D.continuous
  let _ := D.inverseContinuous
  let _ := D.presentation.category
  let E : TwistedActionRingedSite.Modules D.presentation.coefficient ≌ Pairs D :=
    D.presentation.modules
  change E.functor.Additive
  constructor
  intro M N f g
  apply (forget D).map_injective
  exact D.presentation.modules_add f g

private theorem kflat_iso {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    {K L : CochainComplex (TwistedActionRingedSite.Modules R) ℤ} (e : K ≅ L)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) L := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  let _ := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let _ := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF i
  exact (hK F hF i).of_iso
    (((MonoidalCategory.curriedTensor _).map₂CochainComplex.obj F).mapIso e)

set_option backward.isDefEq.respectTransparency false in
private theorem flat_iso {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)} (e : M ≅ N)
    (hM : SheafOfModules.IsFlatOnSite (J := J) (R := R) M) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) N := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  change exactFunctor _ _ (SheafOfModules.siteSheafTensorRight.{u + 1, u + 1, u + 1, u + 1}
      (J := J) (A := R) M) at hM
  change exactFunctor _ _ (SheafOfModules.siteSheafTensorRight.{u + 1, u + 1, u + 1, u + 1}
      (J := J) (A := R) N)
  exact (exactFunctor _ _).prop_of_iso
    ((SheafOfModules.siteSheafTensorRightIso R M) ≪≫
      ((MonoidalCategory.curriedTensor _).flip.mapIso e) ≪≫
      (SheafOfModules.siteSheafTensorRightIso R N).symm) hM

set_option backward.isDefEq.respectTransparency false in
private theorem flat_comparison {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    SheafOfModules.IsFlat M ↔ SheafOfModules.IsFlatOnSite (J := J) (R := R) M := by
  let _ := SheafOfModules.isMonoidal_W_independentCoefficients R
  let _ := SheafOfModules.monoidalCategory R
  change exactFunctor _ _ (MonoidalCategory.tensorRight M) ↔
    exactFunctor _ _ (SheafOfModules.siteSheafTensorRight.{u + 1, u + 1, u + 1, u + 1}
      (J := J) (A := R) M)
  exact ⟨fun h ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R M).symm h,
    fun h ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R M) h⟩

private theorem preserves_flat {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) (K : CochainComplex (Pairs D) ℤ)
    (hk : KFlat D K) (hf : FlatTerms D K) :
    CochainComplex.IsKFlatIndependentCoefficients
      (((forget D).mapHomologicalComplex (.up ℤ)).obj K) ∧
      ∀ n, SheafOfModules.IsFlatOnSite (J := topology T) (R := coefficient T l)
        ((((forget D).mapHomologicalComplex (.up ℤ)).obj K).X n) := by
  let _ := D.continuous
  let _ := D.inverseContinuous
  let _ := D.presentation.category
  let E : TwistedActionRingedSite.Modules D.presentation.coefficient ≌ Pairs D :=
    D.presentation.modules
  have : E.functor.Additive := action_additive D
  let Ec := E.mapHomologicalComplex (.up ℤ)
  obtain ⟨F, hF, adj, hflat, _⟩ := RingedToposMorphism.exists_kFlatPullback
    (topology T) D.presentation.topology (coefficient T l)
    D.presentation.coefficient D.presentation.geometric
  let _ := hF
  let G : TwistedActionRingedSite.Modules D.presentation.coefficient ⥤ Modules T l :=
    E.functor ⋙ forget D
  have adjG : G ⊣ D.presentation.geometric.modules := D.presentation.modulePullback
  let e : F ≅ G := adj.leftAdjointUniq adjG
  obtain ⟨h₁, h₂⟩ := hflat (Ec.inverse.obj K)
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp hk)
    (fun n ↦ (flat_comparison _).mpr (hf n))
  let c : (F.mapHomologicalComplex (.up ℤ)).obj (Ec.inverse.obj K) ≅
      ((forget D).mapHomologicalComplex (.up ℤ)).obj K :=
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app (Ec.inverse.obj K)) ≪≫
      ((forget D).mapHomologicalComplex (.up ℤ)).mapIso (Ec.counitIso.app K)
  refine ⟨kflat_iso c
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr h₁), fun n ↦ ?_⟩
  exact flat_iso ((HomologicalComplex.eval _ (.up ℤ) n).mapIso c)
    ((flat_comparison _).mp (h₂ n))

private theorem flat_resolution {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) (K : CochainComplex (Pairs D) ℤ) :
    ∃ (L : CochainComplex (Pairs D) ℤ) (f : L ⟶ K),
      QuasiIso f ∧ KFlat D L ∧ FlatTerms D L ∧
        QuasiIso (((forget D).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  let _ := D.continuous
  let _ := D.inverseContinuous
  let _ := D.presentation.category
  let E : TwistedActionRingedSite.Modules D.presentation.coefficient ≌ Pairs D :=
    D.presentation.modules
  have : E.functor.Additive := action_additive D
  have : E.inverse.Additive := inferInstance
  let Ec := E.mapHomologicalComplex (.up ℤ)
  obtain ⟨P, p, hP, hflat, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (Ec.inverse.obj K)
  have : QuasiIso p := hp
  let f : Ec.functor.obj P ⟶ K := Ec.functor.map p ≫ Ec.counitIso.hom.app K
  have hq : QuasiIso f := by
    have : QuasiIso (Ec.functor.map p) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology p E.functor
    exact quasiIso_comp _ _
  refine ⟨Ec.functor.obj P, f, hq, ?_, ?_, ?_⟩
  · exact kflat_iso ((Ec.unitIso.app P)) hP
  · intro n
    let _ := SheafOfModules.isMonoidal_W_independentCoefficients D.presentation.coefficient
    let _ := SheafOfModules.monoidalCategory D.presentation.coefficient
    have h : SheafOfModules.IsFlatOnSite (J := D.presentation.topology)
        (R := D.presentation.coefficient) (P.X n) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso D.presentation.coefficient (P.X n)).symm
        (hflat n)
    exact flat_iso ((HomologicalComplex.eval _ (.up ℤ) n).mapIso (Ec.unitIso.app P)) h
  · have := hq
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f (forget D)

private theorem injective_resolution {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) :
    ∃ (I : CochainComplex (Pairs D) ℤ ⥤ CochainComplex (Pairs D) ℤ)
      (η : 𝟭 (CochainComplex (Pairs D) ℤ) ⟶ I),
      ∀ K : CochainComplex (Pairs D) ℤ,
        QuasiIso (η.app K) ∧ (I.obj K).IsKInjective ∧
          QuasiIso (((forget D).mapHomologicalComplex (ComplexShape.up ℤ)).map (η.app K)) := by
  have : IsGrothendieckAbelian.{u + 1} (Modules T l) :=
    (SheafOfModules.grothendieckAbelian_with_localized_generator
      (topology T) (coefficient T l)).1
  have : IsGrothendieckAbelian.{u + 1} (Pairs D) :=
    Endofunctor.IsoAlgebra.isGrothendieckAbelian (pullback D)
  refine ⟨CochainComplex.kInjectiveResolutionFunctor.{u + 1} (Pairs D),
    CochainComplex.toKInjectiveResolution.{u + 1} (Pairs D), fun K ↦ ?_⟩
  have hq := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1}
    (Pairs D) K).2
  have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1} (Pairs D)).app K) := hq
  exact ⟨hq, inferInstance, HomologicalComplex.quasiIso_map_of_preservesHomology _ (forget D)⟩

private theorem derived_constructible {T : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {g : T ≅ T} (D : Realization T l g) [HasDerivedCategory.{wA} (Modules T l)]
    [HasDerivedCategory.{wB} (Pairs D)] (K : DerivedCategory (Pairs D))
    (hb : DerivedCategory.TStructure.t.bounded K)
    (hc : ∀ n : ℤ, Constructible T l ((forget D).obj
      ((DerivedCategory.homologyFunctor _ n).obj K))) :
    DerivedCategory.TStructure.t.bounded ((forget D).mapDerivedCategory.obj K) ∧
      ∀ n : ℤ, Constructible T l ((DerivedCategory.homologyFunctor _ n).obj
        ((forget D).mapDerivedCategory.obj K)) := by
  refine ⟨(forget D).bounded_mapDerivedCategory_obj hb, fun n ↦ ?_⟩
  exact constructible_of_iso (((forget D).mapDerivedCategoryHomologyFunctorIso n).app K) (hc n)

/-- Frobenius action-site realization and preservation of resolutions.
Source: latest blueprint, cor-coef-verdier-weil-equivariance.proof.md,
internal-Hom/evaluation/transposition paragraph; native refinement, steps 1--7;
Stacks 015F, 06YS, 079P, 0G7E, 08BJ
(blueprint: lem-sf-weil-frobenius-action-resolutions).

Proof plan:
1. Postcompose bounded weakly etale objects by geometric Frobenius and its inverse.
Weak etaleness is unchanged by base isomorphisms; covering families depend on their
unchanged domains and arrows. The lifted small model retains all these objects.
Equivalences preserve pullbacks by their universal property.
2. Choose the inverse translation as s, so s.inverse reindexes along g. The site
equivalence induces the sheaf equivalence. Precomposition of continuous
functions with the domain homeomorphism preserves ring operations and the identical
finite coefficient field. Sheafification extends this normalized identification,
including its local finite-subextension condition and inverse.
3. Apply lem-sf-twisted-action-ringed-site. Its presentation supplies the ringed-topos
pullback, invertible ring map, diagonal tensor, contragredient Hom, symmetry and
evaluation comparisons, exact conservative forgetting, created limits and colimits,
and exact additive integer-orbit induction with its shifting and zero-summand formulas.
4. Exact forgetting descends termwise to a triangulated functor. Kernels and cokernels
identify cohomology naturally. Conservativity of ordinary forgetting and detection of
isomorphisms by every cohomology functor prove derived conservativity.
5. The same cohomology comparison preserves the finite interval and the same finite
locally closed stratification with pro-etale locally finite free restrictions.
6. Use 06YS for flat-term K-flat resolutions and 079P for a functorial K-injective
replacement on the action site. Transfer them along the displayed additive equivalence.
Tensor comparisons preserve total acyclic tensor tests, while the Hom bijections
preserve null homotopies. Thus both transported notions are the original ones.
7. Ringed pullback preserves flat-term K-flat complexes (0G7E). The exact LEFT orbit
adjoint implies forgetting preserves K-injectives (08BJ). Exactness preserves every
quasi-isomorphism, in particular both resolution augmentations. All localization is
of complexes of fixed pairs; no fixed-pair category in D(Modules) is substituted. -/
theorem frobenius_action_resolutions (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p) :
    ∃ A : Realization (D.geometricFiber T₀).left l (D.geometricFrobenius T₀),
      ∀ (_hA : HasDerivedCategory.{wA} (Modules (D.geometricFiber T₀).left l))
        (_hB : HasDerivedCategory.{wB} (Pairs A)), Nonempty (ResolutionAssertions A) := by
  obtain ⟨A⟩ := exists_realization (D.geometricFiber T₀).left l (D.geometricFrobenius T₀)
  refine ⟨A, fun _ _ ↦ ⟨{
    derived := ⟨inferInstance, derived_conservative A⟩
    cohomology := fun n ↦ ⟨((forget A).mapDerivedCategoryHomologyFunctorIso n).symm⟩
    constructible := derived_constructible A
    flat_resolution := flat_resolution A
    injective_resolution := injective_resolution A
    preserves_flat := preserves_flat A
    preserves_injective := preserves_injective A
    quasiIso := ?_ }⟩⟩
  intro K L f hf
  let _ := hf
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f (forget A)


end WeilConjectures.WeilFrobeniusAction
