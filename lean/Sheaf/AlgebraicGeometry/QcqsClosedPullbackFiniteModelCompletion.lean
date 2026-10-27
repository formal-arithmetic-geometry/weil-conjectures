/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.Paper.ProfinitePointPullback
public import Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import WeilConjectures.WeilObject.Sheaf.Stalk

/-!
# Closed inverse image: finite scalar models and normalized completion

Source: Stacks Project, proetale.tex, Tags 09BL and 099M; blueprint main-20261015,
proper base change unbounded pullback, Constructible complexes paragraph
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion).

The statements use ordinary unbounded internal-module derived categories. Completion is
specified on the existing strict quotient Roos representative, including both product
coordinates and the actual augmentation. Its localization is the derived-limit comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QcqsClosedPullback

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The existing internal-module category, abbreviated only for the displayed statements.
Source: blueprint ordinary module categories
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- Ordinary unbounded derived modules, with no completeness or boundedness built in.
Source: blueprint ordinary derived categories
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
abbrev Derived (X : Scheme.{u}) := DerivedCategory (Modules Λ X)

variable {Z V : Scheme.{u}} (i : Z ⟶ V)

section GeometricHelpers

set_option backward.isDefEq.respectTransparency true

attribute [local instance 20000] sheafBraidedCategory

attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  CondensedRing.upperStarComp upperStarFromPointComp
  Mod.extendScalarsIsoComapInv


private theorem pointModelIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((CondensedRing.upperStar Λ f).obj (((upperStarFromPoint Y).mapMod Λ).obj P) ≅
      ((upperStarFromPoint X).mapMod Λ).obj P) := by
  exact ⟨(CondensedRing.upperStarFromPointModComp Λ f).app P⟩

private theorem squareIso {X Y T W : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ Y) (a : W ⟶ X) (b : W ⟶ T)
    (h : a ≫ f = b ≫ g) (M : Modules Λ Y) :
    Nonempty ((CondensedRing.upperStar Λ a).obj ((CondensedRing.upperStar Λ f).obj M) ≅
      (CondensedRing.upperStar Λ b).obj ((CondensedRing.upperStar Λ g).obj M)) := by
  exact ⟨((CondensedRing.upperStarComp Λ a f).app M).symm ≪≫
    eqToIso (congrArg (fun q ↦ (CondensedRing.upperStar Λ q).obj M) h) ≪≫
      (CondensedRing.upperStarComp Λ b g).app M⟩

private theorem square_model {X Y T W : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ Y) (a : W ⟶ X) (b : W ⟶ T)
    (h : a ≫ f = b ≫ g) (M : Modules Λ Y)
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (he : Nonempty ((CondensedRing.upperStar Λ g).obj M ≅
      ((upperStarFromPoint T).mapMod Λ).obj P)) :
    Nonempty ((CondensedRing.upperStar Λ a).obj ((CondensedRing.upperStar Λ f).obj M) ≅
      ((upperStarFromPoint W).mapMod Λ).obj P) := by
  obtain ⟨e⟩ := he
  obtain ⟨es⟩ := squareIso Λ f g a b h M
  obtain ⟨ep⟩ := pointModelIso Λ b P
  exact ⟨es ≪≫ (CondensedRing.upperStar Λ b).mapIso e ≪≫ ep⟩

private theorem cover_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y) (a : 𝒰.I₀) :
    ∃ q : (𝒰.pullback₁ f).X a ⟶ 𝒰.X a,
      (𝒰.pullback₁ f).f a ≫ f = q ≫ 𝒰.f a := by
  exact ⟨pullback.snd f (𝒰.f a), pullback.condition⟩

private theorem cover_models {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules Λ Y) (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (P : 𝒰.I₀ → Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ)
    (he : ∀ a, Nonempty ((CondensedRing.upperStar Λ (𝒰.f a)).obj M ≅
      ((upperStarFromPoint (𝒰.X a)).mapMod Λ).obj (P a))) :
    ∀ a, Nonempty ((CondensedRing.upperStar Λ ((𝒰.pullback₁ f).f a)).obj
      ((CondensedRing.upperStar Λ f).obj M) ≅
      ((upperStarFromPoint ((𝒰.pullback₁ f).X a)).mapMod Λ).obj (P a)) := by
  intro a
  obtain ⟨q, hq⟩ := cover_square f 𝒰 a
  exact square_model Λ f (𝒰.f a) ((𝒰.pullback₁ f).f a) q hq M (P a) (he a)

private theorem localModel_iso {X : Scheme.{u}} {M N : Modules Λ X}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun a ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 a
  exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (𝒰.f a)).mapIso e).symm ≪≫ eP⟩⟩

private theorem localModel_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules Λ Y) (hM : HasFiniteConstantLocalModel Λ Y M) :
    HasFiniteConstantLocalModel Λ X ((CondensedRing.upperStar Λ f).obj M) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hM
  choose P hP he using h𝒰
  exact ⟨𝒰.pullback₁ f, fun a ↦ ⟨P a, hP a, cover_models Λ f M 𝒰 P he a⟩⟩

private theorem localModel_square {X Y T W : Scheme.{u}}
    (f : X ⟶ Y) (g : T ⟶ Y) (a : W ⟶ X) (b : W ⟶ T)
    (h : a ≫ f = b ≫ g) (M : Modules Λ Y)
    (hM : HasFiniteConstantLocalModel Λ T ((CondensedRing.upperStar Λ g).obj M)) :
    HasFiniteConstantLocalModel Λ W
      ((CondensedRing.upperStar Λ a).obj ((CondensedRing.upperStar Λ f).obj M)) := by
  obtain ⟨e⟩ := squareIso Λ f g a b h M
  exact localModel_iso Λ e.symm (localModel_pullback Λ b _ hM)

private theorem constructible_iso {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {M N : Modules Λ X}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, if_pos hqc] at hM ⊢
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ localModel_iso Λ
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

private theorem stratum_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : Scheme.Stratification Y) (a : Fin S.n) :
    ∃ q : (S.pullback f).domain a ⟶ S.domain a,
      (S.pullback f).immersion a ≫ f = q ≫ S.immersion a := by
  exact ⟨pullback.fst (S.immersion a) f, pullback.condition.symm⟩

private theorem constructible_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (M : Modules Λ Y) (hM : IsConstantModelConstructible Λ Y M) :
    IsConstantModelConstructible Λ X ((CondensedRing.upperStar Λ f).obj M) := by
  have hX : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  have hY : CompactSpace Y ∧ QuasiSeparatedSpace Y := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, if_pos hX, if_pos hY] at hM ⊢
  obtain ⟨S, hS⟩ := hM
  refine ⟨S.pullback f, fun a ↦ ?_⟩
  obtain ⟨q, hq⟩ := stratum_square f S a
  exact localModel_square Λ f (S.immersion a) ((S.pullback f).immersion a) q hq M (hS a)

private theorem composed_counit {C D B : Type*}
    [Category C] [Category D] [Category B]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ B} {I : B ⥤ D} {R : B ⥤ C}
    (a : F ⊣ G) (b : H ⊣ I) (e : I ⋙ G ≅ R)
    (ha : ∀ M, IsIso (a.counit.app M)) (hb : ∀ N, IsIso (b.counit.app N)) (N : B) :
    IsIso (((a.comp b).ofNatIsoRight e).counit.app N) := by
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Adjunction.comp_counit_app]
  have := ha (I.obj N)
  have := hb N
  infer_instance

private theorem lifted_counit {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Monoidal] [G.LaxMonoidal]
    (a : F ⊣ G) [a.IsMonoidal] (A : C) [MonObj A]
    (ha : ∀ M, IsIso (a.counit.app M)) (M : Mod D (F.obj A)) :
    IsIso ((a.mapModAdjunction A).counit.app M) := by
  have hh : IsIso ((Mod.forget _).map ((a.mapModAdjunction A).counit.app M)) := by
    change IsIso (((a.mapModAdjunction A).counit.app M).hom)
    rw [Adjunction.mapModAdjunction_counit_app_hom]
    exact ha M.X
  exact isIso_of_reflects_iso _ (Mod.forget _)

private theorem internal_closed_counit [IsClosedImmersion i] (N : Modules Λ Z) :
    IsIso ((CondensedRing.upperStarLowerStarAdjunction Λ i).counit.app N) := by
  have hab : IsIso (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).counit :=
    abelian_closed_counit i
  let scalar := Mod.extendRestrictAdjunction (condensedPullbackHom Λ i)
  have : (Mod.comap (condensedPullbackHom Λ i)).Full :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ i)).fullyFaithfulFunctor.full
  have : IsIso scalar.counit := scalar.counit_isIso_of_R_fully_faithful
  have : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i)
      Functor.Monoidal.toOplaxMonoidal _ := by
    exact isMonoidal_upperStarLowerStarAdjunction _ _
  exact composed_counit
    ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} i).mapModAdjunction
      (condensedRingObj Λ V)) scalar (CondensedRing.comapPullbackHomCompIso Λ i)
    (lifted_counit _ _ (fun _ ↦ inferInstance)) (fun _ ↦ inferInstance) N

end GeometricHelpers

private theorem tensor_test_isIso [IsClosedImmersion i]
    (K : Derived Λ V) (N : Modules Λ Z) : IsIso
      ((((CondensedRing.leftDerivedUpperStarTensor Λ i).app K).app
          ((DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.lowerStar Λ i).obj N))) ≫
        (((CondensedRing.moduleObjectDerivedPullback Λ i).obj K) ◁
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ i).hom.app _ ≫
            ((CondensedRing.upperStar Λ i).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
            (DerivedCategory.singleFunctor _ 0).map
              ((CondensedRing.upperStarLowerStarAdjunction Λ i).counit.app N)))) := by
  have := internal_closed_counit Λ i N
  infer_instance

/-- Finite scalar models on the specified pulled-back cover, constructibility, unchanged
Tor intervals and D_ctf are preserved. The last arrow is the canonical derived tensor
comparison followed by the degree-zero pullback comparison and the ordinary closed counit.
In particular the left-hand input is i_*N in degree zero, not Ri_*N.

Source: Stacks 09BL; blueprint proper base change unbounded pullback,
Constructible complexes paragraph
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion).

Proof in words, node steps 1--3: transport module operations and tensor through the
internal/section equivalence (lem-sfb-internal-module-operations-transport and
lem-pe-internal-section-tensor-comparison). The coefficient alpha is invertible
(lem-sfb-alpha-iso), so inverse image is exact, and its unbounded derived functor is
termwise (lem-weil-pbc-exact-functor-derived-factorization). Pull a finite constructible
stratification back to Z, using lem-pur-scheme-constructible-preimage and preservation
of locally closed immersions. Base change preserves the pro-etale cover by
lem-galois-fpqc-covering-base-change and
lem-weil-pbc-weakly-etale-composition-base-change. The scalar-matrix inverse image
lemma gives the same finite matrix and cokernel, hence the same scalar model on each
cover member. For N on Z, the derived tensor comparison
(lem-sfb-derived-pullback-tensor-comparison-iso) and closed counit
(lem-weil-pbc-proetale-ringed-closed-counit) give the specified tensor isomorphism.
Test Tor amplitude on the ordinary sheaf i_*N. Exact inverse image commutes with
cohomology (lem-weil-pbc-exact-functor-complex-cohomology), so the same interval works.
It also preserves bounded constructible cohomology, proving D_ctf preservation. -/
theorem finite_models_constructible_tor
    [IsClosedImmersion i] [CompactSpace V] [QuasiSeparatedSpace V]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (_hc : IsCompact (Set.range i)ᶜ) :
    (∀ (M : Modules Λ V) (𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage V)
      (P : 𝒰.I₀ → Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ),
      (∀ a : 𝒰.I₀, Mod.IsFinitelyPresented Λ (P a)) →
      (∀ a : 𝒰.I₀, Nonempty ((CondensedRing.upperStar Λ (𝒰.f a)).obj M ≅
        ((upperStarFromPoint (𝒰.X a)).mapMod Λ).obj (P a))) →
      ∀ a : 𝒰.I₀, Nonempty
        ((CondensedRing.upperStar Λ ((𝒰.pullback₁ i).f a)).obj
          ((CondensedRing.upperStar Λ i).obj M) ≅
        ((upperStarFromPoint ((𝒰.pullback₁ i).X a)).mapMod Λ).obj (P a))) ∧
    (∀ M : Modules Λ V, IsConstantModelConstructible Λ V M →
      IsConstantModelConstructible Λ Z ((CondensedRing.upperStar Λ i).obj M)) ∧
    (∀ K : Derived Λ V,
      (constantModelBoundedConstructible Λ V K ∧ DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ Z
        ((CondensedRing.moduleObjectDerivedPullback Λ i).obj K) ∧
      DerivedCategory.finiteTorAmplitude _
        ((CondensedRing.moduleObjectDerivedPullback Λ i).obj K)) ∧
    (∀ (a b : ℤ) (K : Derived Λ V), DerivedCategory.torAmplitudeIn _ a b K →
      DerivedCategory.torAmplitudeIn _ a b
        ((CondensedRing.moduleObjectDerivedPullback Λ i).obj K)) ∧
    (∀ (K : Derived Λ V) (N : Modules Λ Z), IsIso
      ((((CondensedRing.leftDerivedUpperStarTensor Λ i).app K).app
          ((DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.lowerStar Λ i).obj N))) ≫
        (((CondensedRing.moduleObjectDerivedPullback Λ i).obj K) ◁
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ i).hom.app _ ≫
            ((CondensedRing.upperStar Λ i).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
            (DerivedCategory.singleFunctor _ 0).map
              ((CondensedRing.upperStarLowerStarAdjunction Λ i).counit.app N))))) := by
  have htor (a b : ℤ) (K : Derived Λ V)
      (hK : DerivedCategory.torAmplitudeIn _ a b K) :
      DerivedCategory.torAmplitudeIn _ a b
        ((CondensedRing.moduleObjectDerivedPullback Λ i).obj K) := by
    intro N
    let F := CondensedRing.upperStar Λ i
    let T := K ⊗ (DerivedCategory.singleFunctor _ 0).obj
      ((CondensedRing.lowerStar Λ i).obj N)
    let e := (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ i).app T
    let t := (((CondensedRing.leftDerivedUpperStarTensor Λ i).app K).app
      ((DerivedCategory.singleFunctor _ 0).obj ((CondensedRing.lowerStar Λ i).obj N))) ≫
        (((CondensedRing.moduleObjectDerivedPullback Λ i).obj K) ◁
          ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ i).hom.app _ ≫
            (F.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
            (DerivedCategory.singleFunctor _ 0).map
              ((CondensedRing.upperStarLowerStarAdjunction Λ i).counit.app N)))
    have : IsIso t := tensor_test_isIso Λ i K N
    exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso
      (e.symm ≪≫ asIso t)
      (F.homologyConcentratedIn_mapDerivedCategory_obj (hK _))
  refine ⟨?_, constructible_pullback Λ i, ?_, htor, tensor_test_isIso Λ i⟩
  · intro M 𝒰 P _ he
    exact cover_models Λ i M 𝒰 P he
  · intro K hK
    obtain ⟨hbc, a, b, hT⟩ := hK
    refine ⟨⟨?_, ?_⟩, a, b, htor a b K hT⟩
    · exact DerivedCategory.TStructure.t.bounded.prop_of_iso
        ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ i).app K).symm
        ((CondensedRing.upperStar Λ i).bounded_mapDerivedCategory_obj hbc.1)
    · intro n
      exact constructible_iso Λ
        (((CondensedRing.upperStar Λ i).mapDerivedCategoryHomologyFunctorIso n).app K ≪≫
          ((DerivedCategory.homologyFunctor _ n).mapIso
            ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ i).app K)).symm)
        (constructible_pullback Λ i _ (hbc.2 n))


set_option backward.isDefEq.respectTransparency true

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The exact integral inverse image already defined by the module pushpull node.
Source: Stacks 09BL, integral specialization
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
def integralPull : AdicCompletion.Modules l E V ⥤ AdicCompletion.Modules l E Z :=
  CondensedRing.upperStar (DerivedNakayama.integerRing l E) i

/-- Additivity of the specified exact pullback, reused without unfolding its coefficient data.
Source: Stacks 09BL (blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
instance integralPull_additive : (integralPull i l E).Additive :=
  CondensedRing.upperStar_additive (DerivedNakayama.integerRing l E) i

/-- Exact pullback preserves finite limits.
Source: Stacks 09BL (blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
instance integralPull_finiteLimits : PreservesFiniteLimits (integralPull i l E) :=
  CondensedRing.preservesFiniteLimits_upperStar (DerivedNakayama.integerRing l E) i

/-- Exact pullback preserves finite colimits.
Source: Stacks 09BL (blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
instance integralPull_finiteColimits : PreservesFiniteColimits (integralPull i l E) :=
  CondensedRing.preservesFiniteColimits_upperStar (DerivedNakayama.integerRing l E) i

/-- The specified relative-tensor monoidal structure of the existing pullback.
Source: Stacks 09BL (blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
instance integralPull_monoidal : (integralPull i l E).Monoidal :=
  CondensedRing.monoidal_upperStar (DerivedNakayama.integerRing l E) i

/-- Termwise application of that exact inverse image to unbounded complexes.
Source: Stacks 09BL, exact localization
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
def integralPullComplex :
    CochainComplex (AdicCompletion.Modules l E V) ℤ ⥤
      CochainComplex (AdicCompletion.Modules l E Z) ℤ :=
  (integralPull i l E).mapHomologicalComplex (.up ℤ)

/-- First projection from the existing Roos coordinates at a fixed degree.
Source: Stacks 099M, strict Roos model
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
def roosFirst (X : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    (k : ℤ) : (AdicCompletion.roos l E X P).X k ⟶
      (AdicCompletion.product l E X P).X k := biprod.fst

/-- Second projection from the existing Roos coordinates, with the specified shift.
Source: Stacks 099M, strict Roos model
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
def roosSecond (X : Scheme.{u}) (P : CochainComplex (AdicCompletion.Modules l E X) ℤ)
    (k : ℤ) : (AdicCompletion.roos l E X P).X k ⟶
      (AdicCompletion.product l E X P).X (k - 1) := biprod.snd

/-- Evaluation of the first Roos coordinate at a quotient level.
Source: Stacks 099M (blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
def roosFirstEvaluation (X : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (k : ℤ) (n : ℕ) :
    (AdicCompletion.roos l E X P).X k ⟶ ((AdicCompletion.level l E X n).obj P).X k :=
  roosFirst l E X P k ≫
    (Pi.π (fun m : ℕ ↦ (AdicCompletion.level l E X m).obj P) n).f k

/-- Evaluation of the shifted second Roos coordinate at a quotient level.
Source: Stacks 099M (blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
def roosSecondEvaluation (X : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (k : ℤ) (n : ℕ) :
    (AdicCompletion.roos l E X P).X k ⟶
      ((AdicCompletion.level l E X n).obj P).X (k - 1) :=
  roosSecond l E X P k ≫
    (Pi.π (fun m : ℕ ↦ (AdicCompletion.level l E X m).obj P) n).f (k - 1)

/-- The regular-module comparison, with the point-pullback identifications made explicit.
Source: Stacks 09BL and the scalar-matrix comparison
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion). -/
def integralRegularComparison :
    (integralPull i l E).obj
      ((DerivedNakayama.pullback l E V).obj (Mod.regular (DerivedNakayama.integerRing l E))) ≅
      (DerivedNakayama.pullback l E Z).obj (Mod.regular (DerivedNakayama.integerRing l E)) :=
  (integralPull i l E).mapIso (DerivedNakayama.regularPullbackIso l E V) ≪≫
    scalarMatrixRegularPullbackIso (DerivedNakayama.integerRing l E) i ≪≫
      (DerivedNakayama.regularPullbackIso l E Z).symm

/-- The normalized strict quotient comparison. The coefficient isomorphisms have exactly
the underlying point-comparison maps. The reduction comparisons are the inverse tensorator
followed by those coefficient maps. Both Roos coordinates are the corresponding canonical
product comparison; augmentation has zero second coordinate. Scalar powers on the two free
terms of [A --pi^n--> A] are preserved by the same regular-module comparison.

Source: Stacks 09BL and 099M, and the node's normalized strict-Roos refinement
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion).

Proof in words, node steps 1, 4--5: the immersion inverse-image theorem gives preservation
of products; exactness and the internal/section equivalence transfer it to internal
modules. Exact countable products (lem-weil-proetale-countable-products-exact) allow
lem-cbc-exact-product-functor-strict-limit to compute derived inverse limits on the
strict product cone. Its comparison is the product comparison in both coordinates,
and takes (gamma,0) to (i^*gamma,0). The scalar-matrix lemma identifies the two free
terms and multiplication by pi^n in the quotient resolution. By
det-pe-derived-nakayama-resolution and lem-pe-principal-reduction-derived-normalization,
the scalar cone, transition (pi,id) and cone inclusion compute the actual quotient
extension/restriction, quotient transition and derived scalar-extension unit. Thus the
strict comparison preserves these transitions and units and the augmentation. This
construction is valid for every unbounded complex and uses no boundedness. -/
theorem normalized_strict_completion
    [IsClosedImmersion i] [CompactSpace V] [QuasiSeparatedSpace V]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (_hc : IsCompact (Set.range i)ᶜ) :
    ∃ (c : ∀ n : ℕ,
      (integralPull i l E).obj (AdicCompletion.finiteModule l E V n) ≅
        AdicCompletion.finiteModule l E Z n),
      (∀ n : ℕ, (c n).hom.hom =
        (profinitePointModuleForgetPullbackIso (DerivedNakayama.integerRing l E) i).hom.app
            (AdicCompletion.finiteModule l E V n) ≫
          (upperStarFromPointComp i).hom.app
            (DerivedNakayama.quotientModule l E (n + 1)).X) ∧
      ∀ P : CochainComplex (AdicCompletion.Modules l E V) ℤ,
      ∃ (b : ∀ n : ℕ,
        (integralPullComplex i l E).obj ((AdicCompletion.level l E V n).obj P) ≅
          (AdicCompletion.level l E Z n).obj ((integralPullComplex i l E).obj P))
        (e : (integralPullComplex i l E).obj (AdicCompletion.roos l E V P) ≅
          AdicCompletion.roos l E Z ((integralPullComplex i l E).obj P)),
        (∀ (n : ℕ) (k : ℤ), ((b n).hom.f k) =
          (Functor.Monoidal.μIso (integralPull i l E)
            (P.X k) (AdicCompletion.finiteModule l E V n)).inv ≫
              ((integralPull i l E).obj (P.X k) ◁ (c n).hom)) ∧
        (∀ n : ℕ,
          (integralPullComplex i l E).map (AdicCompletion.levelStep l E V P n) ≫
              (b n).hom =
            (b (n + 1)).hom ≫
              AdicCompletion.levelStep l E Z ((integralPullComplex i l E).obj P) n) ∧
        (∀ n : ℕ,
          (integralPullComplex i l E).map (AdicCompletion.levelUnit l E V P n) ≫
            (b n).hom = AdicCompletion.levelUnit l E Z
              ((integralPullComplex i l E).obj P) n) ∧
        (∀ (k : ℤ) (n : ℕ),
          e.hom.f k ≫ roosFirstEvaluation l E Z ((integralPullComplex i l E).obj P) k n =
            (integralPull i l E).map (roosFirstEvaluation l E V P k n) ≫ (b n).hom.f k) ∧
        (∀ (k : ℤ) (n : ℕ),
          e.hom.f k ≫ roosSecondEvaluation l E Z ((integralPullComplex i l E).obj P) k n =
            (integralPull i l E).map (roosSecondEvaluation l E V P k n) ≫
              (b n).hom.f (k - 1)) ∧
        ((integralPullComplex i l E).map (AdicCompletion.augmentation l E V P) ≫ e.hom =
          AdicCompletion.augmentation l E Z ((integralPullComplex i l E).obj P)) ∧
        (∀ (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
          (_hd : ∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
            (s : S.unop), ((d.hom.hom.app S) a).down s =
              Padic.coefficientExtensionUniformizer l E * a.down s)
          (n : ℕ) (_hn : 1 ≤ n),
          (integralPull i l E).map ((DerivedNakayama.pullback l E V).map (d ^ n)) ≫
              (integralRegularComparison i l E).hom =
            (integralRegularComparison i l E).hom ≫
              (DerivedNakayama.pullback l E Z).map (d ^ n)) ∧
        (∀ (K : DerivedCategory (AdicCompletion.Modules l E V))
            (_hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E V) (.up ℤ)).kFlat P)
            (a : DerivedCategory.Q.obj P ≅ K),
            (HomologicalComplex.quasiIso (AdicCompletion.Modules l E Z) (.up ℤ)).kFlat
              ((integralPullComplex i l E).obj P) ∧
            ∃ (aZ : DerivedCategory.Q.obj ((integralPullComplex i l E).obj P) ≅
              (CondensedRing.moduleObjectDerivedPullback (DerivedNakayama.integerRing l E) i).obj K)
              (c : (CondensedRing.moduleObjectDerivedPullback
                (DerivedNakayama.integerRing l E) i).obj
                (DerivedCategory.Q.obj (AdicCompletion.roos l E V P)) ≅
                  DerivedCategory.Q.obj
                    (AdicCompletion.roos l E Z ((integralPullComplex i l E).obj P))),
              aZ.inv =
                (CondensedRing.moduleObjectDerivedPullback (DerivedNakayama.integerRing l E) i).map
                    a.inv ≫
                  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                    (DerivedNakayama.integerRing l E) i).hom.app (DerivedCategory.Q.obj P) ≫
                  (integralPull i l E).mapDerivedCategoryFactors.hom.app P ∧
              c.hom =
                (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
                  (DerivedNakayama.integerRing l E) i).hom.app _ ≫
                  (integralPull i l E).mapDerivedCategoryFactors.hom.app _ ≫
                  DerivedCategory.Q.map e.hom ∧
              (integralPullComplex i l E).map (AdicCompletion.augmentation l E V P) ≫ e.hom =
                AdicCompletion.augmentation l E Z ((integralPullComplex i l E).obj P) ∧
              (CondensedRing.moduleObjectDerivedPullback (DerivedNakayama.integerRing l E) i).map
                  (AdicCompletion.completionMap l E V K P a) ≫ c.hom =
                AdicCompletion.completionMap l E Z
                  ((CondensedRing.moduleObjectDerivedPullback
                    (DerivedNakayama.integerRing l E) i).obj K)
                  ((integralPullComplex i l E).obj P) aZ) := by
  sorry

/-- Unbounded derived completeness is preserved, and the localized strict comparison
carries the completion unit to the actual completion unit of the pulled-back object.
The preceding theorem uses the existing derived-limit representatives, obtained
from the canonical quotient tower on a K-flat representative.

Source: Stacks 09BL and 099M, normalized unbounded completion consequence
(blueprint: lem-sfb-qcqs-closed-pullback-finite-model-completion).

Proof in words, node steps 4--6: choose a K-flat representative P. The normalized strict
comparison of the preceding statement identifies the products in both coordinates and
intertwines the zero-second-coordinate augmentation. Exact localization identifies its
source with i^* of the existing completion. K-flat pullback and the principal quotient
normalization identify its target with completion of i^*K, including its unit. These
identifications give the displayed augmented derived isomorphism, independently of P by
sk-def-pe-derived-completion. If K is complete its unit is invertible; its image under
inverse image remains invertible. The augmented comparison therefore makes the unit
of i^*K invertible, proving completeness. No truncation or boundedness is used. -/
theorem derived_completion
    [IsClosedImmersion i] [CompactSpace V] [QuasiSeparatedSpace V]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (_hc : IsCompact (Set.range i)ᶜ) :
    ∀ K : DerivedCategory (AdicCompletion.Modules l E V),
      IsDerivedComplete l E V K → IsDerivedComplete l E Z
        ((CondensedRing.moduleObjectDerivedPullback
          (DerivedNakayama.integerRing l E) i).obj K) := by
  intro K hK
  obtain ⟨P, hP, ⟨a⟩, hη⟩ := hK
  obtain ⟨c, _, hstrict⟩ := normalized_strict_completion i l E _hc
  obtain ⟨b, e, _, _, _, _, _, _, _, hderived⟩ := hstrict P
  obtain ⟨hPZ, aZ, cD, _, _, _, hunit⟩ := hderived K hP a
  have : IsIso (AdicCompletion.completionMap l E V K P a) :=
    by
      dsimp only [AdicCompletion.completionMap]
      infer_instance
  have : IsIso (AdicCompletion.completionMap l E Z
      ((CondensedRing.moduleObjectDerivedPullback (DerivedNakayama.integerRing l E) i).obj K)
      ((integralPullComplex i l E).obj P) aZ) := by
    rw [← hunit]
    infer_instance
  exact (AdicCompletion.isDerivedComplete_iff l E Z _ _ hPZ aZ).mpr inferInstance

end AlgebraicGeometry.ProEtale.QcqsClosedPullback
