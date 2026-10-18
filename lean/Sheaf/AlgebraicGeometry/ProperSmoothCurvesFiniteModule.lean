/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Sheaf.AlgebraicGeometry.ProperSmoothConnectedFibreDimensionLoci
import Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients
import Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Mathlib.Algebra.CharP.Lemmas
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.ConstructibleSheaf.Monoidal
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Integral
import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Constructibility for proper smooth families of curves with finite coefficients

Source: Stacks Project, more-etale.tex, Tag 0GKW; Tag 0GK3 for dimension zero,
and morphisms.tex, Tag 02G1 for the fibre-dimension decomposition
(blueprint: lem-weil-pbc-etale-proper-smooth-curves-finite-module).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open Limits Scheme in
private noncomputable def constantImage
    {C S : Scheme.{u}} (f : C ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) (q : ℤ) :
    Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  higherDirectImage Λ f q
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)

set_option backward.isDefEq.respectTransparency false in
open Limits Scheme in
private theorem finiteLocallyConstant_transfer
    {X : Scheme.{u}} (Λ Θ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [CommRing Θ] [Finite Θ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Θ))
    (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Θ) AddCommGrpCat.{u + 1})).obj G)
    (hF : Scheme.IsFiniteLocallyConstantSheaf F) :
    Scheme.IsFiniteLocallyConstantSheaf G := by
  obtain ⟨d, hd⟩ := (Scheme.finite_locally_constant_module_values_iff F).1.mpr hF
  have hl : Scheme.IsLisseModuleSheaf F := ⟨d.cover, hd⟩
  have hsets := (Scheme.lisseModuleSheaf_iff_underlying_finiteLocallyConstant F).mp hl
  let ef : (sheafCompose X.smallEtaleTopology
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F ≅
      (sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} Θ))).obj G :=
    (sheafCompose X.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso e
  have hgsets : Scheme.IsFiniteLocallyConstantSheafOfTypes
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} Θ))).obj G) := by
    constructor
    · obtain ⟨𝒰, h𝒰⟩ := hsets.1
      refine ⟨𝒰, fun i ↦ ?_⟩
      have : (((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F).over
          (𝒰.etalePrecoverageToEtale i)).IsConstant _ := h𝒰 i
      exact Sheaf.isConstant_congr _
        ((X.smallEtaleTopology.overPullback (Type (u + 1))
          (𝒰.etalePrecoverageToEtale i)).mapIso ef)
    · refine ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).mpr ?_⟩
      have : Finite ((pointSmallEtale s).sheafFiber.obj
          ((sheafCompose X.smallEtaleTopology
          (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj F)) :=
        (ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
          (hsets.2.isFinitelyGenerated_sheafFiber Ω s)
      exact Finite.of_equiv _ ((pointSmallEtale s).sheafFiber.mapIso ef).toEquiv
  obtain ⟨𝒰, h𝒰⟩ :=
    (Scheme.lisseModuleSheaf_iff_underlying_finiteLocallyConstant G).mpr hgsets
  let dG : Scheme.LocallyConstantDatum G := ⟨𝒰, fun i ↦ by
    obtain ⟨M, -, ⟨eM⟩⟩ := h𝒰 i
    exact Sheaf.isConstant_of_iso _ eM⟩
  exact (Scheme.finite_locally_constant_module_values_iff G).1.mp ⟨dG, h𝒰⟩

open Limits Scheme in
private theorem constructible_transfer
    {X : Scheme.{u}} (Λ Θ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [CommRing Θ] [Finite Θ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Θ))
    (e : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Θ) AddCommGrpCat.{u + 1})).obj G)
    (hF : Scheme.IsConstructibleSheaf F) : Scheme.IsConstructibleSheaf G := by
  obtain ⟨T, hT⟩ := hF
  refine ⟨T, fun i ↦ ?_⟩
  obtain ⟨eF⟩ := pullback_forget_modules_iso Λ (T.immersion i) F
  obtain ⟨eG⟩ := pullback_forget_modules_iso Θ (T.immersion i) G
  exact finiteLocallyConstant_transfer Λ Θ _ _
    (eF ≪≫ (upperStar AddCommGrpCat.{u + 1} (T.immersion i)).mapIso e ≪≫ eG.symm) (hT i)

open Limits Scheme in
private theorem finiteModule_devissage
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (P : ModuleCat.{u + 1} Λ → Prop)
    (hp : ∀ (p : ℕ), p.Prime → ∀ M : ModuleCat.{u + 1} Λ, Finite M →
      p • 𝟙 M = 0 → P M)
    (hext : ∀ (S : ShortComplex (ModuleCat.{u + 1} Λ)), S.ShortExact →
      P S.X₁ → P S.X₃ → P S.X₂)
    (M : ModuleCat.{u + 1} Λ) [Finite M] : P M := by
  have step (n : ℕ) : 0 < n → ∀ N : ModuleCat.{u + 1} Λ,
      Finite N → n • 𝟙 N = 0 → P N := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn N hN hkill
      let := hN
      by_cases hone : n = 1
      · have hid : 𝟙 N = 0 := by simpa [hone] using hkill
        exact hp 2 Nat.prime_two N hN (by rw [hid, smul_zero])
      · obtain ⟨p, hprime, m, hpm⟩ := Nat.exists_prime_and_dvd hone
        have hm : 0 < m := by
          by_contra h
          have hz : m = 0 := Nat.eq_zero_of_not_pos h
          simp [hz] at hpm
          omega
        have hmn : m < n := by
          rw [hpm]
          exact lt_mul_of_one_lt_left hm hprime.one_lt
        let φ : N ⟶ N := p • 𝟙 N
        let K := kernel φ
        let Q := cokernel (kernel.ι φ)
        let S := ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ))
          (cokernel.condition (kernel.ι φ))
        have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (kernel.ι φ) }
        have hKfin : Finite K :=
          Finite.of_injective (kernel.ι φ) ((ModuleCat.mono_iff_injective _).mp inferInstance)
        have hQfin : Finite Q :=
          Finite.of_surjective (cokernel.π (kernel.ι φ))
            ((ModuleCat.epi_iff_surjective _).mp inferInstance)
        have hK : p • 𝟙 K = 0 := by
          apply (cancel_mono (kernel.ι φ)).mp
          simpa [K, φ, Preadditive.nsmul_comp, Preadditive.comp_nsmul] using
            kernel.condition φ
        have hQ : m • 𝟙 Q = 0 := by
          have hcomp : (m • 𝟙 N) ≫ φ = 0 := by
            simpa [φ, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
              smul_smul, ← hpm, Nat.mul_comm] using hkill
          have h := Abelian.comp_coimage_π_eq_zero hcomp
          apply (cancel_epi (cokernel.π (kernel.ι φ))).mp
          simpa [Q, Abelian.coimage.π, Preadditive.nsmul_comp,
            Preadditive.comp_nsmul] using h
        exact hext S hS (hp p hprime K hKfin hK) (ih m hmn hm Q hQfin hQ)
  apply step (ringChar Λ)
    (Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite Λ (ringChar Λ))) M inferInstance
  ext x
  change ringChar Λ • x = 0
  rw [← Nat.cast_smul_eq_nsmul Λ, CharP.cast_eq_zero Λ (ringChar Λ), zero_smul]

-- Keep the derived categories abstract here: unfolding a composite functor on a
-- concrete category of sheaves makes the kernel normalize sheafification data.
open Limits Scheme in
private theorem exactFunctor_extension
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory B] [Z₀ : HasZeroMorphisms A] [Z : HasZeroMorphisms B]
    (K : A ⥤ B) [K.PreservesZeroMorphisms]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (Q : ObjectProperty (_root_.DerivedCategory B)) [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms]
    (T : ShortComplex A) (hT : T.ShortExact)
    (h₁ : Q ((_root_.DerivedCategory.singleFunctor B 0).obj (K.obj T.X₁)))
    (h₃ : Q ((_root_.DerivedCategory.singleFunctor B 0).obj (K.obj T.X₃))) :
    Q ((_root_.DerivedCategory.singleFunctor B 0).obj (K.obj T.X₂)) := by
  obtain rfl : Z = Preadditive.preadditiveHasZeroMorphisms := Subsingleton.elim _ _
  have hTK := hT.map_of_exact K
  exact Q.ext_of_isTriangulatedClosed₂ hTK.singleTriangle hTK.singleTriangle_distinguished h₁ h₃

open Limits Scheme in
private noncomputable def plusSingleUnboundedIso
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [EnoughInjectives A] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (X : A) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B q).obj
        (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≅
      (_root_.DerivedCategory.homologyFunctor B q).obj
        (F.rightDerivedFunctor.obj ((_root_.DerivedCategory.singleFunctor A 0).obj X)) :=
  (_root_.DerivedCategory.homologyFunctor B q).mapIso
    (F.rightDerivedFunctorPlusCompatibility.app
      ((DerivedCategory.Plus.singleFunctor A 0).obj X))

open Limits Scheme in
private theorem plusSingle_negative
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (X : A) (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor B q).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))) :=
  F.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
    ((DerivedCategory.Plus.singleFunctor A 0).obj X) 0 hq

open Limits Scheme in
private theorem constantImage_extension
    {C S : Scheme.{u}} (f : C ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (T : ShortComplex (ModuleCat.{u + 1} Λ)) (hT : T.ShortExact)
    (h₁ : DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      (((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₁))))
    (h₃ : DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      (((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₃)))) :
    DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      (((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₂))) := by
  let Q := (DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).inverseImage
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor
  have : (DerivedCategory.constructibleHomology
      (ModuleCat.{u + 1} Λ) S).IsClosedUnderIsomorphisms :=
    inferInstanceAs (_root_.DerivedCategory.homologyProperty
      (constructibleSheaf (ModuleCat.{u + 1} Λ) S)).IsClosedUnderIsomorphisms
  have : Q.IsTriangulated := inferInstance
  exact exactFunctor_extension
    (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) Q T hT h₁ h₃

open Limits Scheme in
private theorem constantImage_negative
    {C S : Scheme.{u}} (f : C ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) (q : ℤ) (hq : q < 0) :
    Scheme.IsConstructibleSheaf (constantImage f Λ M q) := by
  apply Scheme.IsConstructibleSheaf.of_isZero
  exact plusSingle_negative (lowerStar (ModuleCat.{u + 1} Λ) f)
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) q hq

open Limits Scheme in
private noncomputable def compositeIsoAt
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
    (e : F ⋙ G ≅ H ⋙ I) (K : A) : G.obj (F.obj K) ≅ I.obj (H.obj K) :=
  e.app K

open Limits Scheme in
private noncomputable def compositeSourceIsoAt
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    (e : F ⋙ G ≅ H) (K : A) : G.obj (F.obj K) ≅ H.obj K :=
  e.app K

open Limits Scheme in
private noncomputable def compIsoOfLeftIso
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ A) (G : A ⥤ B) (e : F ≅ 𝟭 A) : F ⋙ G ≅ G :=
  Functor.isoWhiskerRight e G ≪≫ Functor.leftUnitor G

open Limits Scheme in
private noncomputable def homologyMapIso
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F G : A ⥤ B) (H : B ⥤ D) (e : F ≅ G) (K : A) :
    H.obj (F.obj K) ≅ H.obj (G.obj K) :=
  H.mapIso (e.app K)

open Limits Scheme in
private noncomputable def homologyBaseChangeIso
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    (Rf : A ⥤ B) (gstar : E ⥤ F) (dg : B ⥤ C)
    (HqB : B ⥤ E) (HqC : C ⥤ F) (dfst : A ⥤ D) (Rpb : D ⥤ C)
    (eH : HqB ⋙ gstar ≅ dg ⋙ HqC) (eBC : Rf ⋙ dg ≅ dfst ⋙ Rpb)
    (K : A) (L : D) (eK : dfst.obj K ≅ L) :
    gstar.obj (HqB.obj (Rf.obj K)) ≅ HqC.obj (Rpb.obj L) :=
  compositeIsoAt HqB gstar dg HqC eH (Rf.obj K) ≪≫
    HqC.mapIso (compositeIsoAt Rf dg dfst Rpb eBC K) ≪≫
    HqC.mapIso (Rpb.mapIso eK)

open Limits Scheme in
private theorem constantImage_transfer
    {C S : Scheme.{u}} (f : C ⟶ S)
    (Λ Θ : Type (u + 1)) [CommRing Λ] [Finite Λ] [CommRing Θ] [Finite Θ]
    (M : ModuleCat.{u + 1} Λ) (N : ModuleCat.{u + 1} Θ) (q : ℤ)
    (e : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M ≅
      (forget₂ (ModuleCat.{u + 1} Θ) AddCommGrpCat.{u + 1}).obj N)
    (hM : Scheme.IsConstructibleSheaf (constantImage f Λ M q)) :
    Scheme.IsConstructibleSheaf (constantImage f Θ N q) := by
  obtain ⟨eM⟩ := nonempty_higherDirectImage_forget_iso Λ f q
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  obtain ⟨eN⟩ := nonempty_higherDirectImage_forget_iso Θ f q
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Θ)).obj N)
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) := inferInstance
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Θ) := inferInstance
  have : HasLimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1} := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1} := inferInstance
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := inferInstance
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} Θ) AddCommGrpCat.{u + 1}) := inferInstance
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} Λ
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (forget₂ (ModuleCat.{u + 1} Θ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} Θ
  have : C.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  have : C.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Θ) AddCommGrpCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  let eC := compositeIsoAt
      (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (sheafCompose C.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (constantCommuteCompose C.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) M ≪≫
    (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso e ≪≫
    (compositeIsoAt
      (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Θ))
      (sheafCompose C.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Θ) AddCommGrpCat.{u + 1}))
      (forget₂ (ModuleCat.{u + 1} Θ) AddCommGrpCat.{u + 1})
      (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (constantCommuteCompose C.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Θ) AddCommGrpCat.{u + 1})) N).symm
  let eH := (DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q).mapIso
    ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).mapIso
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).mapIso eC))
  exact constructible_transfer Λ Θ _ _ (eM ≪≫ eH ≪≫ eN.symm) hM

open Limits Scheme in
private theorem finiteVectorSpace_sum
    (R : Type (u + 1)) [CommRing R] (hR : IsField R)
    (V : ModuleCat.{u + 1} R) [Finite V] :
    ∃ n : ℕ, Nonempty (V ≅ ⨁ (fun _ : Fin n ↦ ModuleCat.of R R)) := by
  classical
  let : Field R := hR.toField
  let I := Module.Basis.ofVectorSpaceIndex R V
  let b := Module.Basis.ofVectorSpace R V
  let : Fintype I := Fintype.ofFinite I
  let b' := b.reindex (Fintype.equivFin I)
  exact ⟨Fintype.card I, ⟨b'.equivFun.toModuleIso ≪≫
    (ModuleCat.biproductIsoPi (fun _ : Fin (Fintype.card I) ↦ ModuleCat.of R R)).symm⟩⟩

open Limits Scheme in
private theorem constructible_finiteFree_image
    {R : Type (u + 1)} [CommRing R] {X : Scheme.{u}}
    {D E F : Type*} [Category D] [Category E] [Category F]
    (T₁ : ModuleCat.{u + 1} R ⥤ D)
    (T₂ : D ⥤ E) (T₃ : E ⥤ F)
    (T₄ : F ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    [(T₁ ⋙ T₂ ⋙ T₃ ⋙ T₄).Additive]
    (V : ModuleCat.{u + 1} R) (r : ℕ)
    (eV : V ≅ ⨁ (fun _ : Fin r ↦ ModuleCat.of R R))
    (hunit : Scheme.IsConstructibleSheaf
      (T₄.obj (T₃.obj (T₂.obj (T₁.obj (ModuleCat.of R R)))))) :
    Scheme.IsConstructibleSheaf (T₄.obj (T₃.obj (T₂.obj (T₁.obj V)))) := by
  let a : Fin r → ModuleCat.{u + 1} R := fun _ ↦ ModuleCat.of R R
  let T := T₁ ⋙ T₂ ⋙ T₃ ⋙ T₄
  have : T.Additive := inferInstance
  have (i : Fin r) : Scheme.IsConstructibleSheaf ((T.obj ∘ a) i) := hunit
  have : Scheme.IsConstructibleSheaf (⨁ (T.obj ∘ a)) :=
    Scheme.IsConstructibleSheaf.biproduct (T.obj ∘ a)
  exact Scheme.IsConstructibleSheaf.of_iso (F := ⨁ (T.obj ∘ a))
    (T.mapIso eV ≪≫ T.mapBiproduct a).symm

open Limits Scheme in
private theorem constantImage_primeKilled
    {C S : Scheme.{u}} (f : C ⟶ S)
    (hprime : ∀ (p : ℕ) [Fact p.Prime] (q : ℕ),
      Scheme.IsConstructibleEtaleModuleSheaf
        (constantImage f (ULift.{u + 1} (ZMod p))
          (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))) q))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (p : ℕ) (hp : p.Prime) (M : ModuleCat.{u + 1} Λ) [Finite M]
    (hkill : p • 𝟙 M = 0) (q : ℤ) :
    Scheme.IsConstructibleSheaf (constantImage f Λ M q) := by
  classical
  by_cases hq : q < 0
  · exact constantImage_negative f Λ M q hq
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hq)
  let : Fact p.Prime := ⟨hp⟩
  have hM : ∀ m : M, p • m = 0 := fun m ↦ by
    simpa using congrArg (fun g : M ⟶ M ↦ g m) hkill
  let : Module (ZMod p) M := AddCommGroup.zmodModule hM
  let R := ULift.{u + 1} (ZMod p)
  let : Module R M := Module.compHom M ULift.ringEquiv.toRingHom
  let V := ModuleCat.of R M
  have : ((lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctorPlus).Additive := by
    infer_instance
  obtain ⟨r, ⟨eV⟩⟩ := finiteVectorSpace_sum R (Field.toIsField R) V
  have hV : Scheme.IsConstructibleSheaf (constantImage f R V n) :=
    constructible_finiteFree_image
      (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} R))
      (DerivedCategory.Plus.singleFunctor _ 0)
      ((lowerStar (ModuleCat.{u + 1} R) f).rightDerivedFunctorPlus)
      (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)) V r eV
      ((Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hprime p n))
  exact constantImage_transfer f R Λ V M n (Iso.refl _) hV

open Limits Scheme in
private noncomputable def constantImage_unbounded_iso
    {C S : Scheme.{u}} (f : C ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ]
    (M : ModuleCat.{u + 1} Λ) (q : ℤ) :
    constantImage f Λ M q ≅
      (_root_.DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        (((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) :=
  plusSingleUnboundedIso (lowerStar (ModuleCat.{u + 1} Λ) f)
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) q

open Limits Scheme in
private theorem constantImage_allDegrees_iff
    {C S : Scheme.{u}} (f : C ⟶ S)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) :
    (∀ q, Scheme.IsConstructibleSheaf (constantImage f Λ M q)) ↔
      DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
        (((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  constructor
  · intro h q
    have := h q
    exact Scheme.IsConstructibleSheaf.of_iso (constantImage_unbounded_iso f Λ M q)
  · intro h q
    have := h q
    exact Scheme.IsConstructibleSheaf.of_iso (constantImage_unbounded_iso f Λ M q).symm

open Limits Scheme in
private theorem finiteCoefficients_of_prime
    {C S : Scheme.{u}} (f : C ⟶ S)
    (hprime : ∀ (p : ℕ) [Fact p.Prime] (q : ℕ),
      Scheme.IsConstructibleEtaleModuleSheaf
        (constantImage f (ULift.{u + 1} (ZMod p))
          (ModuleCat.of (ULift.{u + 1} (ZMod p)) (ULift.{u + 1} (ZMod p))) q))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf (constantImage f Λ M q) := by
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  have h : ∀ q, Scheme.IsConstructibleSheaf (constantImage f Λ M q) := by
    apply finiteModule_devissage Λ
      (fun N ↦ ∀ q, Scheme.IsConstructibleSheaf (constantImage f Λ N q))
    · intro p hp N hN hkill q
      let := hN
      exact constantImage_primeKilled f hprime Λ p hp N hkill q
    · intro T hT h₁ h₃
      apply (constantImage_allDegrees_iff f Λ T.X₂).mpr
      exact constantImage_extension f Λ T hT
        ((constantImage_allDegrees_iff f Λ T.X₁).mp h₁)
        ((constantImage_allDegrees_iff f Λ T.X₃).mp h₃)
  exact h q

open Limits Scheme in
private theorem constantSheaf_constructible
    (C : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    Scheme.IsConstructibleSheaf
      ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  let F := (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have hc : F.IsConstant C.smallEtaleTopology := Sheaf.isConstant_of_iso _ (Iso.refl _)
  have hF : Scheme.IsFiniteLocallyConstantSheaf F := {
    toIsLocallyConstantSheaf := hc.isLocallyConstantSheaf
    toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ by
      have hM : ConcreteCategory.IsFinitelyGenerated M :=
        (ModuleCat.isFinitelyGenerated_iff M).mpr inferInstance
      exact hM.of_iso ((pointSmallEtale s).sheafFiberConstantSheafIso M).symm⟩ }
  exact hF.isConstructibleSheaf

open Limits Scheme in
private theorem singleHomology_property
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (X : A) (hX : P X) (q : ℤ) :
    P ((DerivedCategory.Plus.homologyFunctor A q).obj
      ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := by
  let K := (DerivedCategory.Plus.singleFunctor A 0).obj X
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · exact P.prop_of_isZero (DerivedCategory.Plus.isZero_homology_of_isGE K 0 q hq)
  · exact P.prop_of_iso
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app X).symm hX
  · exact P.prop_of_isZero (DerivedCategory.Plus.isZero_homology_of_isLE K 0 q hq)

open Limits Scheme in
private theorem constantSingle_constructible
    (C : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
          ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  exact singleHomology_property (constructibleSheaf (ModuleCat.{u + 1} Λ) C)
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    (constantSheaf_constructible C Λ M) q

open Limits Scheme in
private theorem properShriekPlus_eq
    {C S : Scheme.{u}} (f : C ⟶ S) [IsProper f]
    (Λ : Type (u + 1)) [CommRing Λ] :
    rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsProper f) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 C)).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus := rfl

open Limits Scheme in
private theorem constantImage_quasiFinite
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] (hqf : f.IsQuasiFinite)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf (constantImage f Λ M q) := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  let A := ModuleCat.{u + 1} Λ
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj
    ((constantSheaf C.smallEtaleTopology A).obj M)
  have : QuasiCompact (Compactification.ofIsProper f).i := by
    change QuasiCompact (𝟙 C)
    infer_instance
  have h := constructibleCohomology_lowerShriek_of_quasiFinite Λ f hqf K
    (constantSingle_constructible C Λ M) (Compactification.ofIsProper f) q
  have hclosed : IsClosed (Set.range (𝟙 C : C ⟶ C).base) := by simp
  have : IsIso (openImmersionLowerShriekToLowerStar A (𝟙 C)) :=
    isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A (𝟙 C) hclosed
  let e := asIso (openImmersionLowerShriekToLowerStar A (𝟙 C)) ≪≫ lowerStarId A C
  let eD := Functor.mapDerivedCategoryPlusNatIso e ≪≫
    Functor.mapDerivedCategoryPlusIdIso (Sheaf C.smallEtaleTopology A)
  let eF : (openImmersionLowerShriek A (𝟙 C)).mapDerivedCategoryPlus ⋙
      (lowerStar A f).rightDerivedFunctorPlus ≅ (lowerStar A f).rightDerivedFunctorPlus :=
    compIsoOfLeftIso _ ((lowerStar A f).rightDerivedFunctorPlus) eD
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  have h' := (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp h
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        (((openImmersionLowerShriek A (𝟙 C)).mapDerivedCategoryPlus ⋙
          (lowerStar A f).rightDerivedFunctorPlus).obj K)) :=
    Eq.mp (congrArg (fun T : DerivedCategory.Plus (Sheaf C.smallEtaleTopology A) ⥤
        DerivedCategory.Plus (Sheaf S.smallEtaleTopology A) ↦
      Scheme.IsConstructibleSheaf ((DerivedCategory.Plus.homologyFunctor _ q).obj (T.obj K)))
        (properShriekPlus_eq f Λ)) h'
  exact Scheme.IsConstructibleSheaf.of_iso
    (homologyMapIso _ _ (DerivedCategory.Plus.homologyFunctor _ q) eF K)

open Limits Scheme in
private theorem geometricFibreDimension_eq
    {C S : Scheme.{u}} (f : C ⟶ S) (s : S) :
    topologicalKrullDim
      ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) = topologicalKrullDim (f.fiber s) := by
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s))))
  have : IsIntegralHom g := by
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.IsIntegral.isIntegral
  have : Surjective g := ⟨fun y ↦ by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (.of (AlgebraicClosure (S.residueField s)))))
    exact ⟨x, Subsingleton.elim _ _⟩⟩
  let π := pullback.fst (f.fiberToSpecResidueField s) g
  have he := IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.homeoOfIso (pullbackLeftPullbackSndIso f (S.fromSpecResidueField s) g)).isHomeomorph
  change topologicalKrullDim ↥(pullback f (g ≫ S.fromSpecResidueField s)) = _
  rw [← he]
  apply le_antisymm
  · exact topologicalKrullDim_le_of_continuous π.continuous
      (fun _ _ h hh ↦ π.eq_of_specializes_of_apply_eq_of_isIntegralHom h hh)
  · exact topologicalKrullDim_le_of_specializingMap
      π.isClosedMap.specializingMap π.surjective

open Limits Scheme in
private noncomputable def constantImage_restrictIso
    {C S B : Scheme.{u}} (f : C ⟶ S) (g : B ⟶ S) [Etale g]
    (Λ : Type (u + 1)) [CommRing Λ]
    (M : ModuleCat.{u + 1} Λ) (q : ℤ) :
    (upperStar (ModuleCat.{u + 1} Λ) g).obj (constantImage f Λ M q) ≅
      constantImage (pullback.snd f g) Λ M q := by
  let A := ModuleCat.{u + 1} Λ
  let F := (constantSheaf C.smallEtaleTopology A).obj M
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let sq := IsPullback.of_hasPullback f g
  have : IsIso (derivedBaseChangeMapPlus A sq.toCommSq) :=
    isIso_derivedBaseChangeMapPlus_of_etale Λ sq
  let eK := compositeIsoAt
      (DerivedCategory.Plus.singleFunctor _ 0)
      (upperStar A (pullback.fst f g)).mapDerivedCategoryPlus
      (upperStar A (pullback.fst f g))
      (DerivedCategory.Plus.singleFunctor _ 0)
      ((upperStar A (pullback.fst f g)).mapDerivedCategoryPlusSingleFunctor 0) F ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (compositeSourceIsoAt (constantSheaf C.smallEtaleTopology A)
        (upperStar A (pullback.fst f g))
        (constantSheaf (pullback f g).smallEtaleTopology A)
        (Scheme.upperStarConstantSheafIso A (pullback.fst f g)) M)
  exact homologyBaseChangeIso ((lowerStar A f).rightDerivedFunctorPlus) (upperStar A g)
    (upperStar A g).mapDerivedCategoryPlus
    (DerivedCategory.Plus.homologyFunctor _ q) (DerivedCategory.Plus.homologyFunctor _ q)
    (upperStar A (pullback.fst f g)).mapDerivedCategoryPlus
    ((lowerStar A (pullback.snd f g)).rightDerivedFunctorPlus)
    ((upperStar A g).mapDerivedCategoryPlusHomologyFunctorIso q)
    (asIso (derivedBaseChangeMapPlus A sq.toCommSq)) K _ eK

open Limits Scheme in
private theorem ordinaryFibreDimension_loci
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1) :
    ∃ U : Fin 2 → S.Opens,
      (∀ i, IsClosed (U i : Set S)) ∧
      Pairwise (fun i j ↦ Disjoint (U i : Set S) (U j : Set S)) ∧
      (⨆ i, U i) = ⊤ ∧ (pullback.snd f (U 0).ι).IsQuasiFinite ∧
      (∀ s : (U 1).toScheme,
        topologicalKrullDim ((pullback.snd f (U 1).ι).fiber s) = 1) := by
  have : IsNoetherian S := {}
  have hconnected (s : S) : ConnectedSpace
      ↥(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
          S.fromSpecResidueField s)) := inferInstance
  obtain ⟨U, hU, hclosed, hdis, hcover, -, hzero⟩ :=
    proper_smooth_connected_fibre_dimension_loci f 1 hconnected
      (fun s ↦ (geometricFibreDimension_eq f s).le.trans (h_dim s))
  refine ⟨U, hclosed, hdis, hcover, hzero, fun s ↦ ?_⟩
  rw [topologicalKrullDim_fiber_of_isPullback (IsPullback.of_hasPullback f (U 1).ι) s]
  have hs := (hU 1).le s.property
  simpa only [Set.mem_ofPred_eq, geometricFibreDimension_eq, Fin.val_one, Nat.cast_one,
    Scheme.Opens.ι_apply] using hs

/-- Higher direct images of a finite constant module in a proper smooth family with
nonempty geometrically connected fibres of dimension at most one are constructible.
The coefficient exponent need not be invertible on the base. `GeometricallyConnected`
includes nonempty fibres; dimension is measured on the residue-field fibres.

Source: Stacks Project, Tag 0GKW (dimension one), Tag 0GK3 (dimension zero),
and Tag 02G1 (locally constant smooth fibre dimension).
(blueprint: lem-weil-pbc-etale-proper-smooth-curves-finite-module)

Proof plan:
1. For finite coefficient rings, constructibility of the underlying abelian sheaf is
   equivalent to module constructibility. On constant finite abelian charts, trivialize
   each of the finitely many scalar endomorphisms using
   `lemma-constructible-hom-constant-locally` and refine the covers simultaneously.
   Read the module identities on a geometric stalk, using
   `lem-weil-pbc-constant-sheaf-geometric-stalk`; the constant values become modules.
   Forgetting scalars gives the converse; restrictions commute with forgetting by
   `lem-weil-pbc-exchange-forget-coefficients`.
2. By `lem-weil-pbc-proper-smooth-connected-fibre-dimension-loci`, split the base into
   open and closed dimension-zero and dimension-one loci, either of which may be empty.
   Exact restriction preserves injectives by `lem-weil-pbc-etale-restriction-injectives`
   and `lem-weil-pbc-site-pullback-abelian-exact`, so higher direct images restrict to
   the corresponding higher direct images. Constant inputs restrict to constants by
   `lemma-constructible-pullback-constant`. Finite stratifications concatenate.
3. On the dimension-zero locus the morphism is quasi-finite, proper and finitely
   presented. The base is Noetherian and quasi-compact; source and base are qcqs by
   `lem-weil-pbc-locally-noetherian-quasi-separated` and
   `lem-weil-pbc-qcqs-morphism-permanence`. Use the identity compactification and
   `lem-weil-pbc-etale-quasifinite-shriek-constructible` on the constant sheaf in
   degree zero. Identity extension by zero identifies proper shriek and direct image.
4. On the dimension-one locus, a finite abelian group killed by a prime is a finite
   dimensional vector space over the prime field. By `lem-weil-pbc-vector-space-free`
   choose a finite basis, including the empty basis for zero. Constant sheafification
   and additive derived functors preserve finite sums, by
   `lem-weil-pbc-sheafification-exact` and
   `lem-weil-pbc-right-derived-universal-delta-functor`. Apply
   `lem-weil-pbc-proper-smooth-curves-prime-coefficients`, and combine the summands
   using `thm-constructible-serre` and the coefficient comparison from step 1.
5. Induct on a positive integer n killing the finite abelian group B. For n = 1,
   B is zero. For n = l n' with l prime, use the exact sequence from B[l] to B
   onto l B. The kernel is killed by l and the quotient by n' < n. Constant
   sheafification is exact; the derived delta functor gives a five-term exact
   segment. The outer terms are constructible by step 4 and induction; the middle
   term is an extension of a cokernel by a kernel, so apply `thm-constructible-serre`.
   This uses `lem-weil-pbc-module-direct-image-left-exact` and
   `lem-weil-pbc-module-sheaves-enough-injectives`. In degree zero the preceding
   negative term is zero. No invertibility assumption enters.
6. The product of the additive orders kills the finite underlying group of M.
   Apply step 5, and upgrade to the given module structure using step 1 and
   `lem-weil-pbc-exchange-forget-coefficients`. Negative-degree cohomology is zero
   because the injective resolution starts in degree zero. Glue the two loci from
   step 2. This includes M = 0 and the zero coefficient ring.
-/
theorem properSmoothCurves_finiteModule_higherDirectImage_constructible
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  obtain ⟨U, hclosed, hdis, hcover, hzero, hone⟩ := ordinaryFibreDimension_loci f h_dim
  have (i : Fin 2) : CompactSpace (U i).toScheme :=
    isCompact_iff_compactSpace.mp (hclosed i).isCompact
  have : IsClosedImmersion (U 1).ι :=
    IsClosedImmersion.of_isOpenImmersion _ (by simpa using hclosed 1)
  have hcomp : Set.range (U 1).ι.base = (Set.range (U 0).ι.base)ᶜ := by
    simp only [Scheme.Opens.range_ι]
    ext s
    have hcov : U 0 ⊔ U 1 = ⊤ := by
      apply le_antisymm le_top
      rw [← hcover]
      apply iSup_le
      intro i
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    have hs : s ∈ U 0 ∨ s ∈ U 1 := by
      change s ∈ (U 0 ⊔ U 1 : S.Opens)
      rw [hcov]
      trivial
    have hd := Set.disjoint_left.mp (hdis (by decide : (0 : Fin 2) ≠ 1))
    constructor
    · intro h₁ h₀
      exact hd h₀ h₁
    · intro h₀
      exact hs.resolve_left h₀
  have h₀ : Scheme.IsConstructibleSheaf
      (constantImage (Limits.pullback.snd f (U 0).ι) Λ M q) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
      (constantImage_quasiFinite (Limits.pullback.snd f (U 0).ι) hzero Λ M q)
  have h₁ : Scheme.IsConstructibleSheaf
      (constantImage (Limits.pullback.snd f (U 1).ι) Λ M q) :=
    (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
      (finiteCoefficients_of_prime (Limits.pullback.snd f (U 1).ι)
        (fun p _ q ↦ properSmoothCurves_prime_higherDirectImage_constructible
          (Limits.pullback.snd f (U 1).ι) hone p q) Λ M q)
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
  apply (Scheme.isConstructibleSheaf_iff_upperStar (U 0).ι (U 1).ι hcomp _).mpr
  constructor
  · exact Scheme.IsConstructibleSheaf.of_iso (F := constantImage
      (Limits.pullback.snd f (U 0).ι) Λ M q)
      (constantImage_restrictIso f (U 0).ι Λ M q).symm
  · exact Scheme.IsConstructibleSheaf.of_iso (F := constantImage
      (Limits.pullback.snd f (U 1).ι) Λ M q)
      (constantImage_restrictIso f (U 1).ι Λ M q).symm


end AlgebraicGeometry.Etale
