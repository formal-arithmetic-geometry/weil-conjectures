/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.TraceFormula.TwoTermPerfectDeterminantData
public import Sheaf.TraceFormula.TwoTermDeterminantPullbackCoherence
public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition
public import WeilConjectures.AlgebraicGeometry.Modules.FlatResolution
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import Sheaf.TraceFormula.TwoTermPerfectTorWindow
import Sheaf.TraceFormula.AffineTwoTermDeterminant
import Sheaf.TraceFormula.AffineTwoTermDeterminantData
import Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus
import Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import WeilConjectures.RingTheory.CoverModuleExact
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.CategoryTheory.PeSiteSheafGluing
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.LinearAlgebra.Determinant

/-! # Canonical determinant sections in Tor degrees zero and one

Source: Stacks Project, perfect.tex Tags 0FJX and 0FJY, more-algebra.tex
Tags 0FJI and 0FJM; rank-zero cancellation of invertible twists.
(blueprint: lem-sfb-rank-zero-perfect-determinant-section).

The existing two-term model supplies the terms, ranks and exterior line. Only its
complex is reindexed into degrees 0,1, retaining the differential without a sign.
The exterior line is written in the existing dual-first order; the symmetry gives
exactly the order det(E¹) tensor det(E⁰) inverse in the node.

## Main definitions

* `IsRankZeroPerfect01`: the exact perfectness, Tor-window and virtual-rank condition.
* `RankZeroPerfectDeterminantSectionData`: the pair and all normalized comparisons.
* `rankZeroTwist`: ordinary tensor by an invertible module localized to the derived category.

## Main statements

* `exists_rankZeroPerfectDeterminantSectionData`: existence of the entire coherent family.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry

/-- The recorded two-term model in degrees 0 and 1, with unchanged differential.
Source: Stacks, Tag 0FJI, reindexing
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroDeterminantComplex {X : Scheme.{u}} (P : TwoTermDeterminantModel X) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  HomologicalComplex.double P.differential
    (c := ComplexShape.up ℤ) (i₀ := 0) (i₁ := 1) (by decide)

/-- The term map of a chain comparison, in either displayed term.
Source: Stacks, Tags 0FJI, 0FJM
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroDeterminantTermMap₀ {X : Scheme.{u}} (P Q : TwoTermDeterminantModel X)
    (q : rankZeroDeterminantComplex P ⟶ rankZeroDeterminantComplex Q) : P.neg ⟶ Q.neg :=
  (HomologicalComplex.doubleXIso₀ P.differential (c := ComplexShape.up ℤ)
    (i₀ := 0) (i₁ := 1) (by decide)).inv ≫ q.f 0 ≫
    (HomologicalComplex.doubleXIso₀ Q.differential (c := ComplexShape.up ℤ)
      (i₀ := 0) (i₁ := 1) (by decide)).hom

/-- The degree-one term map. Source: Stacks, Tag 0FJM
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroDeterminantTermMap₁ {X : Scheme.{u}} (P Q : TwoTermDeterminantModel X)
    (q : rankZeroDeterminantComplex P ⟶ rankZeroDeterminantComplex Q) :
    P.nonneg ⟶ Q.nonneg :=
  (HomologicalComplex.doubleXIso₁ P.differential (c := ComplexShape.up ℤ)
    (i₀ := 0) (i₁ := 1) (by decide) (by decide)).inv ≫ q.f 1 ≫
    (HomologicalComplex.doubleXIso₁ Q.differential (c := ComplexShape.up ℤ)
      (i₀ := 0) (i₁ := 1) (by decide) (by decide)).hom

/-- Ordinary termwise tensor by an invertible module, as a functor on the shared
module category. Its exactness comes from the existing tensor-inverse equivalence.
Source: Stacks, Tag 0FJ9, invertible twists
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroTwistModules (X : Scheme.{u}) (N : X.Modules) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace) :=
  tensorRight (C := X.Modules) N

/-- Tensoring is additive. Source: Stacks, Tag 0FJ9
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
instance rankZeroTwistModules_additive (X : Scheme.{u}) (N : X.Modules) :
    (rankZeroTwistModules X N).Additive := inferInstanceAs (tensorRight N).Additive

/-- Tensoring by an invertible module preserves finite limits, by its tensor inverse.
Source: Stacks, Tag 0FJ9
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
instance rankZeroTwistModules_limits (X : Scheme.{u}) (N : X.Modules) [N.IsInvertible] :
    PreservesFiniteLimits (rankZeroTwistModules X N) :=
  inferInstanceAs (PreservesFiniteLimits
    (BraidedCategory.tensorRightEquivalence N (dual N) (asIso (dualEvaluation N))).functor)

/-- Tensoring by an invertible module preserves finite colimits, by its tensor inverse.
Source: Stacks, Tag 0FJ9
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
instance rankZeroTwistModules_colimits (X : Scheme.{u}) (N : X.Modules) [N.IsInvertible] :
    PreservesFiniteColimits (rankZeroTwistModules X N) :=
  inferInstanceAs (PreservesFiniteColimits
    (BraidedCategory.tensorRightEquivalence N (dual N) (asIso (dualEvaluation N))).functor)

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- Localization of the reindexed model, in the fixed derived-category universe.
Source: Stacks, Tag 0FJX
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroModelObject {X : Scheme.{u}} (P : TwoTermDeterminantModel X) :
    schemeDerivedCategory.{u, w} X :=
  DerivedCategory.Q.{w}.obj (rankZeroDeterminantComplex P)

/-- Localization of a chain comparison in that same category.
Source: Stacks, Tag 0FJM
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroModelMap {X : Scheme.{u}} (P Q : TwoTermDeterminantModel X)
    (q : rankZeroDeterminantComplex P ⟶ rankZeroDeterminantComplex Q) :
    rankZeroModelObject P ⟶ rankZeroModelObject Q :=
  (DerivedCategory.Q.{w}
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map q

/-- Tensor pullback is additive, as supplied by its recorded adjunction.
Source: Stacks, Tags 0095, 0096
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
instance rankZeroPullbackAdditive {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (tensorPullback g).Additive :=
  (tensorPullbackSectionAdjunction g).left_adjoint_additive

/-- Ordinary tensor pullback of a cochain complex, using the recorded adjunction
for additivity. This is a definition-level operation, independent of cotangent complexes.
Source: Stacks, Tag 0095
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroPullbackComplex {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ :=
  letI := (tensorPullbackSectionAdjunction g).left_adjoint_additive
  ((tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P

/-- The component of the original universal counit at a complex, with no new choice
of a counit. It is invertible on K-flat complexes, but the map itself needs no such hypothesis.
Source: Stacks, Tag 06YJ
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroPullbackCounit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    (derivedPullback g).obj (DerivedCategory.Q.{w}.obj P) ⟶
      DerivedCategory.Q.{w}.obj (rankZeroPullbackComplex g P) :=
  (recordedDerivedPullbackCounit g).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- The canonical module comparison for pulling back a twist. The components are
uniquely fixed on pure tensor sections by the published tensor-pullback theorem.
Source: Stacks, Tag 01CD
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroTwistPullbackModules {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules) :
    tensorRight (C := X.Modules) N ⋙ tensorPullback g ≅
      tensorPullback g ⋙ tensorRight (C := Y.Modules) ((tensorPullback g).obj N) :=
  NatIso.ofComponents
    (fun M ↦ (Classical.choose (module_pullback_tensor g)) M N)
    (fun {M M' : X.Modules} (f : M ⟶ M') ↦ by
      have h := (Classical.choose_spec (module_pullback_tensor g)).1 M N M' N f (𝟙 N)
      have hi : (tensorPullback g).map (𝟙 N) = 𝟙 ((tensorPullback g).obj N) :=
        (tensorPullback g).map_id N
      rw [hi] at h
      simpa only [Functor.comp_map, tensorRight, curriedTensor, Functor.flip,
        tensorHom_id] using h)

/-- The same canonical comparison applied in each degree, with no flatness on g.
Source: Stacks, Tags 01CD and 0FJY
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroTwistPullbackComplex {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    rankZeroPullbackComplex g
      (((rankZeroTwistModules X N).mapHomologicalComplex (.up ℤ)).obj P) ≅
    ((rankZeroTwistModules Y ((tensorPullback g).obj N)).mapHomologicalComplex (.up ℤ)).obj
      (rankZeroPullbackComplex g P) :=
  letI := rankZeroPullbackAdditive g
  letI : (rankZeroTwistModules Y ((tensorPullback g).obj N)).Additive :=
    rankZeroTwistModules_additive Y _
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (rankZeroTwistModules X N ⋙ tensorPullback g)) (.up ℤ)).app P ≪≫
    (NatIso.mapHomologicalComplex (rankZeroTwistPullbackModules g N) (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (tensorPullback g ⋙ rankZeroTwistModules Y ((tensorPullback g).obj N)))
        (.up ℤ)).app P).symm

/-- The exact invertible twist on the recorded derived category, computed termwise.
Source: Stacks, Tag 0FJ9
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroTwist (X : Scheme.{u}) (N : X.Modules) (hN : N.IsInvertible) :
    schemeDerivedCategory X ⥤ schemeDerivedCategory X :=
  letI := hN
  (rankZeroTwistModules X N).mapDerivedCategory

/-- Its canonical comparison on a complex, supplied by localization.
Source: Stacks, Tag 0FJ9
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroTwistFactors (X : Scheme.{u}) (N : X.Modules) (hN : N.IsInvertible) :
    DerivedCategory.Q ⋙ rankZeroTwist X N hN ≅
      (rankZeroTwistModules X N).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  letI := hN
  (rankZeroTwistModules X N).mapDerivedCategoryFactors

/-- The twist map induced by an isomorphism of invertible modules.
Source: Stacks, Tag 0FJ9
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroTwistMap (X : Scheme.{u}) (N M : X.Modules)
    (hN : N.IsInvertible) (hM : M.IsInvertible) (e : N ≅ M) :
    rankZeroTwist X N hN ≅ rankZeroTwist X M hM :=
  letI := hN
  letI := hM
  Functor.mapDerivedCategoryNatIso ((tensoringRight X.Modules).mapIso e)

/-- Trivializing a twist is the localization of `x tensor n` mapping to `x`.
Source: Stacks, Tag 0FJ9
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroTwistTrivialization (X : Scheme.{u}) (N : X.Modules)
    (hN : N.IsInvertible) (e : N ≅ 𝟙_ X.Modules) :
    rankZeroTwist X N hN ≅ 𝟭 (schemeDerivedCategory X) :=
  letI := hN
  letI : (𝟭 X.Modules).Additive := ⟨rfl⟩
  letI : (𝟭 (SheafOfModules.{u} (moduleRings X.toRingedSpace))).Additive := ⟨rfl⟩
  letI : PreservesFiniteLimits (𝟭 X.Modules) :=
    inferInstanceAs (PreservesFiniteLimits
      (𝟭 (SheafOfModules.{u} (moduleRings X.toRingedSpace))))
  letI : PreservesFiniteColimits (𝟭 X.Modules) :=
    inferInstanceAs (PreservesFiniteColimits
      (𝟭 (SheafOfModules.{u} (moduleRings X.toRingedSpace))))
  Functor.mapDerivedCategoryNatIso
    ((tensoringRight X.Modules).mapIso e ≪≫ rightUnitorNatIso X.Modules) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The product comparison is the localization of the ordinary tensor associator.
Source: Stacks, Tag 0FJ9
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroTwistProduct (X : Scheme.{u}) (N M : X.Modules)
    (hN : N.IsInvertible) (hM : M.IsInvertible) (hNM : (N ⊗ M).IsInvertible) :
    rankZeroTwist X N hN ⋙ rankZeroTwist X M hM ≅ rankZeroTwist X (N ⊗ M) hNM :=
  letI := hN
  letI := hM
  letI := hNM
  letI := comp_preservesFiniteLimits (rankZeroTwistModules X N) (rankZeroTwistModules X M)
  letI := comp_preservesFiniteColimits (rankZeroTwistModules X N) (rankZeroTwistModules X M)
  (Functor.mapDerivedCategoryCompIso (rankZeroTwistModules X N)
    (rankZeroTwistModules X M)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (tensorRightTensor N M).symm

/-- A unit of the structure sheaf, equivalently its module automorphism, acts on
all terms; localizing this natural automorphism gives its action on every derived object.
Source: Stacks, Tags 0FJ9, 0FJI
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroScalar (X : Scheme.{u}) (a : (𝟙_ X.Modules) ≅ 𝟙_ X.Modules) :
    𝟭 (schemeDerivedCategory X) ≅ 𝟭 (schemeDerivedCategory X) :=
  letI : (𝟭 X.Modules).Additive := ⟨rfl⟩
  letI : (𝟭 (SheafOfModules.{u} (moduleRings X.toRingedSpace))).Additive := ⟨rfl⟩
  letI : PreservesFiniteLimits (𝟭 X.Modules) :=
    inferInstanceAs (PreservesFiniteLimits
      (𝟭 (SheafOfModules.{u} (moduleRings X.toRingedSpace))))
  letI : PreservesFiniteColimits (𝟭 X.Modules) :=
    inferInstanceAs (PreservesFiniteColimits
      (𝟭 (SheafOfModules.{u} (moduleRings X.toRingedSpace))))
  (Functor.mapDerivedCategoryIdIso _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((leftUnitorNatIso X.Modules).symm ≪≫ (tensoringLeft X.Modules).mapIso a ≪≫
        leftUnitorNatIso X.Modules) ≪≫ Functor.mapDerivedCategoryIdIso _

variable [∀ (X : Scheme.{u}) (U : X.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]

/-- Perfect, Tor amplitude [0,1], and virtual rank zero in every local model.
The rank equality is pointwise, so no rank is assigned to a module on an empty open.
Source: Stacks, Tag 0FJX, with degrees reindexed
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
@[irreducible]
def IsRankZeroPerfect01 (X : Scheme.{u}) : ObjectProperty (schemeDerivedCategory X) :=
  fun K ↦ Scheme.IsPerfect X K ∧
    (∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i : ℤ),
      i < 0 ∨ 1 < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (K ⊗ (DerivedCategory.singleFunctor _ 0).obj M))) ∧
    ∀ (U : X.Opens) (P : TwoTermDeterminantModel U.toScheme),
      Nonempty ((derivedPullback U.ι).obj K ≅
        rankZeroModelObject P) →
      ∀ _x : U, P.negRank = P.nonnegRank

/-- The source condition as an object property, with no auxiliary choice of models.
Source: Stacks, Tag 0FJX
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
abbrev RankZeroPerfect01Core (X : Scheme.{u}) :=
  Core (IsRankZeroPerfect01 X).FullSubcategory

/-- The value of a core-valued determinant functor.
Source: Stacks, Tag 0FJX
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroDeterminantValue {X : Scheme.{u}}
    (F : RankZeroPerfect01Core X ⥤ Core X.Modules)
    (K : schemeDerivedCategory X) (hK : IsRankZeroPerfect01 X K) : X.Modules :=
  (F.obj (Core.mk ⟨K, hK⟩)).of

/-- The line isomorphism induced by an actual derived isomorphism. Functor laws
encode identities and composition, including every change of local model.
Source: Stacks, Tag 0FJX
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroDeterminantIso {X : Scheme.{u}}
    (F : RankZeroPerfect01Core X ⥤ Core X.Modules)
    {K L : schemeDerivedCategory X} (hK : IsRankZeroPerfect01 X K)
    (hL : IsRankZeroPerfect01 X L) (e : K ≅ L) :
    rankZeroDeterminantValue F K hK ≅ rankZeroDeterminantValue F L hL :=
  let x : RankZeroPerfect01Core X := Core.mk ⟨K, hK⟩
  let y : RankZeroPerfect01Core X := Core.mk ⟨L, hL⟩
  let e' : x.of ≅ y.of := (IsRankZeroPerfect01 X).isoMk e
  (F.map (CoreHom.mk e')).iso

/-- Degree-zero map of an ordinary pulled-back model.
Source: Stacks, Tag 0FJY
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroPullbackTermMap₀ {X Y : Scheme.{u}} (g : Y ⟶ X)
    (P : TwoTermDeterminantModel X) (Q : TwoTermDeterminantModel Y)
    (q : rankZeroPullbackComplex g (rankZeroDeterminantComplex P) ⟶
      rankZeroDeterminantComplex Q) : (tensorPullback g).obj P.neg ⟶ Q.neg :=
  (tensorPullback g).map
    (HomologicalComplex.doubleXIso₀ P.differential (c := ComplexShape.up ℤ)
      (i₀ := 0) (i₁ := 1) (by decide)).inv ≫ q.f 0 ≫
      (HomologicalComplex.doubleXIso₀ Q.differential (c := ComplexShape.up ℤ)
        (i₀ := 0) (i₁ := 1) (by decide)).hom

/-- Degree-one map of an ordinary pulled-back model.
Source: Stacks, Tag 0FJY
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
def rankZeroPullbackTermMap₁ {X Y : Scheme.{u}} (g : Y ⟶ X)
    (P : TwoTermDeterminantModel X) (Q : TwoTermDeterminantModel Y)
    (q : rankZeroPullbackComplex g (rankZeroDeterminantComplex P) ⟶
      rankZeroDeterminantComplex Q) : (tensorPullback g).obj P.nonneg ⟶ Q.nonneg :=
  (tensorPullback g).map
    (HomologicalComplex.doubleXIso₁ P.differential (c := ComplexShape.up ℤ)
      (i₀ := 0) (i₁ := 1) (by decide) (by decide)).inv ≫ q.f 1 ≫
      (HomologicalComplex.doubleXIso₁ Q.differential (c := ComplexShape.up ℤ)
        (i₀ := 0) (i₁ := 1) (by decide) (by decide)).hom

/-- Full section, model, pullback and invertible-twist data. Every comparison on
models is pinned by a wedge or exact-cone formula; none is an arbitrary line isomorphism.
Source: Stacks, Tags 0FJI, 0FJM, 0FJX, 0FJY, and rank-zero twist cancellation
(blueprint: lem-sfb-rank-zero-perfect-determinant-section). -/
structure RankZeroPerfectDeterminantSectionData
    (κ : TwoTermDeterminantPullbackCoherence.{u, w}) where
  /-- The determinant on derived objects and derived isomorphisms. -/
  functor : ∀ X : Scheme.{u}, RankZeroPerfect01Core X ⥤ Core X.Modules
  /-- Its values are invertible modules. -/
  invertible : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K), (rankZeroDeterminantValue (functor X) K hK).IsInvertible
  /-- The canonical global section. -/
  delta : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K), Γ(rankZeroDeterminantValue (functor X) K hK, ⊤)
  /-- All derived isomorphisms preserve the section. -/
  section_naturality : ∀ (X : Scheme.{u}) (K L : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (hL : IsRankZeroPerfect01 X L) (e : K ≅ L),
    (rankZeroDeterminantIso (functor X) hK hL e).hom.app ⊤ (delta X K hK) = delta X L hL
  /-- Every equal-rank displayed model is in the domain, including empty schemes. -/
  model_mem : ∀ {X : Scheme.{u}} (P : TwoTermDeterminantModel X),
    P.negRank = P.nonnegRank →
      IsRankZeroPerfect01 X (rankZeroModelObject P)
  /-- The canonical exterior model identification. -/
  modelIso : ∀ {X : Scheme.{u}} (P : TwoTermDeterminantModel X)
    (hr : P.negRank = P.nonnegRank),
    rankZeroDeterminantValue (functor X)
      (rankZeroModelObject P) (model_mem P hr) ≅ P.line
  /-- In every model the section is det(d), with the rank transport explicit. -/
  model_section : ∀ {X : Scheme.{u}} (P : TwoTermDeterminantModel X)
    (hr : P.negRank = P.nonnegRank),
    ∀ (O : X.Opens) (ba : Module.Basis (Fin P.negRank) Γ(X, O) Γ(P.neg, O))
      (α : Γ(dual (exteriorSheaf P.neg P.negRank), O)),
      α.app (op (Over.mk (𝟙 O))) (exteriorSheafSection P.neg P.negRank O ba) =
        (1 : Γ(X, O)) →
      P.line.presheaf.map (homOfLE le_top).op
        ((modelIso P hr).hom.app ⊤
          (delta X _ (model_mem P hr))) =
        tmulSection (X := X) (M := dual (exteriorSheaf P.neg P.negRank))
          (N := exteriorSheaf P.nonneg P.nonnegRank) α
          (exteriorSheafSection P.nonneg P.nonnegRank O
          (fun i ↦ P.differential.app O (ba (Fin.cast hr.symm i))))
  /-- General model changes use the kernel-first exact-cone determinant, including
  the fixed sign, so comparisons are independent of presentation. -/
  model_comparison : ∀ {X : Scheme.{u}} (P Q : TwoTermDeterminantModel X)
    (hP : P.negRank = P.nonnegRank) (hQ : Q.negRank = Q.nonnegRank)
    (q : rankZeroDeterminantComplex P ⟶ rankZeroDeterminantComplex Q)
    (e : rankZeroModelObject P ≅
      rankZeroModelObject Q),
    e.hom = rankZeroModelMap P Q q →
    ∀ hr : P.negRank + Q.nonnegRank = Q.negRank + P.nonnegRank,
      IsFlatLCIDeterminantComparison P.neg Q.neg P.nonneg Q.nonneg
        P.negRank Q.negRank P.nonnegRank Q.nonnegRank hr P.differential Q.differential
        (rankZeroDeterminantTermMap₀ P Q q) (rankZeroDeterminantTermMap₁ P Q q)
        ((modelIso P hP).symm ≪≫
          rankZeroDeterminantIso (functor X) (model_mem P hP) (model_mem Q hQ) e ≪≫
            modelIso Q hQ)
  /-- Arbitrary pullback preserves the domain. -/
  pullback_mem : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) (K : schemeDerivedCategory X),
    IsRankZeroPerfect01 X K → IsRankZeroPerfect01 Y ((derivedPullback g).obj K)
  /-- The comparison to the actual ordinary pullback of the pair. -/
  pullbackIso : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K),
    (tensorPullback g).obj (rankZeroDeterminantValue (functor X) K hK) ≅
      rankZeroDeterminantValue (functor Y) ((derivedPullback g).obj K) (pullback_mem g K hK)
  /-- Section preservation, as the normalized section 1 tensor delta. -/
  pullback_section : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K),
    ∀ s : Γ((tensorPullback g).obj (rankZeroDeterminantValue (functor X) K hK), ⊤),
      s = @id Γ((tensorPullback g).obj (rankZeroDeterminantValue (functor X) K hK),
        g ⁻¹ᵁ (⊤ : X.Opens)) (tensorPullbackSection g _ ⊤ (delta X K hK)) →
      (pullbackIso g K hK).hom.app ⊤ s =
        delta Y ((derivedPullback g).obj K) (pullback_mem g K hK)
  /-- Naturality in every derived isomorphism. -/
  pullback_naturality : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X)
    {K L : schemeDerivedCategory X} (hK : IsRankZeroPerfect01 X K)
    (hL : IsRankZeroPerfect01 X L) (e : K ≅ L),
    (tensorPullback g).map (rankZeroDeterminantIso (functor X) hK hL e).hom ≫
        (pullbackIso g L hL).hom =
      (pullbackIso g K hK).hom ≫
        (rankZeroDeterminantIso (functor Y) (pullback_mem g K hK) (pullback_mem g L hL)
          ((derivedPullback g).mapIso e)).hom
  /-- Identity normalization. -/
  pullback_id : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K),
    (pullbackIso (𝟙 X) K hK).hom ≫
        (rankZeroDeterminantIso (functor X) (pullback_mem (𝟙 X) K hK) hK
          ((κ.derivedId X).app K)).hom =
      (tensorPullbackSectionId X).hom.app (rankZeroDeterminantValue (functor X) K hK)
  /-- Composition normalization, also for successive open restrictions. -/
  pullback_comp : ∀ {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y)
    (K : schemeDerivedCategory X) (hK : IsRankZeroPerfect01 X K),
    (tensorPullbackSectionComp h g).hom.app (rankZeroDeterminantValue (functor X) K hK) ≫
        (tensorPullback h).map (pullbackIso g K hK).hom ≫
        (pullbackIso h _ (pullback_mem g K hK)).hom ≫
        (rankZeroDeterminantIso (functor Z)
          (pullback_mem h _ (pullback_mem g K hK)) (pullback_mem (h ≫ g) K hK)
          ((κ.derivedComp h g).app K)).hom =
      (pullbackIso (h ≫ g) K hK).hom
  /-- On every termwise pulled-back model the line comparison is extension of
  scalars on pure wedges and dual wedges, using the retained K-flat counit. -/
  pullback_model : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X)
    (P : TwoTermDeterminantModel X) (Q : TwoTermDeterminantModel Y)
    (hP : P.negRank = P.nonnegRank) (hQ : Q.negRank = Q.nonnegRank)
    (q : rankZeroPullbackComplex g (rankZeroDeterminantComplex P) ⟶
      rankZeroDeterminantComplex Q)
    (e : (derivedPullback g).obj (rankZeroModelObject P) ≅
      rankZeroModelObject Q),
    e.hom = rankZeroPullbackCounit g (rankZeroDeterminantComplex P) ≫
      DerivedCategory.Q.{w}.map q →
    IsIso (rankZeroPullbackTermMap₀ g P Q q) →
    IsIso (rankZeroPullbackTermMap₁ g P Q q) →
    ∀ (ha : P.negRank = Q.negRank) (hn : P.nonnegRank = Q.nonnegRank),
      IsFlatLCIPullbackDeterminantComparison g P.neg P.nonneg Q.neg Q.nonneg
        P.negRank Q.negRank P.nonnegRank Q.nonnegRank ha hn
        (rankZeroPullbackTermMap₀ g P Q q) (rankZeroPullbackTermMap₁ g P Q q)
        ((tensorPullback g).mapIso (modelIso P hP).symm ≪≫
          pullbackIso g _ (model_mem P hP) ≪≫
          rankZeroDeterminantIso (functor Y) (pullback_mem g _ (model_mem P hP))
            (model_mem Q hQ) e ≪≫ modelIso Q hQ)
  /-- Invertible modules remain invertible after ordinary tensor pullback. -/
  twist_pullback_invertible : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X)
    (N : X.Modules), N.IsInvertible → ((tensorPullback g).obj N).IsInvertible
  /-- Products of twisting lines are invertible. -/
  twist_tensor_invertible : ∀ (X : Scheme.{u}) (N M : X.Modules),
    N.IsInvertible → M.IsInvertible → (N ⊗ M).IsInvertible
  /-- The canonical derived comparison between pullback and the exact twist. -/
  twistPullbackIso : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    (hN : N.IsInvertible),
    rankZeroTwist X N hN ⋙ derivedPullback g ≅
      derivedPullback g ⋙ rankZeroTwist Y ((tensorPullback g).obj N)
        (twist_pullback_invertible g N hN)
  /-- Its normalization on every complex fixes the comparison by localization:
  it is the termwise pure-tensor comparison composed with the original counits. -/
  twist_pullback_normalization : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X)
    (N : X.Modules) (hN : N.IsInvertible)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ),
    (twistPullbackIso g N hN).hom.app (DerivedCategory.Q.{w}.obj P) ≫
        (rankZeroTwist Y ((tensorPullback g).obj N)
          (twist_pullback_invertible g N hN)).map (rankZeroPullbackCounit g P) ≫
        (rankZeroTwistFactors Y ((tensorPullback g).obj N)
          (twist_pullback_invertible g N hN)).hom.app
          (rankZeroPullbackComplex g P) =
      (derivedPullback g).map ((rankZeroTwistFactors X N hN).hom.app P) ≫
        rankZeroPullbackCounit g
          (((rankZeroTwistModules X N).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.{w}.map (rankZeroTwistPullbackComplex g N P).hom
  /-- The domain is closed under invertible twists, without a choice of generator. -/
  twist_mem : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (_hK : IsRankZeroPerfect01 X K) (N : X.Modules) (hN : N.IsInvertible),
    IsRankZeroPerfect01 X ((rankZeroTwist X N hN).obj K)
  /-- The canonical cancellation map of pairs. -/
  twistIso : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (N : X.Modules) (hN : N.IsInvertible),
    rankZeroDeterminantValue (functor X) ((rankZeroTwist X N hN).obj K)
      (twist_mem X K hK N hN) ≅ rankZeroDeterminantValue (functor X) K hK
  /-- It carries the canonical sections to one another. -/
  twist_section : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (N : X.Modules) (hN : N.IsInvertible),
    (twistIso X K hK N hN).hom.app ⊤
      (delta X _ (twist_mem X K hK N hN)) = delta X K hK
  /-- On a trivialized line this is the actual map x tensor n to x. -/
  twist_trivialization : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (N : X.Modules) (hN : N.IsInvertible)
    (e : N ≅ 𝟙_ X.Modules),
    twistIso X K hK N hN = rankZeroDeterminantIso (functor X)
      (twist_mem X K hK N hN) hK ((rankZeroTwistTrivialization X N hN e).app K)
  /-- Naturality in derived isomorphisms of K. -/
  twist_naturality : ∀ (X : Scheme.{u}) (K L : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (hL : IsRankZeroPerfect01 X L) (e : K ≅ L)
    (N : X.Modules) (hN : N.IsInvertible),
    (rankZeroDeterminantIso (functor X) (twist_mem X K hK N hN)
        (twist_mem X L hL N hN) ((rankZeroTwist X N hN).mapIso e)).hom ≫
        (twistIso X L hL N hN).hom =
      (twistIso X K hK N hN).hom ≫ (rankZeroDeterminantIso (functor X) hK hL e).hom
  /-- Naturality in isomorphisms of the twisting line. -/
  twist_line_iso : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (N M : X.Modules)
    (hN : N.IsInvertible) (hM : M.IsInvertible) (e : N ≅ M),
    (rankZeroDeterminantIso (functor X) (twist_mem X K hK N hN)
      (twist_mem X K hK M hM) ((rankZeroTwistMap X N M hN hM e).app K)).hom ≫
        (twistIso X K hK M hM).hom = (twistIso X K hK N hN).hom
  /-- The ordinary tensor associator gives the product law. -/
  twist_product : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (N M : X.Modules) (hN : N.IsInvertible)
    (hM : M.IsInvertible) (hNM : (N ⊗ M).IsInvertible),
    (rankZeroDeterminantIso (functor X)
      (twist_mem X _ (twist_mem X K hK N hN) M hM)
      (twist_mem X K hK (N ⊗ M) hNM)
      ((rankZeroTwistProduct X N M hN hM hNM).app K)).hom ≫
        (twistIso X K hK (N ⊗ M) hNM).hom =
      (twistIso X _ (twist_mem X K hK N hN) M hM).hom ≫ (twistIso X K hK N hN).hom
  /-- Twist cancellation commutes with arbitrary base change along the canonical
  comparison just normalized on complexes. -/
  twist_basechange : ∀ {X Y : Scheme.{u}} (g : Y ⟶ X) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (N : X.Modules) (hN : N.IsInvertible),
    (tensorPullback g).map (twistIso X K hK N hN).hom ≫ (pullbackIso g K hK).hom =
      (pullbackIso g _ (twist_mem X K hK N hN)).hom ≫
        (rankZeroDeterminantIso (functor Y)
          (pullback_mem g _ (twist_mem X K hK N hN))
          (twist_mem Y _ (pullback_mem g K hK) ((tensorPullback g).obj N)
            (twist_pullback_invertible g N hN))
          ((twistPullbackIso g N hN).app K)).hom ≫
        (twistIso Y _ (pullback_mem g K hK) ((tensorPullback g).obj N)
          (twist_pullback_invertible g N hN)).hom
  /-- Every scalar unit acts identically on the entire pair, including zero sections. -/
  scalar_identity : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (a : (𝟙_ X.Modules) ≅ 𝟙_ X.Modules),
    rankZeroDeterminantIso (functor X) hK hK ((rankZeroScalar X a).app K) = Iso.refl _
  /-- Field-valued fibres, with no restriction on characteristic. -/
  fibre_nonzero : ∀ (X : Scheme.{u}) (K : schemeDerivedCategory X)
    (hK : IsRankZeroPerfect01 X K) (k : Type u) [Field k]
    (x : Spec (CommRingCat.of k) ⟶ X),
    delta _ ((derivedPullback x).obj K) (pullback_mem x K hK) ≠ 0 ↔
      IsZero ((derivedPullback x).obj K)

/-- The canonical determinant pair for every rank-zero perfect object of Tor
amplitude [0,1], functorially in derived isomorphisms, arbitrary scheme pullback,
and invertible twists. The data record fixes all comparisons on representatives.
Source: Stacks Project, perfect.tex Tags 0FJX (lemma-determinant-two-term-complexes),
0FJY (remark-functorial-det), more-algebra.tex Tags 0FJI and 0FJM; line-twist
cancellation from the rank-zero exterior formula.
(blueprint: lem-sfb-rank-zero-perfect-determinant-section).

Proof (the twelve steps of the DAG node):
1. Use sign-free reindexing R(P)^i=P^{i+1}, d_{R(P)}^i=d_P^{i+1}, and R(f)^i=f^{i+1}. Its inverse
   reindexes backwards; H^i(R(P))=H^{i+1}(P), so both preserve quasi-isomorphisms and descend
   through the derived localization. This is not the usual signed differential of P[1]. Reindexing
   commutes with tensoring a module and with termwise pullback of a flat resolution. Thus R(K) has
   Tor amplitude [-1,0], and the window theorem supplies an affine open cover with finite locally
   free two-term models, refined to constant ranks. Fix the normalized derived pullback coherence
   supplied by the coherence theorem, and the affine cartesian determinant system supplied by the
   affine theorem. In Steps 2--8 we construct the global line and its arrows from this affine
   system; no previously chosen global determinant functor or its unspecified model comparisons
   are used.
   Dependencies: def-weil-abstract-derived-category, lem-trf-two-term-perfect-tor-window, lem-trf-
   two-term-determinant-pullback-coherence, lem-trf-affine-two-term-determinant, def-trf-affine-
   determinant-interfaces.
2. For a model P=[E^0xrightarrow d E^1] of common rank r, use the explicit exterior line L(P)=det
   E^1otimes(det E^0)^vee. The top exterior map bigwedge^r d:det E^0todet E^1 defines its section
   delta_P. On a free chart with ordered wedges e=e_1wedgecdotswedge e_r and f=f_1wedgecdotswedge
   f_r, write bigwedge^r d(e)=c f and set delta_P=c fotimes e^vee. Changing e by a unit u
   multiplies c by u and e^vee by u^{-1}; changing f by a unit v multiplies c by v^{-1}. This is
   the intrinsic top exterior map. The identification operatorname{Hom}(det E^0,det E^1)=L(P) and
   its inverse are evaluation on a generator and tensoring that image with its dual. These
   exterior lines are the displayed-model lines of the affine construction, with arrows given by
   its kernel-normalized good diagrams. Degree-zero exterior powers give delta_{[0to0]}=1.
   Dependencies: def-sc-sheaf-exterior-power, def-sc-invertible-module, lem-trf-affine-two-term-
   determinant, lem-trf-surjective-two-term-determinant-calculus.
3. Check preservation under a degreewise surjective quasi-isomorphism a:Pto Q of affine finite
   projective two-term models (reindexed into degrees -1,0). The normalization theorem gives
   finite projective kernels N^i, an isomorphism d_N, and T_a^{-1}(x)=Gamma_a(xotimesdelta_N).
   Take a common finite standard free cover of N^{-1} and Q^{-1},Q^0; products of their covering
   elements still generate the unit ideal. The lifting property of the finite projective quotients
   gives sections of the two surjections; x=(x-sa(x))+sa(x) gives the direct-sum splittings. The
   kernel-first wedge maps then give bases (k,widetilde q) in P^{-1} and (d_N k,widetilde t) in
   P^0. In the wedge of their images under d_P, the kernel basis goes to d_N k. Every kernel
   component in an image d_Pwidetilde q wedges to zero against this full kernel wedge. The
   remaining quotient wedge is bigwedge d_Q(q). Therefore the kernel-first formula gives
   delta_P=Gamma_a(delta_Qotimesdelta_N), so T_a(delta_P)=delta_Q. Scalar comparison identifies
   these localized formulas, including their duals and exact-sequence maps, with the original
   maps. Equality on the finite standard cover detects equality in the module. No invertibility of
   d_P or d_Q was used.
   Dependencies: lem-trf-surjective-two-term-determinant-calculus, lem-trf-projective-determinant-
   exact-sequence, lem-trf-projective-exterior-scalar-comparisons, lem-weil-pbc-finite-projective-
   standard-free-cover, lem-weil-pbc-cover-module-exact, def-weil-pbc-projective-module.
4. The affine determinant theorem states that EVERY derived isomorphism acts by a kernel-
   normalized good-diagram map. For such an isomorphism Psimeq Q, write its map as T_cT_b^{-1} for
   its good diagram Pxleftarrow b Mxrightarrow c Q. Both legs are surjective quasi-isomorphisms;
   their kernel differentials are isomorphisms by the normalization theorem. Their kernels have
   equal ranks in the two degrees, so if P and Q have rank zero, so does M. Step 3 gives
   T_bdelta_M=delta_P and T_cdelta_M=delta_Q, hence (T_cT_b^{-1})delta_P=delta_Q. Independence of
   diagrams and the identity and composition laws are the affine determinant functor's existing
   assertions; we have only restricted its arrows to ones preserving the newly defined sections.
   Dependencies: lem-trf-affine-two-term-determinant, lem-trf-surjective-two-term-determinant-
   calculus.
5. Write s_P:Botimes_A L(P)to L(Botimes_A P) for the explicit exterior scalar comparison,
   including duals and ordinary tensor symmetry. Its generator formula sends 1otimesdelta_P to
   delta_{Botimes_A P}: the wedge of d e_j goes to the wedge of 1otimes d e_j, and the dual basis
   goes to the dual basis. For a surjective quasi-isomorphism a:Pto Q, its termwise sequences
   split by projectivity as in Step 3. Tensor preserves these splittings, so its new kernel is
   Botimes_A N and its differential is still invertible. Compatibility of the exterior scalar maps
   with the kernel-first wedge maps, duals and evaluation gives
   s_P(1otimesGamma_a)(xotimesdelta_N)=Gamma_{Botimes a}(s_Q(x)otimesdelta_{Botimes N}).
   Substitute T_a^{-1}(x)=Gamma_a(xotimesdelta_N) and cancel the isomorphisms. This proves
   s_Q(1otimes T_a)=T_{Botimes a}s_P. For u represented by Pxleftarrow b Mxrightarrow c Q, the
   same equation for both legs and their inverses yields s_Q(1otimes T_u)=T_{Lu},s_P. The tensor
   diagram is again good: its split kernel complexes remain contractible. The flat-complex and
   affine tensor comparison theorems identify it with the derived-pulled-back diagram, including
   for nonflat Ato B. The identity and associativity equations for these explicit s are in the
   exterior scalar theorem; derived identifications use the fixed normalized coherence. Thus this
   equivariance applies to every further affine restriction, with no appeal to a global
   determinant comparison.
   Dependencies: lem-trf-affine-two-term-determinant, lem-trf-surjective-two-term-determinant-
   calculus, lem-trf-projective-exterior-scalar-comparisons, def-weil-pbc-projective-module, lem-
   pc-flat-complex-derived-pullback, lem-pc-affine-derived-pullback-tensor-tilde, lem-trf-two-
   term-determinant-pullback-coherence.
6. Choose affine model charts (U_i,P_i,alpha_i:P_isimeq K|_{U_i}). On an affine Wsubset U_icap
   U_j, restrict both models via the exterior comparisons s. Define g_{ij} there to be
   T_{alpha_j^{-1}alpha_i}:L(P_i)|_Wto L(P_j)|_W. Step 5's equation makes these maps agree after
   further affine restriction. They therefore glue on the overlap: images of any local section
   agree on an affine cover, so the sheaf axiom gives its unique image; the inverse is obtained
   the same way. Step 4 gives g_{ii}=1, g_{jk}g_{ij}=g_{ik} on affine triple-overlap charts and
   g_{ij}delta_{P_i}=delta_{P_j}, hence globally. Apply the sheaf-gluing theorem on the small site
   of opens of V, with this set-indexed cover. Concretely D(K)(O)={(x_i)inprod_i L(P_i)(Ocap
   U_i):g_{ij}(x_i|)=x_j|}. Restriction, addition and scalar multiplication are componentwise.
   Linearity of g_{ij} preserves the matching condition. Projection to the ith coordinate on
   Osubset U_i is an isomorphism, with inverse xmapsto(g_{ij}(x|))_j. Thus this is a module sheaf
   locally equal to L(P_i), and is invertible. The matching tuple (delta_{P_i})_i is its global
   section delta_K. All intersections are covered by affines, never assumed affine.
   Dependencies: lem-trf-affine-two-term-determinant, def-trf-affine-determinant-interfaces, lem-
   pe-site-sheaf-gluing, def-weil-sheaf-of-modules-category, def-sc-invertible-module.
7. For a derived isomorphism u:Ksimeq K', choose affine model charts alpha_i:P_isimeq K and
   beta_j:Q_jsimeq K' and refine their overlaps by affines. Define the line map there as
   T_{beta_j^{-1}ualpha_i}. Step 5 makes it compatible with restrictions. On a change of source
   and target chart, affine composition gives T_{beta_{j'}^{-1}beta_j},T_{beta_j^{-1}ualpha_i}
   =T_{beta_{j'}^{-1}ualpha_{i'}},T_{alpha_{i'}^{-1}alpha_i}. It therefore defines a map of the
   matching-tuple sheaves in Step 6. Step 4 makes it section-preserving, and using u^{-1} gives
   its inverse. The identity and composite equations follow on every affine chart from those for
   T. Taking u=1_K between two choices of chart covers gives canonical inverse comparisons; for
   three choices their composites agree by the same equation. On any displayed model, comparison
   with the chosen charts is this very T, so the local formula holds for every model and is
   compatible with its derived isomorphisms. This constructs the functor on pairs and its model
   independence, with its local action specified rather than borrowed from an unrelated global
   functor.
   Dependencies: lem-trf-affine-two-term-determinant, def-trf-affine-determinant-interfaces, def-
   weil-sheaf-of-modules-category.
8. Let h:V'to V. Pullback preserves the two-term class by the window theorem. Cover h^{-1}U_i by
   affine opens W; on W, the flat-complex pullback theorem and the affine tensor comparison
   identify Lh^*P_i with the termwise scalar-extended model h^*P_i. Define the local line
   comparison h^*L(P_i)to L(h^*P_i) to be exactly s_{P_i} of Step 5. On an overlap its equation
   s_{P_j},h^*g_{ij}=g'_{ij},s_{P_i} identifies the two local maps, where g'_{ij} is the
   transition of the pulled-back models. These maps and their inverses glue to h^*D(K)simeq
   D(Lh^*K), using Step 7 to compare with any chosen target model charts. The generator equation
   in Step 5 proves section preservation. Naturality in derived isomorphisms is the same
   equivariance equation with u in place of a transition. On three affine model charts, the two
   comparisons for a composite pullback are s_{h^*P}h^*s_P and s_P for the composite scalar
   extension, identified by the exterior associativity equation and the fixed normalized derived
   coherence. For an identity map the exterior comparison is the identity. Equality on affine
   covers proves all these diagrams globally, without a flatness assumption on h.
   Dependencies: lem-trf-two-term-perfect-tor-window, lem-trf-affine-two-term-determinant, def-
   trf-affine-determinant-interfaces, lem-trf-projective-exterior-scalar-comparisons, lem-pc-flat-
   complex-derived-pullback, lem-pc-affine-derived-pullback-tensor-tilde, lem-trf-two-term-
   determinant-pullback-coherence, def-weil-sheaf-of-modules-category.
9. For a termwise isomorphism u:Pto Q, its kernel is zero. The kernel-first normalization formula
   therefore identifies its determinant action with ymapsto(det u^1)y(det u^0)^{-1}, with the
   degrees now 0,1. This follows directly from the zero-kernel exact-sequence wedge maps, with
   their empty kernel wedge equal to 1. Apply this to multiplication by a unit a on both terms of
   a rank-zero model of common rank r. Multilinearity gives bigwedge^r(a,1)=a^r1, so the action is
   a^r a^{-r}=1. The affine determinant theorem identifies this with the derived action, and Step
   7 defines the global action by these very affine arrows, so the sheaf separatedness axiom
   extends the equality from model charts to D(K). Thus every such scalar acts by the identity on
   the pair, even when delta_K=0.
   Dependencies: lem-trf-affine-two-term-determinant, lem-trf-surjective-two-term-determinant-
   calculus, lem-trf-projective-determinant-exact-sequence, def-sc-sheaf-exterior-power, def-weil-
   sheaf-of-modules-category.
10. Let N be invertible. On an open where it has a generator n, the map xotimes nmapsto x
   identifies Kotimes N with K in the derived category. Tensoring by N preserves quasi-
   isomorphisms: locally this functor is the identity, so its cohomology maps are the same maps;
   in particular this is the ordinary and derived twist. Apply the functor on pairs already
   obtained to this local isomorphism. If n'=a n, the new map is a^{-1} times the old map, and
   Step 9 says these induce the same map of determinant pairs. They consequently glue to a
   canonical isomorphism (D(Kotimes N),delta_{Kotimes N})simeq(D(K),delta_K); inverses glue as
   well. In a model, det(E^iotimes N)simeqdet E^iotimes N^{otimes r} sends the wedge of the
   e_jotimes n to (bigwedge e_j)otimes n^{otimes r}. Cancelling the two n^{otimes r} factors gives
   exactly this glued map and preserves bigwedge^r d. Changing the generator multiplies both
   factors by the same a^r.
   Dependencies: def-sc-invertible-module, def-sc-sheaf-exterior-power, def-weil-sheaf-of-modules-
   category.
11. The twist comparisons are natural also in derived isomorphisms of K: with n fixed,
   tau_n:Kotimes Nto K satisfies utau_n=tau_n(uotimes1), and the functor on pairs preserves this
   equation. For an isomorphism v:Nto N', choose generators n,n' and write v(n)=a n'. The
   analogous square differs from the identity square by multiplication by a, whose determinant
   action is the identity by Step 9. For two twists, the generator notimes m gives tau_{notimes
   m}=tau_ncirc(tau_mtext{ on the second twist}) after the ordinary tensor associator.
   Functoriality gives precisely the required product and unit comparisons. Finally h^*n generates
   h^*N, and the pullback of tau_n is tau_{h^*n}. Naturality of the pair comparison in Step 8
   gives the base-change square. All equations are local on the indicated trivializations and
   hence hold globally by sheaf separatedness.
   Dependencies: def-sc-invertible-module, def-weil-sheaf-of-modules-category.
12. On a field-valued fibre choose bases of its two vector spaces of common finite rank r. Base
   change in Step 8 identifies the section with det(d) times the displayed basis of the
   determinant line. Identify both vector spaces with the same k^r; the determinant-nonvanishing
   criterion for endomorphisms says that this coefficient is nonzero exactly when d is bijective.
   The two-term cohomology is ker d in degree 0 and operatorname{coker}d in degree 1, so this is
   exactly acyclicity. For r=0 the differential of the zero object is an isomorphism and the empty
   determinant is 1, consistent with this criterion. The argument also covers the empty scheme
   (unique sheaf data, no field-valued fibres), varying locally constant ranks, and characteristic
   two.
   Dependencies: lem-weil-endomorphism-invertible-iff-det-nonzero, def-weil-abstract-derived-
   category.
-/
theorem exists_rankZeroPerfectDeterminantSectionData :
    ∃ κ : TwoTermDeterminantPullbackCoherence.{u, w},
      Nonempty (RankZeroPerfectDeterminantSectionData κ) := by
  sorry

end AlgebraicGeometry
