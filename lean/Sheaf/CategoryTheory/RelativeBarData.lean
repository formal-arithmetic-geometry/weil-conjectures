/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.RelativeDerivedInvariants
public import Sheaf.CategoryTheory.CondensedDerivedInvariantBar



/-! # RelativeBarData

Source: main-20261015, six-functors direct-images proof, paragraph (3),
agent-formulated relative rank-one input (exact combined reference wanted).
(blueprint: def-sfb-relative-bar-data)

## Main definitions and statements

The primary declaration is `barEta`.
The accompanying definitions fix the canonical maps, coordinates and normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (inflate ProductInvariants)
namespace CategoryTheory.RelativeCyclic
variable (A : CondensedBar.Ring.{u}) (G J : Type u)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {A' : CondensedBar.Ring.{u}}
variable {J}

/-- The existing compatible bar model, with its recorded larger localization supplied
explicitly. This alias changes no data and avoids competing localization-universe instances.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
abbrev BarModel (A : CondensedBar.Ring.{u}) (H : Type u)
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] :=
  @CondensedBar.Model A H inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (largeActionDerived (A := A) (H := H)) (largeModulesDerived A)

variable {A}

/-- The actual functions projection of the recorded bar model, with its localization
instances supplied only for this projection. No data is changed.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def barFunctions [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (M : BarModel A H) : InternalFunctions A := by
  letI : HasDerivedCategory.{u + 2} (Equivariant A H) :=
    largeActionDerived (A := A) (H := H)
  letI : HasDerivedCategory.{u + 2} (Modules A) := largeModulesDerived A
  exact M.functions

/-- The actual invariants projection of the recorded bar model, with its localization
instances supplied only for this projection. No data is changed.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def barInvariants [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (M : BarModel A H) : Profinite.CondensedAction.Invariants A.toMon H := by
  letI : HasDerivedCategory.{u + 2} (Equivariant A H) :=
    largeActionDerived (A := A) (H := H)
  letI : HasDerivedCategory.{u + 2} (Modules A) := largeModulesDerived A
  exact M.invariants

/-- The actual bar projection of the recorded bar model, with its localization
instances supplied only for this projection. No data is changed.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def barDiagram [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (M : BarModel A H) : BarDiagram (G := H) (barFunctions M) := by
  letI : HasDerivedCategory.{u + 2} (Equivariant A H) :=
    largeActionDerived (A := A) (H := H)
  letI : HasDerivedCategory.{u + 2} (Modules A) := largeModulesDerived A
  exact M.bar

/-- The actual augmentation projection of the recorded bar model, with its localization
instances supplied only for this projection. No data is changed.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def barAugmentationData [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (M : BarModel A H) : Augmentation (barInvariants M) (barDiagram M) := by
  letI : HasDerivedCategory.{u + 2} (Equivariant A H) :=
    largeActionDerived (A := A) (H := H)
  letI : HasDerivedCategory.{u + 2} (Modules A) := largeModulesDerived A
  exact M.augmentation

/-- The actual totalAugmentation projection of the recorded bar model, with its localization
instances supplied only for this projection. No data is changed.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def barTotalAugmentation [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (M : BarModel A H) : TotalAugmentation (barInvariants M) (barDiagram M)
      (barAugmentationData M) := by
  letI : HasDerivedCategory.{u + 2} (Equivariant A H) :=
    largeActionDerived (A := A) (H := H)
  letI : HasDerivedCategory.{u + 2} (Modules A) := largeModulesDerived A
  exact M.totalAugmentation

variable (A)

/-- The complex [R -> 0 R], in cyclic degrees zero and one.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def trivialCyclic : CochainComplex (Modules A) ℕ where
  X n := if n ≤ 1 then Mod.regular A.X else 0
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

variable {A G}

/-- Evaluation at the chosen generator is a cochain map on the underived bar of trivial R.
Its equations are on every generalized section, and do not assume bar acyclicity.
Source: paragraph (3), steps 16--18
(blueprint: def-sfb-relative-bar-data).
Proof: the degree-zero inhomogeneous differential of trivial R is zero. The target has
zero differential and no terms above degree one. Evaluation is precomposition with
R -> R[H], 1 maps to [v(1)], hence is an internal R-linear natural map. -/
theorem evaluationExist [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (F : InternalFunctions A) (B : BarDiagram (G := H) F) (v : Z.{u} →ₜ* H) :
    ∃! e : (cochains B).obj (CondensedDerivedRestriction.regularTrivial A H) ⟶
        trivialCyclic A,
      (∀ (S : Profinite.{u})
        (x : sections A
          (((cochains B).obj (CondensedDerivedRestriction.regularTrivial A H)).X 0) S),
        (e.f 0).hom.hom.app (op S) x =
          (F.evaluate (power H 0) S (Mod.regular A.X)
            (((B.term (CondensedDerivedRestriction.regularTrivial A H) 0).hom).hom.hom.app
              (op S) x)).val S (𝟙 S) (ContinuousMap.const S (fun _ ↦ 1))) ∧
      (∀ (S : Profinite.{u})
        (x : sections A
          (((cochains B).obj (CondensedDerivedRestriction.regularTrivial A H)).X 1) S),
        (e.f 1).hom.hom.app (op S) x =
          (F.evaluate (power H 1) S (Mod.regular A.X)
            (((B.term (CondensedDerivedRestriction.regularTrivial A H) 1).hom).hom.hom.app
              (op S) x)).val S (𝟙 S) (ContinuousMap.const S (fun _ ↦ v generator))) ∧
      (∀ n : ℕ, 2 ≤ n → e.f n = 0) := by
  sorry

/-- The unique bar evaluation with identity in degree zero and evaluation at v(1) in degree one.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def evaluation [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (F : InternalFunctions A) (B : BarDiagram (G := H) F) (v : Z.{u} →ₜ* H) :=
  Classical.choose (evaluationExist F B v)

/-- The underived-to-derived bar map, specified in the resolution-zero row of the same total.
Source: paragraph (3), step 15
(blueprint: def-sfb-relative-bar-data).
Proof: map the coefficient augmentation into resolution degree zero and then the (n,0)
coprojection into the total. The bar and resolution differentials commute; the
augmentation is closed in resolution degree zero. Total functoriality gives the chain map,
and its degreewise formula determines it uniquely. -/
theorem barAugmentationExist [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (F : InternalFunctions A) (B : BarDiagram (G := H) F) (N : Equivariant A H)
    (I : InjectiveResolution N) :
    ∃! j : (cochains B).obj N ⟶ (totalCochains B).obj I.cocomplex,
      ∀ n : ℕ, j.f n = ((cochains B).map (I.ι.f 0)).f n ≫
        (doubleComplex B I.cocomplex).ιTotal (.up ℕ) n 0 n (by simp) := by
  sorry

/-- The canonical underived-to-derived bar augmentation, not an assumed quasi-isomorphism.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def barAugmentation [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (F : InternalFunctions A) (B : BarDiagram (G := H) F) (N : Equivariant A H)
    (I : InjectiveResolution N) := Classical.choose (barAugmentationExist F B N I)

set_option backward.isDefEq.respectTransparency false in
/-- The actual scalar invariant computation on a nonnegative equivariant injective resolution,
using the small-Hom localization of the recorded scalar restriction calculus.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def scalarResolutionIso (N : Equivariant A H) (I : InjectiveResolution N) :
    (CondensedDerivedRestriction.derived A H).obj ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      DerivedCategory.Q.{u + 1}.obj (extend
        (((CondensedDerivedRestriction.invariants A H).functor.mapHomologicalComplex
          (.up ℕ)).obj I.cocomplex)) := by
  letI : QuasiIso I.ι' := inferInstance
  letI : I.cochainComplex.IsKInjective := by
    dsimp only [InjectiveResolution.cochainComplex]
    infer_instance
  exact
    (CondensedDerivedRestriction.derived A H).mapIso (asIso (DerivedCategory.Q.{u + 1}.map I.ι')) ≪≫
      (CondensedDerivedRestriction.invariants A H).functor.rightDerivedFunctorObjQIso
        I.cochainComplex ≪≫
      DerivedCategory.Q.{u + 1}.mapIso (HomologicalComplex.mapExtendIso I.cocomplex
        ComplexShape.embeddingUpNat (CondensedDerivedRestriction.invariants A H).functor)

set_option backward.isDefEq.respectTransparency false in
/-- The bar comparison uses the existing bar model and its invariant-inclusion normalization,
with the canonical comparison from scalar invariants to the model's invariants.
Source: paragraph (3), step 15
(blueprint: def-sfb-relative-bar-data). -/
structure BarNormalization [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (M : BarModel A H) where
  invariants : (CondensedDerivedRestriction.invariants A H).functor ≅ (barInvariants M).functor
  inclusion : ∀ N, invariants.hom.app N ≫ (barInvariants M).inclusion.app N =
    (CondensedDerivedRestriction.invariants A H).inclusion.app N

set_option backward.isDefEq.respectTransparency false in
/-- The recorded total augmentation is a quasi-isomorphism in each compatible resolution.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
instance barAugmentationQuasiIso [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (M : BarModel A H) {N : Equivariant A H} (I : InjectiveResolution N) :
    QuasiIso ((barTotalAugmentation M).map.app I.cocomplex) := by
  let : HasDerivedCategory.{u + 2} (Equivariant A H) :=
    largeActionDerived (A := A) (H := H)
  let : HasDerivedCategory.{u + 2} (Modules A) := largeModulesDerived A
  exact M.computation.augmentation_quasiIso I

set_option backward.isDefEq.respectTransparency false in
/-- The invariant-normalized derived bar isomorphism in any specified compatible resolution.
Source: paragraph (3) (blueprint: def-sfb-relative-bar-data). -/
def barEta [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (M : BarModel A H) (b : BarNormalization M) (N : Equivariant A H)
    (I : InjectiveResolution N) :
    (CondensedDerivedRestriction.derived A H).obj ((DerivedCategory.singleFunctor _ 0).obj N) ≅
      DerivedCategory.Q.obj (extend ((totalCochains (barDiagram M)).obj I.cocomplex)) :=
  scalarResolutionIso N I ≪≫ DerivedCategory.Q.mapIso
    ((ComplexShape.embeddingUpNat.extendFunctor (Modules A)).mapIso
      ((NatIso.mapHomologicalComplex b.invariants (.up ℕ)).app I.cocomplex)) ≪≫
    asIso (DerivedCategory.Q.map (HomologicalComplex.extendMap
      ((barTotalAugmentation M).map.app I.cocomplex) ComplexShape.embeddingUpNat))

set_option backward.isDefEq.respectTransparency false in
/-- The two normalized invariant-submodule functors give the bar normalization for every
compatible bar model, so `barEvaluation` requires no additional invariant-identification data.
Source: paragraph (3), step 15
(blueprint: def-sfb-relative-bar-data).
Proof: both inclusions have exactly the fully fixed sections as image after every base
change. Restrict each inclusion's codomain to the other's image. Injectivity gives inverse
maps, naturality, and the unique normalized invariant comparison. -/
theorem barNormalizationExist [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (M : BarModel A H) : Nonempty (BarNormalization M) := by
  sorry


end CategoryTheory.RelativeCyclic
