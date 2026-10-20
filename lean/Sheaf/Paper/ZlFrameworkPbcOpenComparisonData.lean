/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.ZlFrameworkOpenExchange
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.CompleteProetaleStrictTowerRealization
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.RationalCompactSupportCoefficientCoherence

/-! # Framework and PBC exchange under open restriction

Source: blueprint main-20261015, thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u w u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
  u₅ u₆ u₇ u₈ v₅ v₆ v₇ v₈
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

namespace ZlFrameworkPbc

open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The PBC coefficient presentation with its specified scheme-edge isomorphisms.
Source: thm-cbc-qbar.proof.md, integral comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def pbcCoefficients : Coefficients.{u} where
  ring W := (pbcIntegralDatum l E).completedRing W
  pull g := (pbcIntegralDatum l E).integralRingIso g

/-- The coefficient square asserts equality of the specified maps, not a choice of
coefficient identifications. Source: thm-cbc-qbar.proof.md, integral comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def CoefficientSquares : Prop :=
  ∀ {U W : Scheme.{u}} (g : U ⟶ W),
    ((pbcCoefficients l E).pull g).hom ≫ (purCoefficientIso l E U).hom =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (purCoefficientIso l E W).hom ≫ ((completed l E).pull g).hom

/-- The actual normalized coefficient map, with the equality proof supplied separately.
Source: thm-cbc-qbar.proof.md, integral comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def coefficientChange (h : CoefficientSquares l E) :
    Change (pbcCoefficients l E) (completed l E) where
  map W := (purCoefficientIso l E W).hom
  square g := h g

/-- Compact support in the PBC presentation, before restriction to complete objects.
Source: def-weil-pbc-projection-compactification, thm-cbc-qbar.proof.md
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
abbrev pbcImage {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  cbcDerivedOpenShriek (pbcIntegralDatum l E) c.i c.isOpenImmersion ⋙
    (pbcIntegralDatum l E).push c.g

/-- Canonical comparison of the two open-extension presentations, fixed by their
adjunctions to the very same ordinary pullback.
Source: thm-cbc-qbar.proof.md, integral comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def pbcImageIso {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    image (pbcCoefficients l E) c ≅ pbcImage l E c :=
  Functor.isoWhiskerRight
    ((openDerivedAdjunction (pbcCoefficients l E) c.i).leftAdjointUniq
      (cbcDerivedOpenAdjunction (pbcIntegralDatum l E) c.i))
    ((pbcIntegralDatum l E).push c.g)

variable (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Compact-support comparison with its entire strict-tower normalization retained.
The first factor is the recorded Roos-projection-normalized realization. The next
factor is coefficient restriction, whose proper comparison uses the canonical
right-derived direct-image comparison and whose open comparison is its unit mate.
Source: thm-cbc-qbar.proof.md, integral comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def supportComparison (h : CoefficientSquares l E) (c : Compactification f) :=
  Functor.isoWhiskerRight (sfQcqsCompactSupportRealization l E K₀ hl c).symm
      (pbcDerivedRestrict (purCoefficientIso l E Y).hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι
      (restriction (coefficientChange l E h) c).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft
      ((sfIntegralConstructible l E X).ι ⋙ pbcDerivedRestrict
        (purCoefficientIso l E X).hom) (pbcImageIso l E c)

end ZlFrameworkPbc

namespace ZlExchange

/-- The lift of the specified comparison to fixed pairs, with its underlying map fixed.
Source: thm-cbc-qbar.proof.md, Weil compatibility
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def HasFixedPairSupportLift
    {CX : Type u₁} {CY : Type u₂} {PX : Type u₃} {PY : Type u₄}
    [Category.{v₁} CX] [Category.{v₂} CY] [Category.{v₃} PX] [Category.{v₄} PY]
    {JX : CX ⥤ PX} {JY : CY ⥤ PY} {F : CX ⥤ CY} {G : PX ⥤ PY}
    {φX : CX ⥤ CX} {φY : CY ⥤ CY} {ψX : PX ⥤ PX} {ψY : PY ⥤ PY}
    (b : F ⋙ JY ≅ JX ⋙ G)
    (aX : φX ⋙ JX ≅ JX ⋙ ψX) (aY : φY ⋙ JY ≅ JY ⋙ ψY)
    (e : F ⋙ φY ≅ φX ⋙ F) (e' : G ⋙ ψY ≅ ψX ⋙ G) : Prop :=
  ∃ t : Endofunctor.IsoAlgebra.mapOfNatIso e ⋙
      Endofunctor.IsoAlgebra.mapOfNatIso aY.symm ≅
    Endofunctor.IsoAlgebra.mapOfNatIso aX.symm ⋙
      Endofunctor.IsoAlgebra.mapOfNatIso e',
    ∀ K, (t.hom.app K).hom.f = b.hom.app K.carrier

/-- Fixed-pair compatibility for specified exchange arrows, including their invertibility.
The isomorphisms are required to have exactly those arrows as hom, and the lift has b
as its underlying component. Source: thm-cbc-qbar.proof.md, Weil compatibility
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def HasExchangeFixedPairSupportLift
    {CX : Type u₁} {CY : Type u₂} {PX : Type u₃} {PY : Type u₄}
    [Category.{v₁} CX] [Category.{v₂} CY] [Category.{v₃} PX] [Category.{v₄} PY]
    {JX : CX ⥤ PX} {JY : CY ⥤ PY} {F : CX ⥤ CY} {G : PX ⥤ PY}
    {φX : CX ⥤ CX} {φY : CY ⥤ CY} {ψX : PX ⥤ PX} {ψY : PY ⥤ PY}
    (b : F ⋙ JY ≅ JX ⋙ G)
    (aX : φX ⋙ JX ≅ JX ⋙ ψX) (aY : φY ⋙ JY ≅ JY ⋙ ψY)
    {AS : Type (max u₁ v₂)} {AP : Type (max u₃ v₄)} (e : AS) (e' : AP) : Prop :=
  ∃ i : F ⋙ φY ≅ φX ⋙ F, ∃ i' : G ⋙ ψY ≅ ψX ⋙ G,
    HEq i.hom e ∧ HEq i'.hom e' ∧ HasFixedPairSupportLift b aX aY i i'

variable {CX : Type u₁} {CY : Type u₂} {CU : Type u₃} {CV : Type u₄}
  {PX : Type u₅} {PY : Type u₆} {PU : Type u₇} {PV : Type u₈}
  [Category.{v₁} CX] [Category.{v₂} CY] [Category.{v₃} CU] [Category.{v₄} CV]
  [Category.{v₅} PX] [Category.{v₆} PY] [Category.{v₇} PU] [Category.{v₈} PV]

/-- The four comparison isomorphisms, with their actual typed endpoints.
Source: thm-cbc-qbar.proof.md, common-stage comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
structure Comparisons (JX : CX ⥤ PX) (JY : CY ⥤ PY) (JU : CU ⥤ PU) (JV : CV ⥤ PV)
    (F : CX ⥤ CY) (F' : CU ⥤ CV) (P : CY ⥤ CV) (P' : CX ⥤ CU)
    (G : PX ⥤ PY) (G' : PU ⥤ PV) (Q : PY ⥤ PV) (Q' : PX ⥤ PU) where
  b : F ⋙ JY ≅ JX ⋙ G
  b' : F' ⋙ JV ≅ JU ⋙ G'
  a : P ⋙ JV ≅ JY ⋙ Q
  a' : P' ⋙ JU ≅ JX ⋙ Q'

variable {JX : CX ⥤ PX} {JY : CY ⥤ PY} {JU : CU ⥤ PU} {JV : CV ⥤ PV}
  {F : CX ⥤ CY} {F' : CU ⥤ CV} {P : CY ⥤ CV} {P' : CX ⥤ CU}
  {G : PX ⥤ PY} {G' : PU ⥤ PV} {Q : PY ⥤ PV} {Q' : PX ⥤ PU}

/-- The source identification S, in the order a followed by pullback of b.
Source: thm-cbc-qbar.proof.md, common-stage comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def Comparisons.source (C : Comparisons JX JY JU JV F F' P P' G G' Q Q') (K : CX) :
    JV.obj (P.obj (F.obj K)) ≅ Q.obj (G.obj (JX.obj K)) :=
  C.a.app (F.obj K) ≪≫ Q.mapIso (C.b.app K)

/-- The target identification T, in the order b followed by compact support of a.
Source: thm-cbc-qbar.proof.md, common-stage comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def Comparisons.target (C : Comparisons JX JY JU JV F F' P P' G G' Q Q') (K : CX) :
    JV.obj (F'.obj (P'.obj K)) ≅ G'.obj (Q'.obj (JX.obj K)) :=
  C.b'.app (P'.obj K) ≪≫ G'.mapIso (C.a'.app K)

/-- Equality of the actual natural transformations, expressed on every component.
Source: thm-cbc-qbar.proof.md, common-stage comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def Comparisons.Commutes (C : Comparisons JX JY JU JV F F' P P' G G' Q Q')
    (e : F ⋙ P ⟶ P' ⋙ F') (e' : G ⋙ Q ⟶ Q' ⋙ G') : Prop :=
  ∀ K : CX, (C.source K).hom ≫ e'.app (JX.obj K) =
    JV.map (e.app K) ≫ (C.target K).hom

end ZlExchange

namespace ZlFrameworkPbc

open PurCompactSupport

section CoherentComparison

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u₁} {C' : I → Type u₂}
  [∀ i, Category.{v₁} (C i)] [∀ i, Category.{v₂} (C' i)]
  {T : StageSystem C} {T' : StageSystem C'}

/-- A compatible natural isomorphism on the unchanged raw coefficient stages.
The compatibility field is the actual beta equation, including repeated stages.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
structure FamilyIso (F G : StageSystem.Morphism T T') where
  finite : ∀ i, F.Φ i ≅ G.Φ i
  hom : StageSystem.Morphism.Hom F G
  components : ∀ i, hom.τ i = (finite i).hom

/-- Descend the actual compatible finite maps, retaining their literal common-stage
components. Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def FamilyIso.pair {F G : StageSystem.Morphism T T'} (a : FamilyIso F G) :
    F.functor ≅ G.functor :=
  @asIso _ _ _ _ (StageSystem.Morphism.descNatTrans a.hom)
    (StageSystem.Morphism.isIso_descNatTrans a.hom
      (fun i ↦ Eq.mp (congrArg IsIso (a.components i).symm) inferInstance))

end CoherentComparison

section PullNormalization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (h : U ⟶ T) (E : Padic.FiniteCoefficientFields l Ω)

/-- The specified strict-tower/completion-reflector comparison, restricted to the
recorded complete objects. Uniqueness retains the quotient augmentation.
Source: Stacks 099N(2),(5), thm-cbc-qbar.proof.md
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def strictReflectorIso :=
  (pbcActualCompletedPullback_tower (pbcStageDatum.{u} l Ω E) h).exists.choose

/-- Whole-tower normalization of the pullback comparison for an arbitrary scheme edge.
The chain is the existing quotient-coordinate/zero-shifted-coordinate comparison.
Source: thm-cbc-qbar.proof.md, integral comparison
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
structure PullNormalization where
  chain : FdPullbackChain l Ω E h
  ambient : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
      integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
        pbcActualCompletedPull h (pbcStageDatum.{u} l Ω E) ≅
    constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) h ⋙
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) U).ι ⋙
        integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)
  normalization : ∀ (P : (integralOperationsGoodComplex l
      (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq ((pbcActualCompletedPullUnit h (pbcStageDatum.{u} l Ω E)).app
        ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj
          (DerivedCategory.Q.obj P.obj)) ≫
      ambient.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).map
        ((integralDerivedPullbackComparison l (pbcFiniteField.{u} l Ω E) h).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) U).hom.app
        ((integralOperationsPullbackComplexFunctor l
          (pbcFiniteField.{u} l Ω E) h).obj P.obj))
      ((pbcActualDerivedPull h (pbcStageDatum.{u} l Ω E)).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcActualPullComplexCounit h (pbcStageDatum.{u} l Ω E)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map (chain.map.app P.obj))

/-- The specified comparison with strict completed pullback, at a complete input.
It uses the inverse of the whole-tower unit-normalized reflector comparison.
Source: Stacks 099N(5), thm-cbc-qbar.proof.md
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def rawPullComparison (N : PullNormalization l Ω h E)
    (K : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hc : PbcIsIntrinsicallyComplete T (pbcStageDatum.{u} l Ω E)
      ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj K.obj)) :=
  (N.ambient.app K).symm ≪≫
    ((strictReflectorIso l Ω h E).app
      ⟨(integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj K.obj, hc⟩).symm ≪≫
    (cbcDatumActualStrictTransport (pbcStageDatum.{u} l Ω E) h).app _

/-- Framework pullback on the unchanged raw field stages and pair quotient. Its beta
maps are the already defined balanced scalar/pullback comparisons, including identities.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
structure SfPullFamily where
  system : StageSystem.Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω U)
  finite : ∀ L, HEq (system.Φ L)
    (rationalDerivedPullback l (pbcFiniteField.{u} l Ω L) h)
  beta : ∀ {L M : Padic.FiniteCoefficientFields l Ω} (e : L ≤ M)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T L),
    HEq ((system.β e).hom.app K)
      (commonStagePullbackComparison l Ω h ⟨L, K⟩ M e).hom
  pair : system.functor = commonStageDerivedPullback l Ω h

end PullNormalization

section GlobalPullCoherence

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- One normalized pullback comparison for every scheme edge, with the actual unit and
composition equations. Scheme isomorphisms are arbitrary scheme isomorphisms, so the
comparison includes semilinear automorphisms as well as linear ones.
Source: thm-cbc-qbar.proof.md, integral comparison; Stacks 099N(5)
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
structure PullSystem (S : FdCoefficientComparisonSystem.{u} l Ω) where
  complete : ∀ (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).FullSubcategory),
    PbcIsIntrinsicallyComplete T (pbcStageDatum.{u} l Ω E)
      ((integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj K.obj)
  comparison : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ⟶ T) (E : Padic.FiniteCoefficientFields l Ω), PullNormalization l Ω h E
  identity : ∀ (T : Scheme.{u}) [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (E : Padic.FiniteCoefficientFields l Ω)
    (K : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).FullSubcategory),
    ((comparison (𝟙 T) E).ambient.inv.app K) ≫
        (pbcActualCompletedPullIdIso (pbcStageDatum.{u} l Ω E) T).hom.app
          ⟨(integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj K.obj,
            complete T E K⟩ =
      (integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).map
        (integralComparisonUnit l (pbcFiniteField.{u} l Ω E) S.realization T K).hom
  composition : ∀ {U V T : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
    [Fact (∀ t : V, IsUnit (l : V.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ⟶ V) (k : V ⟶ T) (E : Padic.FiniteCoefficientFields l Ω)
    (K : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).FullSubcategory),
    (comparison (h ≫ k) E).ambient.inv.app K ≫
        (pbcActualCompletedPullCompIso h k (pbcStageDatum.{u} l Ω E)).inv.app
          ⟨(integralDetailedTransport T l (pbcFiniteField.{u} l Ω E)).obj K.obj,
            complete T E K⟩ =
      (integralDetailedTransport U l (pbcFiniteField.{u} l Ω E)).map
        (integralComparisonComposition l (pbcFiniteField.{u} l Ω E)
          S.realization h k K).hom ≫
      (comparison h E).ambient.inv.app
        ((constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) k).obj K) ≫
      (pbcActualCompletedPull h (pbcStageDatum.{u} l Ω E)).map
        ((comparison k E).ambient.inv.app K)
  isomorphism : ∀ {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
    [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (h : U ≅ T) (E : Padic.FiniteCoefficientFields l Ω),
    (comparison h.hom E).ambient = ((S.pullback h).finite E).ambient

end GlobalPullCoherence

section SquareComparisons

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (R : IntegralComparisonSystem.{u} l)
  {X' X Y' Y : Scheme.{u}}
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : ChosenCartesianSquare g' f' f g)

/-- The framework pullback square is the composite of the specified whole-tower
compositors, with precisely the given commutativity transport in the middle.
Source: thm-cbc-qbar.proof.md, naturality; Stacks 099N(5)
(blueprint: def-zl-framework-pbc-open-comparison-data).
Proof: compose the inverse of the comparison for g' then f, the equality sq.w,
and the comparison for f' then g. Each factor is natural by the whole-system
realization construction. Full inclusion lifts this natural isomorphism uniquely
from ambient derived categories. Components determine the natural transformation,
so the stipulated formula also proves uniqueness. -/
theorem sfPullSquare_existsUnique :
    ∃! a : constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E g' ≅
      constructibleIntegralPullback l E g ⋙ constructibleIntegralPullback l E f',
      ∀ K, (a.hom.app K).hom =
        (integralComparisonComposition l E R g' f K).inv ≫
          eqToHom (congrArg (fun h : X' ⟶ Y ↦ (integralDerivedPullback l E h).obj K.obj)
            sq.w) ≫
          (integralComparisonComposition l E R f' g K).hom := by
  sorry

/-- The actual framework pullback-square comparison, fixed on the whole quotient tower.
Source: thm-cbc-qbar.proof.md, naturality; Stacks 099N(5)
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def sfPullSquare := (sfPullSquare_existsUnique l E R sq).exists.choose

end SquareComparisons

section PbcSquareComparisons

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X' X Y' Y : Scheme.{u}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : ChosenCartesianSquare g' f' f g)

/-- Ordinary pullback around the same square, transported by the specified ordinary
coefficient identifications. Every factor is fixed before passing to completion.
Source: thm-cbc-qbar.proof.md, naturality; Stacks 0D6D
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def ordinaryPbcSquare : d.pull f ⋙ d.pull g' ≅ d.pull g ⋙ d.pull f' :=
  Functor.isoWhiskerRight (cbcDatumOrdinaryTransport d f).symm (d.pull g') ≪≫
    Functor.isoWhiskerLeft (pbcActualDerivedPull f d)
      (cbcDatumOrdinaryTransport d g').symm ≪≫
    (pbcActualCompletedPullSquareIso d sq).symm ≪≫
    Functor.isoWhiskerRight (cbcDatumOrdinaryTransport d g) (pbcActualDerivedPull f' d) ≪≫
    Functor.isoWhiskerLeft (d.pull g) (cbcDatumOrdinaryTransport d f')

end PbcSquareComparisons

section IntegralPullFamilies

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {U T : Scheme.{u}} [IsNoetherian U] [IsNoetherian T]
  [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  {h : U ⟶ T}

/-- The integral stage of the specified completed-pullback coefficient family.
Source: thm-cbc-qbar.proof.md, naturality
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
abbrev familyIntegralPull (P : CbcCompletedPullCoefficientFamily l Ω h)
    (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    ((pbcStageDatum.{u} l Ω E).completedPull h) (P.preserves E)

end IntegralPullFamilies

section CompletedSquares

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X' X Y' Y : Scheme.{u}}
  [IsNoetherian X'] [IsNoetherian X] [IsNoetherian Y'] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X' ≤ n)]
  [Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ n)]
  [Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  (sq : ChosenCartesianSquare g' f' f g)
  (Pf : CbcCompletedPullCoefficientFamily l Ω f)
  (Pg' : CbcCompletedPullCoefficientFamily l Ω g')
  (Pg : CbcCompletedPullCoefficientFamily l Ω g)
  (Pf' : CbcCompletedPullCoefficientFamily l Ω f')
  (E : Padic.FiniteCoefficientFields l Ω)

/-- The completed square is uniquely determined by the ordinary square and quotient
units. In particular it is the actual canonical compositor square, not any isomorphism
of its endpoints. Source: thm-cbc-qbar.proof.md, naturality; Stacks 099N(5)
(blueprint: def-zl-framework-pbc-open-comparison-data).
Proof: each composite is completion of the ordinary composite on complete inputs.
Use the ordinary square, then the target's two quotient units. The universal
reflection property extends it uniquely across the source units. The inverse
ordinary square gives its inverse, since the composites preserve the units.
This gives a natural isomorphism, restricts to the full constructible categories,
and proves the displayed normalization and its uniqueness. -/
theorem pbcPullSquare_existsUnique :
    ∃! a : familyIntegralPull l Ω Pf E ⋙ familyIntegralPull l Ω Pg' E ≅
      familyIntegralPull l Ω Pg E ⋙ familyIntegralPull l Ω Pf' E,
      ∀ K : pbcIntegralStage l Ω Y E,
        ((pbcStageDatum.{u} l Ω E).pull g').map
            ((pbcStageDatum.{u} l Ω E).ordinaryToCompleted f K.obj) ≫
          (pbcStageDatum.{u} l Ω E).ordinaryToCompleted g'
            (((pbcStageDatum.{u} l Ω E).completedPull f).obj K.obj) ≫
          (a.hom.app K).hom =
        (ordinaryPbcSquare (pbcStageDatum.{u} l Ω E) sq).hom.app K.obj ≫
          ((pbcStageDatum.{u} l Ω E).pull f').map
            ((pbcStageDatum.{u} l Ω E).ordinaryToCompleted g K.obj) ≫
          (pbcStageDatum.{u} l Ω E).ordinaryToCompleted f'
            (((pbcStageDatum.{u} l Ω E).completedPull g).obj K.obj) := by
  sorry

/-- The unit-normalized completed pullback square on the integral full categories.
Source: thm-cbc-qbar.proof.md, naturality; Stacks 099N(5)
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def pbcPullSquare := (pbcPullSquare_existsUnique l Ω sq Pf Pg' Pg Pf' E).exists.choose

end CompletedSquares

section SquareData

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (G : OpenDiagram D l)
  (S : FdCoefficientComparisonSystem.{u} l Ω)

/-- The actual integral PBC support functor on its full constructible category.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
abbrev integralSupport (H : CbcCompactSupportCoefficientFamily l Ω G.c)
    (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    (pbcImage l (pbcFiniteField.{u} l Ω E) G.c) (H.preserves E)

/-- The actual integral PBC support functor for the pulled-back compactification.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
abbrev integralSupport' (H : CbcCompactSupportCoefficientFamily l Ω G.c')
    (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    (pbcImage l (pbcFiniteField.{u} l Ω E) G.c') (H.preserves E)

/-- Integral completed pullback along the lower open edge.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
abbrev integralPull (P : CbcCompletedPullCoefficientFamily l Ω G.v)
    (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    ((pbcStageDatum.{u} l Ω E).completedPull G.v) (P.preserves E)

/-- Integral completed pullback along the upper open edge.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
abbrev integralPull' (P : CbcCompletedPullCoefficientFamily l Ω G.u)
    (E : Padic.FiniteCoefficientFields l Ω) :=
  pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
    ((pbcStageDatum.{u} l Ω E).completedPull G.u) (P.preserves E)

/-- The four comparisons on the actual integral categories.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
abbrev IntegralComparisons
    (H : CbcCompactSupportCoefficientFamily l Ω G.c)
    (H' : CbcCompactSupportCoefficientFamily l Ω G.c')
    (P : CbcCompletedPullCoefficientFamily l Ω G.v)
    (P' : CbcCompletedPullCoefficientFamily l Ω G.u)
    (E : Padic.FiniteCoefficientFields l Ω) :=
  ZlExchange.Comparisons
    (((S.coefficients G.X).stage E).integral.functor)
    (((S.coefficients G.Y).stage E).integral.functor)
    (((S.coefficients G.U).stage E).integral.functor)
    (((S.coefficients G.V).stage E).integral.functor)
    (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) G.c
      (pbcFiniteField.{u} l Ω E))
    (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) G.c'
      (pbcFiniteField.{u} l Ω E))
    (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) G.v)
    (constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) G.u)
    (integralSupport D l Ω G H E) (integralSupport' D l Ω G H' E)
    (integralPull D l Ω G P E) (integralPull' D l Ω G P' E)

/-- Integral data with the stipulated normalizations. Both exchanges are actual natural
transformations; the framework one is fixed on the entire strict diagram, and the PBC
one is the named ordered completed exchange. No invertibility is required of either.
Source: thm-cbc-qbar.proof.md, integral comparison and ordered factors
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
structure IntegralSquare
    (H : CbcCompactSupportCoefficientFamily l Ω G.c)
    (H' : CbcCompactSupportCoefficientFamily l Ω G.c')
    (P : CbcCompletedPullCoefficientFamily l Ω G.v)
    (P' : CbcCompletedPullCoefficientFamily l Ω G.u)
    (E : Padic.FiniteCoefficientFields l Ω) where
  coefficients : CoefficientSquares l (pbcFiniteField.{u} l Ω E)
  comparisons : IntegralComparisons D l hl Ω G S H H' P P' E
  support : ∀ K, HEq (comparisons.b.hom.app K).hom
    ((supportComparison l (pbcFiniteField.{u} l Ω E) D.k
      (coefficientPrimeUnit l D hl) coefficients G.c).hom.app K)
  support' : ∀ K, HEq (comparisons.b'.hom.app K).hom
    ((supportComparison l (pbcFiniteField.{u} l Ω E) D.k
      (coefficientPrimeUnit l D hl) coefficients G.c').hom.app K)
  pullV : PullNormalization l Ω G.v E
  pullU : PullNormalization l Ω G.u E
  completeY : ∀ K : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) G.Y).FullSubcategory,
    PbcIsIntrinsicallyComplete G.Y (pbcStageDatum.{u} l Ω E)
      ((integralDetailedTransport G.Y l (pbcFiniteField.{u} l Ω E)).obj K.obj)
  completeX : ∀ K : (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) G.X).FullSubcategory,
    PbcIsIntrinsicallyComplete G.X (pbcStageDatum.{u} l Ω E)
      ((integralDetailedTransport G.X l (pbcFiniteField.{u} l Ω E)).obj K.obj)
  pullV_spec : ∀ K, HEq (comparisons.a.hom.app K).hom
    (rawPullComparison l Ω G.v E pullV K (completeY K)).hom
  pullU_spec : ∀ K, HEq (comparisons.a'.hom.app K).hom
    (rawPullComparison l Ω G.u E pullU K (completeX K)).hom
  sfExchange : sfCompactSupportFiniteIntegralFunctor l D.k
      (coefficientPrimeUnit l D hl) G.c (pbcFiniteField.{u} l Ω E) ⋙
      constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) G.v ⟶
    constructibleIntegralPullback l (pbcFiniteField.{u} l Ω E) G.u ⋙
      sfCompactSupportFiniteIntegralFunctor l D.k
        (coefficientPrimeUnit l D hl) G.c' (pbcFiniteField.{u} l Ω E)
  pbcExchange : integralSupport D l Ω G H E ⋙ integralPull D l Ω G P E ⟶
    integralPull' D l Ω G P' E ⋙ integralSupport' D l Ω G H' E
  uniformizerIdeal : Ideal.span (Set.range
      (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} l Ω E)) = (pbcStageDatum.{u} l Ω E).ideal
  completeInput : ∀ K : (sfIntegralConstructible l
      (pbcFiniteField.{u} l Ω E) G.X).FullSubcategory,
    cbcCompleteProperty (pbcStageDatum.{u} l Ω E) G.X 1
      (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} l Ω E) uniformizerIdeal
      ((((S.coefficients G.X).stage E).integral.functor.obj K).obj)
  pbcExchange_spec : ∀ K, HEq
    (pbcExchange.app (((S.coefficients G.X).stage E).integral.functor.obj K)).hom
    (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E)
      G.c G.c' G.w G.properSquare G.openSquare 1
      (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} l Ω E) uniformizerIdeal
      ⟨(((S.coefficients G.X).stage E).integral.functor.obj K).obj, completeInput K⟩)
  sfExchange_spec : ∀ K, HEq (sfExchange.app K).hom
    (frameworkExchange l (pbcFiniteField.{u} l Ω E) D G hl K)

/-- Simultaneous integral, raw rational and common-stage comparisons. The field maps
are the actual localizations of the integral maps; FamilyIso retains the coefficient
extension equations and their associators, rather than choosing new endpoint isos.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
structure FieldSquares
    (H : CbcCompactSupportCoefficientFamily l Ω G.c)
    (H' : CbcCompactSupportCoefficientFamily l Ω G.c')
    (P : CbcCompletedPullCoefficientFamily l Ω G.v)
    (P' : CbcCompletedPullCoefficientFamily l Ω G.u) where
  integral : ∀ E, IntegralSquare D l hl Ω G S H H' P P' E
  sfH : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω G.c
  sfH' : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω G.c'
  sfP : SfPullFamily l Ω G.v
  sfP' : SfPullFamily l Ω G.u
  b : FamilyIso (sfH.system.comp (S.coefficients G.Y).family)
    ((S.coefficients G.X).family.comp H.family.base)
  b' : FamilyIso (sfH'.system.comp (S.coefficients G.V).family)
    ((S.coefficients G.U).family.comp H'.family.base)
  a : FamilyIso (sfP.system.comp (S.coefficients G.V).family)
    ((S.coefficients G.Y).family.comp P.family.base)
  a' : FamilyIso (sfP'.system.comp (S.coefficients G.U).family)
    ((S.coefficients G.X).family.comp P'.family.base)
  b_spec : ∀ E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω G.X E),
    HEq ((b.finite E).hom.app K)
      ((pbcStageLocalization l Ω G.Y E).map ((integral E).comparisons.b.hom.app K.obj))
  b'_spec : ∀ E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω G.U E),
    HEq ((b'.finite E).hom.app K)
      ((pbcStageLocalization l Ω G.V E).map ((integral E).comparisons.b'.hom.app K.obj))
  a_spec : ∀ E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω G.Y E),
    HEq ((a.finite E).hom.app K)
      ((pbcStageLocalization l Ω G.V E).map ((integral E).comparisons.a.hom.app K.obj))
  a'_spec : ∀ E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω G.X E),
    HEq ((a'.finite E).hom.app K)
      ((pbcStageLocalization l Ω G.U E).map ((integral E).comparisons.a'.hom.app K.obj))
  sfExchange : StageSystem.Morphism.Hom
    (sfH.system.comp sfP.system) (sfP'.system.comp sfH'.system)
  pbcExchange : StageSystem.Morphism.Hom
    (H.family.base.comp P.family.base) (P'.family.base.comp H'.family.base)
  sfExchange_spec : ∀ E (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω G.X E),
    HEq ((sfExchange.τ E).app K)
      ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) G.V).map
        ((integral E).sfExchange.app K.obj))
  pbcExchange_spec : ∀ E (K : pbcStageCategory l Ω G.X E),
    HEq ((pbcExchange.τ E).app K)
      ((pbcStageLocalization l Ω G.V E).map ((integral E).pbcExchange.app K.obj))

variable {D l hl Ω G S}

/-- The raw finite-stage four-arrow comparison, without a second rational category.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def FieldSquares.finiteComparisons
    {H : CbcCompactSupportCoefficientFamily l Ω G.c}
    {H' : CbcCompactSupportCoefficientFamily l Ω G.c'}
    {P : CbcCompletedPullCoefficientFamily l Ω G.v}
    {P' : CbcCompletedPullCoefficientFamily l Ω G.u}
    (A : FieldSquares D l hl Ω G S H H' P P') (E : Padic.FiniteCoefficientFields l Ω) :
    ZlExchange.Comparisons
      ((S.coefficients G.X).family.Φ E) ((S.coefficients G.Y).family.Φ E)
      ((S.coefficients G.U).family.Φ E) ((S.coefficients G.V).family.Φ E)
      (A.sfH.system.Φ E) (A.sfH'.system.Φ E) (A.sfP.system.Φ E) (A.sfP'.system.Φ E)
      (H.family.base.Φ E) (H'.family.base.Φ E) (P.family.base.Φ E) (P'.family.base.Φ E) where
  b := A.b.finite E
  b' := A.b'.finite E
  a := A.a.finite E
  a' := A.a'.finite E

/-- The common-stage comparisons descend the compatible finite maps, with exactly the
specified composition associators of the pair-functor construction.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def FieldSquares.pairComparisons
    {H : CbcCompactSupportCoefficientFamily l Ω G.c}
    {H' : CbcCompactSupportCoefficientFamily l Ω G.c'}
    {P : CbcCompletedPullCoefficientFamily l Ω G.v}
    {P' : CbcCompletedPullCoefficientFamily l Ω G.u}
    (A : FieldSquares D l hl Ω G S H H' P P') :
    ZlExchange.Comparisons
      (S.coefficients G.X).family.functor (S.coefficients G.Y).family.functor
      (S.coefficients G.U).family.functor (S.coefficients G.V).family.functor
      A.sfH.system.functor A.sfH'.system.functor A.sfP.system.functor A.sfP'.system.functor
      H.family.base.functor H'.family.base.functor
      P.family.base.functor P'.family.base.functor where
  b := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ A.b.pair ≪≫
    StageSystem.Morphism.functorCompIso _ _
  b' := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ A.b'.pair ≪≫
    StageSystem.Morphism.functorCompIso _ _
  a := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ A.a.pair ≪≫
    StageSystem.Morphism.functorCompIso _ _
  a' := (StageSystem.Morphism.functorCompIso _ _).symm ≪≫ A.a'.pair ≪≫
    StageSystem.Morphism.functorCompIso _ _

/-- Framework exchange on the actual common-stage pair quotient. Every representative
is the image of the finite-stage map, with the specified composition comparisons.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def FieldSquares.sfPairExchange
    {H : CbcCompactSupportCoefficientFamily l Ω G.c}
    {H' : CbcCompactSupportCoefficientFamily l Ω G.c'}
    {P : CbcCompletedPullCoefficientFamily l Ω G.v}
    {P' : CbcCompletedPullCoefficientFamily l Ω G.u}
    (A : FieldSquares D l hl Ω G S H H' P P') :
    A.sfH.system.functor ⋙ A.sfP.system.functor ⟶
      A.sfP'.system.functor ⋙ A.sfH'.system.functor :=
  (StageSystem.Morphism.functorCompIso _ _).inv ≫
    StageSystem.Morphism.descNatTrans A.sfExchange ≫
    (StageSystem.Morphism.functorCompIso _ _).hom

/-- The specified PBC common-stage exchange, descending the normalized integral arrow.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
def FieldSquares.pbcPairExchange
    {H : CbcCompactSupportCoefficientFamily l Ω G.c}
    {H' : CbcCompactSupportCoefficientFamily l Ω G.c'}
    {P : CbcCompletedPullCoefficientFamily l Ω G.v}
    {P' : CbcCompletedPullCoefficientFamily l Ω G.u}
    (A : FieldSquares D l hl Ω G S H H' P P') :
    H.family.base.functor ⋙ P.family.base.functor ⟶
      P'.family.base.functor ⋙ H'.family.base.functor :=
  (StageSystem.Morphism.functorCompIso _ _).inv ≫
    StageSystem.Morphism.descNatTrans A.pbcExchange ≫
    (StageSystem.Morphism.functorCompIso _ _).hom

end SquareData

/-- One square's specified integral and coefficient-family data, bundled only to
index whole-diagram naturality without changing any of its categories or functors.
Source: thm-cbc-qbar.proof.md, common-stage descent
(blueprint: def-zl-framework-pbc-open-comparison-data). -/
structure SquarePacket (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (hl : l ≠ D.p) (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (G : OpenDiagram D l)
    (S : FdCoefficientComparisonSystem.{u} l Ω) where
  support : CbcCompactSupportCoefficientFamily l Ω G.c
  support' : CbcCompactSupportCoefficientFamily l Ω G.c'
  pull : CbcCompletedPullCoefficientFamily l Ω G.v
  pull' : CbcCompletedPullCoefficientFamily l Ω G.u
  data : FieldSquares D l hl Ω G S support support' pull pull'

end ZlFrameworkPbc
end WeilConjectures
