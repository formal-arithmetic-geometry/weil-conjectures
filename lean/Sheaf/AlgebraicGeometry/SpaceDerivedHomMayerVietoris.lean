module

public import Sheaf.AlgebraicGeometry.ElementaryEtaleShriekExact
public import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
public import Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.CategoryTheory.Localization.Adjunction
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.CategoryTheory.Localization.Adjunction
import Sheaf.Algebra.Homology.KFlatHomotopyTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Derived Hom for an elementary distinguished square of algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tags 08H9 and 08GV; derived.tex, Tag 0152;
sites-cohomology.tex, Tags 08FJ, 06YY and 0D6D
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris).

The module categories and their small-model equivalences are the recorded ones.
The connecting arrow is normalized by the actual signed extension-by-zero sequence,
including its canonical short-exact-sequence boundary. Pullback shift structures are
normalized by the existing total-derived comparison, rather than chosen arbitrarily.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

attribute [local instance 2000] Functor.preservesZeroMorphisms_of_additive

/-- Additivity of the already recorded restriction functor on complexes.
Source: Stacks 039Z (blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
instance spaceSmallModuleComplex_additive (X : AlgebraicSpace S) :
    (smallModuleComplex X).Additive :=
  inferInstanceAs (X.smallModuleRestriction.mapHomologicalComplex (.up ℤ)).Additive

/-- The canonical localization of an original-site complex through actual affine-chart
restriction. Source: Stacks 039Z, 05RU
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceOriginalComplexQ (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules] :
    CochainComplex X.Modules ℤ ⥤ X.DerivedModules :=
  smallModuleComplex X ⋙ DerivedCategory.Q

/-- The already defined étale sum functor on complexes; the witness supplies only
additivity, not new data. Source: Stacks 08GV
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceEtaleSumComplex (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (ex : EtaleModuleSumExact j hj) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  letI := ex.2.2.2.2.2.2.1
  (etaleModuleSum j hj).mapHomologicalComplex (.up ℤ)

/-- The chain-level evaluation counit, with no change of its normalization.
Source: Stacks 03DI, 08GV
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceEtaleSumComplexCounit (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (ex : EtaleModuleSumExact j hj) :
    spaceEtaleSumComplex j hj ex ⟶ 𝟭 (CochainComplex X.Modules ℤ) :=
  letI := ex.2.2.2.2.2.2.1
  NatTrans.mapHomologicalComplex (etaleModuleSumCounit j hj) (.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)).hom

/-- Compatibility with the total-derived counit specifies the canonical shifts of
unbounded tensor pullback. Source: Stacks 06YY, 05SC
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def SpacePullbackShiftNormalized (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (s : (spaceDerivedPullback f).CommShift ℤ) : Prop :=
  letI := s
  letI : (smallTensorPullbackComplex f).CommShift ℤ :=
    inferInstanceAs (((smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).CommShift ℤ)
  NatTrans.CommShift (spaceDerivedPullbackCounit f) ℤ

/-- Pullback on integral Ext, followed by its specified shift comparison.
Source: Stacks 08H9, 0D6D
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceExtPullback (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    (s : (spaceDerivedPullback f).CommShift ℤ)
    {E F : Y.DerivedModules} (n : ℤ) (a : E ⟶ F⟦n⟧) :
    (spaceDerivedPullback f).obj E ⟶ ((spaceDerivedPullback f).obj F)⟦n⟧ :=
  letI := s
  (spaceDerivedPullback f).map a ≫ ((spaceDerivedPullback f).commShiftIso n).hom.app F

/-- The local-to-overlap restriction, conjugated by the canonical pullback compositor.
Source: Stacks 08H9, 0D6D
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceExtRestrictionOver (j : Y ⟶ X) (k : Z ⟶ Y) (t : Z ⟶ X)
    (e : k ≫ j = t)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    [HasDerivedCategory.{w} Z.SmallModules]
    (s : (spaceDerivedPullback k).CommShift ℤ)
    {E F : X.DerivedModules} (n : ℤ)
    (a : (spaceDerivedPullback j).obj E ⟶ ((spaceDerivedPullback j).obj F)⟦n⟧) :
    (spaceDerivedPullback t).obj E ⟶ ((spaceDerivedPullback t).obj F)⟦n⟧ :=
  (eqToIso (congrArg spaceDerivedPullback e)).inv.app E ≫
    (spaceDerivedPullbackComp j k).hom.app E ≫ spaceExtPullback k s n a ≫
    ((spaceDerivedPullbackComp j k).inv.app F)⟦n⟧' ≫
    ((eqToIso (congrArg spaceDerivedPullback e)).hom.app F)⟦n⟧'

/-- The comparison of the two pullback paths in the square, constructed solely from
its commuting equation and the canonical derived-pullback compositors.
Source: Stacks 0D6D, 08H9
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceHomPullbackSquare {X' Y' : AlgebraicSpace S}
    (j : Y ⟶ X) (h : X' ⟶ X) (p : Y' ⟶ Y) (j' : Y' ⟶ X')
    (e : p ≫ j = j' ≫ h)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    [HasDerivedCategory.{w} X'.SmallModules] [HasDerivedCategory.{w} Y'.SmallModules] :
    spaceDerivedPullback j ⋙ spaceDerivedPullback p ≅
      spaceDerivedPullback h ⋙ spaceDerivedPullback j' :=
  (spaceDerivedPullbackComp j p).symm ≪≫
    eqToIso (congrArg spaceDerivedPullback e) ≪≫ spaceDerivedPullbackComp h j'

/-- Pullback on a local Ext group of a commuting base-change square, with both endpoints
identified by the fixed pullback-composition comparison. Source: Stacks 0D6D, 08H9
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceExtSquarePullback {X' Y' : AlgebraicSpace S}
    (j : Y ⟶ X) (h : X' ⟶ X) (p : Y' ⟶ Y) (j' : Y' ⟶ X')
    (e : p ≫ j = j' ≫ h)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
    [HasDerivedCategory.{w} X'.SmallModules] [HasDerivedCategory.{w} Y'.SmallModules]
    (s : (spaceDerivedPullback p).CommShift ℤ)
    {E F : X.DerivedModules} (n : ℤ)
    (a : (spaceDerivedPullback j).obj E ⟶ ((spaceDerivedPullback j).obj F)⟦n⟧) :
    (spaceDerivedPullback j').obj ((spaceDerivedPullback h).obj E) ⟶
      ((spaceDerivedPullback j').obj ((spaceDerivedPullback h).obj F))⟦n⟧ :=
  (spaceHomPullbackSquare j h p j' e).inv.app E ≫
    spaceExtPullback p s n a ≫
    ((spaceHomPullbackSquare j h p j' e).hom.app F)⟦n⟧'

/-- Termwise literal étale restriction. Source: Stacks 08FJ, 03DI
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceEtaleRestrictionComplex (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (ex : EtaleModuleSumExact j hj) :
    CochainComplex X.Modules ℤ ⥤ CochainComplex Z.Modules ℤ :=
  letI := ex.1
  (pullback j hj).mapHomologicalComplex (.up ℤ)

/-- Termwise extension by zero, using the recorded exact extension functor.
Source: Stacks 08FJ, 03DI
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceEtaleShriekComplex (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (ex : EtaleModuleSumExact j hj) :
    CochainComplex Z.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  letI := ex.2.2.2.1
  (etaleModuleShriek j hj).mapHomologicalComplex (.up ℤ)

/-- The original extension/restriction adjunction applied degreewise.
Source: Stacks 08FJ, 03DI
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceEtaleComplexAdjunction (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (ex : EtaleModuleSumExact j hj) :
    spaceEtaleShriekComplex j hj ex ⊣ spaceEtaleRestrictionComplex j hj ex :=
  letI := ex.1
  letI := ex.2.2.2.1
  (etaleModuleShriekAdjunction j hj).mapHomologicalComplex (.up ℤ)

/-- The small-model comparison from canonical tensor pullback of an original complex
to literal étale restriction. The ordinary comparison is fixed on every tensor section.
Source: Stacks 03LV, 03LW, 06YY, 08FJ
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceEtaleRestrictionComplexComparison (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (ex : EtaleModuleSumExact j hj)
    (e : moduleTensorPullback j ≅ pullback j hj)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Z.SmallModules]
    (P : CochainComplex X.Modules ℤ) :
    (spaceDerivedPullback j).obj ((spaceOriginalComplexQ X).obj P) ⟶
      (spaceOriginalComplexQ Z).obj ((spaceEtaleRestrictionComplex j hj ex).obj P) :=
  letI := ex.1
  moduleOriginalPullbackCounit j P ≫
    (spaceOriginalComplexQ Z).map
      ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)

/-- Regard the underlying triangle of a module chart as a morphism of the target's
small étale site, using the recorded étale-site functor.
Source: Stacks 03LP, 03LV
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceHomChartEtaleHom (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (V : X.EtaleSite) (q : ModuleChart j V) : (etaleMap j hj).obj q.left ⟶ V :=
  ⟨q.hom⟩

/-- A derived extension/restriction adjunction normalized on all chain maps.
The ordinary tensor comparison is specified on every local tensor, and the Hom
transpose equation fixes the extension comparison using the original adjunction.
Thus no automorphism of the lift summands can change the connecting boundary.
Source: Stacks 08FJ, 08GV, 03DI
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
structure SpaceEtaleHomAdjunction (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (ex : EtaleModuleSumExact j hj)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Z.SmallModules] where
  /-- The ordinary tensor-to-literal-restriction comparison. -/
  ordinaryRestriction : moduleTensorPullback j ≅ pullback j hj
  /-- Its normalization is multiplication on the actual original chart sections. -/
  ordinarySections : ∀ (N : X.Modules) (V : X.EtaleSite) (q : ModuleChart j V)
      (c : Z.structureSheaf.obj.obj (Opposite.op q.left)) (m : N.val.obj (Opposite.op V)),
    (ordinaryRestriction.hom.app N).val.app (Opposite.op q.left)
        (moduleTensorSection j N V q c m) =
      c • N.val.map (spaceHomChartEtaleHom j hj V q).op m
  /-- The left adjoint of the fixed canonical derived restriction. -/
  shriek : Z.DerivedModules ⥤ X.DerivedModules
  /-- The extension/restriction Hom universal property. -/
  adj : shriek ⊣ spaceDerivedPullback j
  /-- Computation of extension on every original complex. -/
  shriekFactors : spaceOriginalComplexQ Z ⋙ shriek ≅
    spaceEtaleShriekComplex j hj ex ⋙ spaceOriginalComplexQ X
  /-- Transposition is the localization of the specified original transposition. -/
  transpose : ∀ (P : CochainComplex Z.Modules ℤ) (Q : CochainComplex X.Modules ℤ)
      (f : (spaceEtaleShriekComplex j hj ex).obj P ⟶ Q),
    adj.homEquiv _ _ (shriekFactors.hom.app P ≫ (spaceOriginalComplexQ X).map f) ≫
      spaceEtaleRestrictionComplexComparison j hj ex ordinaryRestriction Q =
        (spaceOriginalComplexQ Z).map
          ((spaceEtaleComplexAdjunction j hj ex).homEquiv _ _ f)
  /-- Computation of the sum-extension on every complex. -/
  factors : spaceOriginalComplexQ X ⋙ spaceDerivedPullback j ⋙ shriek ≅
    spaceEtaleSumComplex j hj ex ⋙ spaceOriginalComplexQ X
  /-- The composite factorization uses precisely the restriction comparison above and
  the extension comparison, not a new automorphism preserving evaluation. -/
  factors_normalized : ∀ P : CochainComplex X.Modules ℤ,
    factors.hom.app P =
      shriek.map (spaceEtaleRestrictionComplexComparison j hj ex ordinaryRestriction P) ≫
        shriekFactors.hom.app ((spaceEtaleRestrictionComplex j hj ex).obj P)
  /-- Evaluation agrees with the specified original-site counit. -/
  evaluation : ∀ P : CochainComplex X.Modules ℤ,
    adj.counit.app ((spaceOriginalComplexQ X).obj P) =
      factors.hom.app P ≫
        (spaceOriginalComplexQ X).map ((spaceEtaleSumComplexCounit j hj ex).app P)

/-- The boundary obtained by transposing a local Ext class and composing its shifted
transpose with the canonical extension-by-zero triangle boundary.
Source: Stacks 08H9, 08FJ, 0152
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceHomConnecting (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (ex : EtaleModuleSumExact j hj)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Z.SmallModules]
    (s : (spaceDerivedPullback j).CommShift ℤ) (M : SpaceEtaleHomAdjunction j hj ex)
    (delta : ∀ E : X.DerivedModules,
      E ⟶ (M.shriek.obj ((spaceDerivedPullback j).obj E))⟦(1 : ℤ)⟧)
    (E F : X.DerivedModules) (n : ℤ)
    (a : (spaceDerivedPullback j).obj E ⟶ ((spaceDerivedPullback j).obj F)⟦n⟧) :
    E ⟶ F⟦n + 1⟧ :=
  letI := s
  delta E ≫
    ((M.adj.homEquiv _ _).symm
      (a ≫ ((spaceDerivedPullback j).commShiftIso n).inv.app F))⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd X.DerivedModules n (1 : ℤ)).inv.app F

section Square

variable {U V T : AlgebraicSpace S}
  (jU : U ⟶ X) (jV : V ⟶ X) (a : T ⟶ U) (b : T ⟶ V)
  (sq : IsPullback a b jU jV)
  (hU : IsEtale jU.hom.hom) (hV : IsEtale jV.hom.hom)
  (ha : IsEtale a.hom.hom) (hb : IsEtale b.hom.hom)
  (exU : EtaleModuleSumExact jU hU) (exV : EtaleModuleSumExact jV hV)
  (exT : EtaleModuleSumExact (a ≫ jU)
    (isEtale_comp a.hom.hom jU.hom.hom ha hU))
  (addB : (etaleModuleSum jU hU ⊞ etaleModuleSum jV hV).Additive)

/-- The middle term of the original signed sequence on complexes.
Source: Stacks 08GV (blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceElementaryMiddleComplex :
    CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  letI := addB
  (etaleModuleSum jU hU ⊞ etaleModuleSum jV hV).mapHomologicalComplex (.up ℤ)

/-- The chain map induced by the actual signed overlap counits.
Source: Stacks 08GV (blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceElementaryFirstComplex :
    spaceEtaleSumComplex (a ≫ jU) (isEtale_comp a.hom.hom jU.hom.hom ha hU) exT ⟶
      spaceElementaryMiddleComplex jU jV hU hV addB :=
  letI := exT.2.2.2.2.2.2.1
  letI := addB
  NatTrans.mapHomologicalComplex
    (elementaryEtaleSumDifferential jU jV (a ≫ jU) a b hU hV
      (isEtale_comp a.hom.hom jU.hom.hom ha hU) ha hb rfl sq.w.symm) (.up ℤ)

/-- The chain map induced by the sum of the two original evaluation counits.
Source: Stacks 08GV (blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def spaceElementarySecondComplex :
    spaceElementaryMiddleComplex jU jV hU hV addB ⟶ 𝟭 (CochainComplex X.Modules ℤ) :=
  letI := addB
  NatTrans.mapHomologicalComplex (elementaryEtaleSumEvaluation jU jV hU hV) (.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)).hom

variable [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
  [HasDerivedCategory.{w} V.SmallModules] [HasDerivedCategory.{w} T.SmallModules]

/-- Normalization on every representative by the canonical SES triangle after actual
small-model restriction. Existence of the zero-composite and short-exactness proofs is
included, so the representative condition cannot be vacuous.
Source: Stacks 08GV(2), 0152
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def SpaceHomDeltaNormalized
    (M : SpaceEtaleHomAdjunction (a ≫ jU)
      (isEtale_comp a.hom.hom jU.hom.hom ha hU) exT)
    (delta : ∀ E : X.DerivedModules,
      E ⟶ (M.shriek.obj ((spaceDerivedPullback (a ≫ jU)).obj E))⟦(1 : ℤ)⟧) : Prop :=
  ∀ P : CochainComplex X.Modules ℤ,
    ∃ hz : (spaceElementaryFirstComplex jU jV a b sq hU hV ha hb exT addB).app P ≫
      (spaceElementarySecondComplex jU jV hU hV addB).app P = 0,
    ∃ hs : ((ShortComplex.mk
      ((spaceElementaryFirstComplex jU jV a b sq hU hV ha hb exT addB).app P)
      ((spaceElementarySecondComplex jU jV hU hV addB).app P) hz).map
        (smallModuleComplex X)).ShortExact,
      delta ((spaceOriginalComplexQ X).obj P) = DerivedCategory.triangleOfSESδ (C := X.SmallModules)
        (S := (ShortComplex.mk
          ((spaceElementaryFirstComplex jU jV a b sq hU hV ha hb exT addB).app P)
          ((spaceElementarySecondComplex jU jV hU hV addB).app P) hz).map
            (smallModuleComplex X)) hs ≫
        (M.factors.inv.app P)⟦(1 : ℤ)⟧'

/-- Exactness at all three kinds of terms, additivity of the boundary, and its two
variances. Integral `n` includes the preceding overlap term by replacing `n` with `n-1`.
Source: Stacks 08H9 and derived.tex 0149
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def SpaceHomLES
    (sU : (spaceDerivedPullback jU).CommShift ℤ)
    (sV : (spaceDerivedPullback jV).CommShift ℤ)
    (sa : (spaceDerivedPullback a).CommShift ℤ)
    (sb : (spaceDerivedPullback b).CommShift ℤ)
    (boundary : ∀ (E F : X.DerivedModules) (n : ℤ),
      ((spaceDerivedPullback (a ≫ jU)).obj E ⟶
        ((spaceDerivedPullback (a ≫ jU)).obj F)⟦n⟧) → (E ⟶ F⟦n + 1⟧)) : Prop :=
  (∀ (E F : X.DerivedModules) (n : ℤ),
    (∀ x y, boundary E F n (x + y) = boundary E F n x + boundary E F n y) ∧
    Function.Exact
      (fun f : E ⟶ F⟦n⟧ ↦
        (spaceExtPullback jU sU n f, spaceExtPullback jV sV n f))
      (fun p :
        ((spaceDerivedPullback jU).obj E ⟶ ((spaceDerivedPullback jU).obj F)⟦n⟧) ×
        ((spaceDerivedPullback jV).obj E ⟶ ((spaceDerivedPullback jV).obj F)⟦n⟧) ↦
        spaceExtRestrictionOver jU a (a ≫ jU) rfl sa n p.1 -
        spaceExtRestrictionOver jV b (a ≫ jU) sq.w.symm sb n p.2) ∧
    Function.Exact
      (fun p :
        ((spaceDerivedPullback jU).obj E ⟶ ((spaceDerivedPullback jU).obj F)⟦n⟧) ×
        ((spaceDerivedPullback jV).obj E ⟶ ((spaceDerivedPullback jV).obj F)⟦n⟧) ↦
        spaceExtRestrictionOver jU a (a ≫ jU) rfl sa n p.1 -
        spaceExtRestrictionOver jV b (a ≫ jU) sq.w.symm sb n p.2)
      (boundary E F n) ∧
    Function.Exact (boundary E F n)
      (fun f : E ⟶ F⟦n + 1⟧ ↦
        (spaceExtPullback jU sU (n + 1) f, spaceExtPullback jV sV (n + 1) f))) ∧
  (∀ (E E' F : X.DerivedModules) (x : E' ⟶ E) (n : ℤ) f,
    boundary E' F n ((spaceDerivedPullback (a ≫ jU)).map x ≫ f) =
      x ≫ boundary E F n f) ∧
  (∀ (E F F' : X.DerivedModules) (y : F ⟶ F') (n : ℤ) f,
    boundary E F' n (f ≫ ((spaceDerivedPullback (a ≫ jU)).map y)⟦n⟧') =
      boundary E F n f ≫ y⟦n + 1⟧')

end Square

/-- All the canonical boundary data for this square. No geometric hypothesis is hidden
in the record: its existence under precisely the elementary-square hypotheses is the
main theorem below. Source: Stacks 08H9, 08GV, 08FJ, 0152
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
structure SpaceHomMayerVietorisData {U V T : AlgebraicSpace S}
    (jU : U ⟶ X) (jV : V ⟶ X) (a : T ⟶ U) (b : T ⟶ V)
    (sq : IsPullback a b jU jV) (hV : IsEtale jV.hom.hom)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
    [HasDerivedCategory.{w} V.SmallModules] [HasDerivedCategory.{w} T.SmallModules] where
  /-- Étaleness of the open inclusion. -/
  hU : IsEtale jU.hom.hom
  /-- Étaleness of the first overlap projection. -/
  ha : IsEtale a.hom.hom
  /-- Étaleness of the second overlap projection. -/
  hb : IsEtale b.hom.hom
  /-- Exactness of the recorded open sum functor. -/
  exU : EtaleModuleSumExact jU hU
  /-- Exactness of the recorded étale sum functor. -/
  exV : EtaleModuleSumExact jV hV
  /-- Exactness of the recorded overlap sum functor. -/
  exT : EtaleModuleSumExact (a ≫ jU) (isEtale_comp a.hom.hom jU.hom.hom ha hU)
  /-- Additivity of the middle sum, needed to apply it termwise. -/
  addB : (etaleModuleSum jU hU ⊞ etaleModuleSum jV hV).Additive
  /-- Shift comparison for restriction to U. -/
  sU : (spaceDerivedPullback jU).CommShift ℤ
  /-- Shift comparison for restriction to V. -/
  sV : (spaceDerivedPullback jV).CommShift ℤ
  /-- Shift comparison for restriction from U to T. -/
  sa : (spaceDerivedPullback a).CommShift ℤ
  /-- Shift comparison for restriction from V to T. -/
  sb : (spaceDerivedPullback b).CommShift ℤ
  /-- Shift comparison for restriction to T. -/
  sT : (spaceDerivedPullback (a ≫ jU)).CommShift ℤ
  /-- Every shift is fixed by its existing total-derived comparison. -/
  shifts : SpacePullbackShiftNormalized jU sU ∧ SpacePullbackShiftNormalized jV sV ∧
    SpacePullbackShiftNormalized a sa ∧ SpacePullbackShiftNormalized b sb ∧
    SpacePullbackShiftNormalized (a ≫ jU) sT
  /-- The normalized overlap extension/restriction adjunction. -/
  overlap : SpaceEtaleHomAdjunction (a ≫ jU)
    (isEtale_comp a.hom.hom jU.hom.hom ha hU) exT
  /-- The canonical extension-by-zero triangle boundary. -/
  delta : ∀ E : X.DerivedModules,
    E ⟶ (overlap.shriek.obj ((spaceDerivedPullback (a ≫ jU)).obj E))⟦(1 : ℤ)⟧
  /-- On every complex this is precisely the SES boundary. -/
  normalized : SpaceHomDeltaNormalized jU jV a b sq hU hV ha hb exT addB overlap delta
  /-- Exactness and both variances for the specified Hom boundary. -/
  exact : SpaceHomLES jU jV a b sq sU sV sa sb
    (spaceHomConnecting (a ≫ jU) (isEtale_comp a.hom.hom jU.hom.hom ha hU)
      exT sT overlap delta)

/-- The specified boundary, as an explicit function rather than an arbitrary additive map.
Source: Stacks 08H9, 08GV (blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def SpaceHomMayerVietorisData.boundary {U V T : AlgebraicSpace S}
    {jU : U ⟶ X} {jV : V ⟶ X} {a : T ⟶ U} {b : T ⟶ V}
    {sq : IsPullback a b jU jV} {hV : IsEtale jV.hom.hom}
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
    [HasDerivedCategory.{w} V.SmallModules] [HasDerivedCategory.{w} T.SmallModules]
    (M : SpaceHomMayerVietorisData jU jV a b sq hV) :=
  spaceHomConnecting (a ≫ jU) (isEtale_comp a.hom.hom jU.hom.hom M.ha M.hU)
    M.exT M.sT M.overlap M.delta

/-- The three squares of a morphism of the displayed long exact sequences. Every map
is the canonical pullback on Ext, including the endpoint compositors and shifts.
Source: Stacks 08H9, 08GV and sites-cohomology.tex 0D6D
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris). -/
def SpaceHomBaseChange {U V T X' U' V' T' : AlgebraicSpace S}
    {jU : U ⟶ X} {jV : V ⟶ X} {a : T ⟶ U} {b : T ⟶ V}
    {sq : IsPullback a b jU jV} {hV : IsEtale jV.hom.hom}
    {jU' : U' ⟶ X'} {jV' : V' ⟶ X'} {a' : T' ⟶ U'} {b' : T' ⟶ V'}
    {sq' : IsPullback a' b' jU' jV'} {hV' : IsEtale jV'.hom.hom}
    (h : X' ⟶ X) (pU : U' ⟶ U) (pV : V' ⟶ V) (pT : T' ⟶ T)
    (eU : pU ≫ jU = jU' ≫ h) (eV : pV ≫ jV = jV' ≫ h)
    (eT : pT ≫ (a ≫ jU) = (a' ≫ jU') ≫ h)
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
    [HasDerivedCategory.{w} V.SmallModules] [HasDerivedCategory.{w} T.SmallModules]
    [HasDerivedCategory.{w} X'.SmallModules] [HasDerivedCategory.{w} U'.SmallModules]
    [HasDerivedCategory.{w} V'.SmallModules] [HasDerivedCategory.{w} T'.SmallModules]
    (M : SpaceHomMayerVietorisData jU jV a b sq hV)
    (M' : SpaceHomMayerVietorisData jU' jV' a' b' sq' hV')
    (sh : (spaceDerivedPullback h).CommShift ℤ)
    (spU : (spaceDerivedPullback pU).CommShift ℤ)
    (spV : (spaceDerivedPullback pV).CommShift ℤ)
    (spT : (spaceDerivedPullback pT).CommShift ℤ) : Prop :=
  ∀ (E F : X.DerivedModules) (n : ℤ),
    (∀ f : E ⟶ F⟦n⟧,
      spaceExtSquarePullback jU h pU jU' eU spU n (spaceExtPullback jU M.sU n f) =
        spaceExtPullback jU' M'.sU n (spaceExtPullback h sh n f)) ∧
    (∀ f : E ⟶ F⟦n⟧,
      spaceExtSquarePullback jV h pV jV' eV spV n (spaceExtPullback jV M.sV n f) =
        spaceExtPullback jV' M'.sV n (spaceExtPullback h sh n f)) ∧
    (∀ (fU : (spaceDerivedPullback jU).obj E ⟶ ((spaceDerivedPullback jU).obj F)⟦n⟧)
      (fV : (spaceDerivedPullback jV).obj E ⟶ ((spaceDerivedPullback jV).obj F)⟦n⟧),
      spaceExtSquarePullback (a ≫ jU) h pT (a' ≫ jU') eT spT n
        (spaceExtRestrictionOver jU a (a ≫ jU) rfl M.sa n fU -
          spaceExtRestrictionOver jV b (a ≫ jU) sq.w.symm M.sb n fV) =
        spaceExtRestrictionOver jU' a' (a' ≫ jU') rfl M'.sa n
          (spaceExtSquarePullback jU h pU jU' eU spU n fU) -
        spaceExtRestrictionOver jV' b' (a' ≫ jU') sq'.w.symm M'.sb n
          (spaceExtSquarePullback jV h pV jV' eV spV n fV)) ∧
    (∀ f : (spaceDerivedPullback (a ≫ jU)).obj E ⟶
        ((spaceDerivedPullback (a ≫ jU)).obj F)⟦n⟧,
      spaceExtPullback h sh (n + 1) (M.boundary E F n f) =
        M'.boundary ((spaceDerivedPullback h).obj E) ((spaceDerivedPullback h).obj F) n
          (spaceExtSquarePullback (a ≫ jU) h pT (a' ≫ jU') eT spT n f))

/-- The full unbounded Mayer--Vietoris sequence, its canonical boundary, its two
variances and arbitrary derived-pullback compatibility.
Source: Stacks Project, spaces-perfect.tex 08H9, 08GV, 08GN(2);
sites-cohomology.tex 08FJ, 06YS, 06YY, 0D6D; derived.tex 0152, 0149, 05SC, 05SU
(blueprint: lem-sfb-space-derived-hom-mayer-vietoris).

Proof:
1. The exact additive endofunctors and signed counits of
lem-sfb-space-elementary-shriek-exact give a termwise SES of complexes.
Exact functors descend through localization
(lem-weil-pbc-exact-functor-derived-factorization). The canonical SES triangle
(lem-weil-pbc-complex-ses-triangle) is natural by its cone construction and the
fully faithful precomposition property of lem-weil-pbc-localization-universal-property.
2. Localize the termwise extension/restriction adjunction, using
lem-weil-pbc-termwise-adjunction-homotopy and lem-sfb-adjunction-localization.
Its counit is the original evaluation, and its degree-zero unit and counit commute
with integral shifts. No boundedness is involved.
3. Apply lem-weil-pbc-hom-out-of-triangle-exact and all rotations and shifts of
def-weil-triangulated-category. The adjunction identifies the local Hom terms.
For a transposed overlap class c the boundary is delta followed by c[1], exactly
spaceHomConnecting. This gives the three exactness assertions for every integer n.
4. Precomposition with evaluation is restriction, by the adjunction triangle identity.
Nested counits agree on every direct-sum generator, so the first signed arrow gives
the difference of restrictions. Naturality of the SES triangle in E and composition
in F give the two boundary naturality equations.
5. After any h the reduced complement is formed on X', not by assuming the old
complement remains reduced. Use lem-sfb-space-reduced-closed-support and
lem-sfb-space-elementary-shriek-exact. On reduced scheme charts the new complement
factors through the old base change, since a function vanishing everywhere is nilpotent
and hence zero. Base change the old complement isomorphism to obtain the new one.
The canonical restriction comparison is lem-sfb-space-derived-etale-chart-calculus.
6. Resolve E by a flat-term K-flat complex P (lem-pc-kflat-resolution).
By lem-sfb-space-etale-sum-pullback its three sum extensions remain flat-term K-flat.
The middle sum and cone are K-flat by lem-sfb-kflat-homotopy-triangulated; its tensor
hypotheses follow from lem-pc-sheaf-modules-tensor-closed and
lem-weil-pbc-module-sheaves-colimits-forgetful. Tensor preserves colimits by its
closed adjunction. Thus every term computes Lh* by ordinary pullback
(lem-weil-pbc-ringed-topoi-derived-pullback).
7. The comparisons of lem-sfb-space-etale-sum-pullback preserve nested counits and
finite sums, so identify the pulled-back signed SES with the new signed SES.
Apply lem-sfb-ringed-kflat-pullback-ses-triangle: additive pullback preserves the
strict cone and its maps, and the boundary is -p q^{-1}. Together with naturality
of lem-weil-pbc-complex-ses-triangle this identifies the last arrows too.
8. The same comparisons preserve evaluation. The normalized adjunction of
lem-sfb-adjunction-localization therefore identifies local Ext pullback with Lh_A*.
Writing c for the overlap comparison, the boundary identity is
(a c^{-1})[1] c[1] Lh*(delta) = Lh*(a[1] delta).
The signed counits give the other squares. This proves the asserted morphism of
long exact sequences without flatness, quasi-compactness, or cohomological bounds. -/
theorem space_derived_hom_mayer_vietoris {U V T : AlgebraicSpace S}
    (jU : U ⟶ X) (jV : V ⟶ X) (a : T ⟶ U) (b : T ⟶ V)
    (sq : IsPullback a b jU jV)
    (hOpen : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) jU.hom.hom)
    (hV : IsEtale jV.hom.hom) (C : ClosedSubspace X)
    (hC : IsReduced (C.val : AlgebraicSpace S))
    (hSupport : pointImage C.val.arrow.hom.hom = (pointImage jU.hom.hom)ᶜ)
    (hIso : IsIso (Limits.pullback.snd jV.hom C.val.arrow.hom))
    [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} U.SmallModules]
    [HasDerivedCategory.{w} V.SmallModules] [HasDerivedCategory.{w} T.SmallModules] :
    ∃ M : SpaceHomMayerVietorisData jU jV a b sq hV,
      ∀ (X' U' V' T' : AlgebraicSpace S) (h : X' ⟶ X)
        (jU' : U' ⟶ X') (jV' : V' ⟶ X') (a' : T' ⟶ U') (b' : T' ⟶ V')
        (sq' : IsPullback a' b' jU' jV')
        (pU : U' ⟶ U) (pV : V' ⟶ V) (pT : T' ⟶ T)
        (sqU : IsPullback pU jU' jU h) (sqV : IsPullback pV jV' jV h)
        (sqT : IsPullback pT (a' ≫ jU') (a ≫ jU) h),
        pT ≫ a = a' ≫ pU → pT ≫ b = b' ≫ pV →
        ∀ [HasDerivedCategory.{w} X'.SmallModules] [HasDerivedCategory.{w} U'.SmallModules]
          [HasDerivedCategory.{w} V'.SmallModules] [HasDerivedCategory.{w} T'.SmallModules],
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) jU'.hom.hom ∧
        ∃ (hV' : IsEtale jV'.hom.hom) (C' : ClosedSubspace X'),
          IsReduced (C'.val : AlgebraicSpace S) ∧
          pointImage C'.val.arrow.hom.hom = (pointImage jU'.hom.hom)ᶜ ∧
          IsIso (Limits.pullback.snd jV'.hom C'.val.arrow.hom) ∧
          ∃ (M' : SpaceHomMayerVietorisData jU' jV' a' b' sq' hV')
            (sh : (spaceDerivedPullback h).CommShift ℤ)
            (spU : (spaceDerivedPullback pU).CommShift ℤ)
            (spV : (spaceDerivedPullback pV).CommShift ℤ)
            (spT : (spaceDerivedPullback pT).CommShift ℤ),
            SpacePullbackShiftNormalized h sh ∧ SpacePullbackShiftNormalized pU spU ∧
            SpacePullbackShiftNormalized pV spV ∧ SpacePullbackShiftNormalized pT spT ∧
            SpaceHomBaseChange h pU pV pT sqU.w sqV.w sqT.w M M' sh spU spV spT := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
