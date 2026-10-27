/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.SixFunctors.FiniteExceptional
public import Sheaf.SixFunctors.IntegralDualizing
public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.SixFunctors.IntegralSystemOperations
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-!
# Data for finite operations on normalized derived coefficient systems

Source: blueprint finite exceptional dual formula and enriched adjunction,
`sec-six-functors/sk-thm-sf-package/lem-coef-finite-exceptional`;
Stacks Project, Tags 06YS, 0A95, 0941 and 079P
(blueprint: def-coef-finite-adjunction-system-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The full normalized category, with finite Tor constructibility separately at each level.
There is no quantifier imposing a uniform cohomological or Tor interval.
Source: the node's first paragraph
(blueprint: def-coef-finite-adjunction-system-data). -/
def domain (W : Scheme.{u}) : ObjectProperty (coefficientSequenceDerived l E W) :=
  fun M ↦ IsNormalizedCoefficientSequence l E W M ∧
    ∀ n : ℕ, FiniteExceptional.domain l E W n
      ((coefficientSequenceDerivedEvaluation l E W n).obj M)

/-- Restriction of the recorded exact evaluation to its actual finite-Tor domain.
Source: the node's first paragraph
(blueprint: def-coef-finite-adjunction-system-data). -/
def evaluation (W : Scheme.{u}) (n : ℕ) :
    (domain l E W).FullSubcategory ⥤ (FiniteExceptional.domain l E W n).FullSubcategory :=
  (FiniteExceptional.domain l E W n).lift
    ((domain l E W).ι ⋙ coefficientSequenceDerivedEvaluation l E W n)
    (fun M ↦ M.property.2 n)

/-- Actual ordinary adjunction, fixed by sectionwise system direct image.
Source: Stacks 03D2, 0941
(blueprint: def-coef-finite-adjunction-system-data). -/
def ordinaryAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)

/-- Additivity follows from the actual ordinary adjunction, with no extra theorem.
Source: Stacks 03D2 (blueprint: def-coef-finite-adjunction-system-data). -/
instance directAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralComparisonSequenceDirectImage l E f).Additive :=
  letI : (integralComparisonSequenceDirectImage l E f).leftAdjoint.Additive :=
    integralComparisonSequencePullbackAdditive l E f
  (ordinaryAdj l E f).right_adjoint_additive

/-- A universal derived geometric image together with its exact localization comparison.
The derived adjunction is normalized on every cochain map by `CoefficientDerivedImage`.
Source: Stacks 07A4, 0941; node proof steps 1 and 15
(blueprint: def-coef-finite-adjunction-system-data). -/
structure Geometry {X Y : Scheme.{u}} (f : X ⟶ Y)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SY : CoefficientDerivedSystemCalculus l E Y) where
  image : SheafOfModules.CoefficientDerivedImage
    (integralComparisonSequencePullback l E f)
    (integralComparisonSequenceDirectImage l E f) (ordinaryAdj l E f)
  /-- The exact inverse image is the recorded termwise localization. -/
  pull : image.inverse ≅ integralComparisonDerivedSequencePullback l E f
  pull_factors : ∀ C, pull.hom.app (DerivedCategory.Q.obj C) ≫
      (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C =
    image.inverseFactors.hom.app C
  /-- This comparison is the identity on all underlying sections. -/
  ordinaryDirect : integralComparisonSequenceDirectImage l E f ≅
    pullbackTensorSequenceDirect l E f
  ordinaryDirect_sections : ∀ (M : coefficientSequenceModules l E X)
    (V : (ℕ × Y.ProEt)ᵒᵖ) (x : ((integralComparisonSequenceDirectImage l E f).obj M).val.obj V),
    HEq ((ordinaryDirect.hom.app M).val.app V x) x
  /-- Tensor pullback is an actual comparison on the system category. -/
  tensor : SY.systemClosed.tensor ⋙
      integralComparisonDerivedSequencePullback l E f ≅
    (integralComparisonDerivedSequencePullback l E f).prod
      (integralComparisonDerivedSequencePullback l E f) ⋙ SX.systemClosed.tensor
  /-- The comparison is fixed on all total summands of simultaneous flat resolutions. -/
  tensor_model : SemilinearSections.TensorComparisonModel.{u+1, u, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
    (integralComparisonSequencePullback l E f) SY.systemClosed SX.systemClosed
    SY.systemTensorModel SX.systemTensorModel tensor
  /-- The ordinary map sends tensor products of adjunction-unit sections to their tensor.
  This pins the ordinary map before localization and rules out rescaling it. -/
  tensor_unit : ∀ (M N : coefficientSequenceModules l E Y) (U : (ℕ × Y.ProEt)ᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U),
    ((tensor_model.ordinary M N).hom.val.app
      ((integralComparisonSequenceBaseChange f).op.obj U))
        (((ordinaryAdj l E f).unit.app
          (SemilinearSections.ordinaryTensor.{u+1, u, u}
            (coefficientSequenceTopology (Scheme.ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y) M N)).val.app U
              (SemilinearSections.tensorSection.{u+1, u, u}
                (coefficientSequenceTopology (Scheme.ProEt.topology Y))
                (coefficientSequenceCommRingSheaf l E Y) M N U x y)) =
      SemilinearSections.tensorSection.{u+1, u, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        ((integralComparisonSequencePullback l E f).obj M)
        ((integralComparisonSequencePullback l E f).obj N)
        ((integralComparisonSequenceBaseChange f).op.obj U)
        (((ordinaryAdj l E f).unit.app M).val.app U x)
        (((ordinaryAdj l E f).unit.app N).val.app U y)

/-- The right-derived adjunction expressed using the recorded exact inverse image.
Source: Stacks 07A6; node proof step 15
(blueprint: def-coef-finite-adjunction-system-data). -/
def Geometry.adjunction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SY : CoefficientDerivedSystemCalculus l E Y} (g : Geometry l E f SX SY) :
    integralComparisonDerivedSequencePullback l E f ⊣ g.image.direct :=
  g.image.adjunction.ofNatIsoLeft g.pull

/-- The inverse-image transport is forced by the sectionwise identity comparison.
Source: Stacks 03D2, 0941 (blueprint: def-coef-finite-adjunction-system-data). -/
def Geometry.pullTransport {X Y : Scheme.{u}} {f : X ⟶ Y}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SY : CoefficientDerivedSystemCalculus l E Y} (g : Geometry l E f SX SY) :
    integralComparisonDerivedSequencePullback l E f ≅ pullbackTensorSequenceDerived l E f :=
  Functor.mapDerivedCategoryNatIso
    ((ordinaryAdj l E f).leftAdjointUniq
      ((pullbackTensorSequenceAdjunction l E f).ofNatIsoRight g.ordinaryDirect.symm))

/-- Evaluation of this inverse image is the published cochain-normalized comparison.
Source: Stacks 0941 (blueprint: def-coef-finite-adjunction-system-data). -/
def Geometry.pullEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SY : CoefficientDerivedSystemCalculus l E Y} (g : Geometry l E f SX SY) (n : ℕ) :
    integralComparisonDerivedSequencePullback l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f :=
  Functor.isoWhiskerRight g.pullTransport _ ≪≫ pullbackTensorDerivedEvaluation l E f n

/-- The canonical system proper projection is the ordinary-image counit transpose.
Source: Stacks 07A4; node proof steps 12 and 14
(blueprint: def-coef-finite-adjunction-system-data). -/
def Geometry.projection {X Y : Scheme.{u}} {f : X ⟶ Y}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SY : CoefficientDerivedSystemCalculus l E Y} (g : Geometry l E f SX SY)
    (M : coefficientSequenceDerived l E X) (P : coefficientSequenceDerived l E Y) :
    SY.systemClosed.tensor.obj (g.image.direct.obj M, P) ⟶
      g.image.direct.obj (SX.systemClosed.tensor.obj
        (M, (integralComparisonDerivedSequencePullback l E f).obj P)) :=
  (g.adjunction l E).homEquiv _ _
    (g.tensor.hom.app (g.image.direct.obj M, P) ≫
      SX.systemClosed.tensor.map
        (Prod.mkHom ((g.adjunction l E).counit.app M) (𝟙 _)))

/-- The simultaneous proper/open construction on actual strict coefficient systems.
Open extension is the exact left adjoint of the recorded inverse image; proper image
is the universal derived image in `Geometry`, rather than a levelwise lift.
Source: node proof steps 1, 2 and 6; Stacks 03DI, 07A4
(blueprint: def-coef-finite-adjunction-system-data). -/
structure Support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SZ : CoefficientDerivedSystemCalculus l E c.Z)
    (SY : CoefficientDerivedSystemCalculus l E Y) where
  openGeometry : Geometry l E c.i SX SZ
  properGeometry : Geometry l E c.g SZ SY
  extension : coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E c.Z
  [extensionAdditive : extension.Additive]
  [extensionLimits : PreservesFiniteLimits extension]
  [extensionColimits : PreservesFiniteColimits extension]
  openAdjunction : extension ⊣ integralComparisonSequencePullback l E c.i
  /-- Published local proper/open evaluations, with their unit/counit normalizations. -/
  finiteProper : IntegralSystemRealization.Direct l E c.g
  finiteProperEvaluation : IntegralSystemRealization.DirectEvaluation l E finiteProper
  finiteOpen : IntegralSystemRealization.Open l E c.i
  finiteOpenEvaluation : IntegralSystemRealization.OpenEvaluation l E finiteOpen
  /-- Invertibility of the actual open-unit tensor transpose, used in the projection. -/
  openTensorInvertible : ∀ (M : coefficientSequenceDerived l E X)
    (P : coefficientSequenceDerived l E c.Z),
    IsIso (((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      openAdjunction).homEquiv _ _).symm
        (SX.systemClosed.tensor.map (Prod.mkHom
          ((SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
            openAdjunction).unit.app M) (𝟙 _)) ≫
          openGeometry.tensor.inv.app (extension.mapDerivedCategory.obj M, P)))

attribute [instance] Support.extensionAdditive Support.extensionLimits Support.extensionColimits

variable {l E}

/-- Actual proper/open compact support on the ambient ordinary derived system category.
Source: node proof step 2 (blueprint: def-coef-finite-adjunction-system-data). -/
def Support.functor {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (s : Support l E c SX SZ SY) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y :=
  s.extension.mapDerivedCategory ⋙ s.properGeometry.image.direct

/-- Exact derived open adjunction, with the ordinary adjunction's cochain normalization.
Source: node proof step 1 (blueprint: def-coef-finite-adjunction-system-data). -/
def Support.openAdj {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (s : Support l E c SX SZ SY) :
    s.extension.mapDerivedCategory ⊣ integralComparisonDerivedSequencePullback l E c.i :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction s.openAdjunction

/-- The proper comparison is the unique counit-compatible comparison of right adjoints.
Source: Stacks 07A6 (blueprint: def-coef-finite-adjunction-system-data). -/
def Support.properComparison {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (s : Support l E c SX SZ SY) :
    s.properGeometry.image.direct ≅ s.finiteProper.direct :=
  (s.properGeometry.adjunction l E).rightAdjointUniq
    (s.finiteProper.adj.ofNatIsoLeft s.properGeometry.pullTransport.symm)

/-- Open comparison is fixed by the two localized ordinary adjunctions.
Source: Stacks 03DI (blueprint: def-coef-finite-adjunction-system-data). -/
def Support.openComparison {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (s : Support l E c SX SZ SY) :
    s.extension.mapDerivedCategory ≅ s.finiteOpen.derived :=
  s.openAdj.leftAdjointUniq
    (s.finiteOpen.adj.ofNatIsoRight s.openGeometry.pullTransport.symm)

/-- Actual compact-support evaluation, assembled from the normalized proper/open factors.
Source: Stacks 0941, 0F7J (blueprint: def-coef-finite-adjunction-system-data). -/
def Support.evaluation {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (s : Support l E c SX SZ SY) (n : ℕ) :
    s.functor ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙
        sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ s.properComparison ≪≫
        Functor.isoWhiskerRight s.openComparison _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (s.finiteProperEvaluation.evaluation n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (s.finiteOpenEvaluation.evaluation n) _ ≪≫
    Functor.associator _ _ _

/-- The open tensor arrow is the transpose of inverse-image tensor and the open unit.
Source: node proof steps 12 and 14
(blueprint: def-coef-finite-adjunction-system-data). -/
def Support.openTensor {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (s : Support l E c SX SZ SY)
    (M : coefficientSequenceDerived l E X) (P : coefficientSequenceDerived l E c.Z) :
    s.extension.mapDerivedCategory.obj
      (SX.systemClosed.tensor.obj
        (M, (integralComparisonDerivedSequencePullback l E c.i).obj P)) ⟶
      SZ.systemClosed.tensor.obj (s.extension.mapDerivedCategory.obj M, P) :=
  (s.openAdj.homEquiv _ _).symm
    (SX.systemClosed.tensor.map (Prod.mkHom (s.openAdj.unit.app M) (𝟙 _)) ≫
      s.openGeometry.tensor.inv.app (s.extension.mapDerivedCategory.obj M, P))

/-- The actual compact-support projection: proper counit projection, inverse open tensor,
and the canonical pullback compositor. It is defined before finite evaluation.
Source: node proof steps 12 and 14
(blueprint: def-coef-finite-adjunction-system-data). -/
def Support.projection {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (s : Support l E c SX SZ SY)
    (M : coefficientSequenceDerived l E X) (P : coefficientSequenceDerived l E Y) :
    SY.systemClosed.tensor.obj (s.functor.obj M, P) ⟶
      s.functor.obj (SX.systemClosed.tensor.obj
        (M, (integralComparisonDerivedSequencePullback l E f).obj P)) :=
  letI : IsIso (s.openTensor M
      ((integralComparisonDerivedSequencePullback l E c.g).obj P)) :=
    s.openTensorInvertible M ((integralComparisonDerivedSequencePullback l E c.g).obj P)
  s.properGeometry.projection l E (s.extension.mapDerivedCategory.obj M) P ≫
    s.properGeometry.image.direct.map
      (inv (s.openTensor M ((integralComparisonDerivedSequencePullback l E c.g).obj P))) ≫
    s.functor.map (SX.systemClosed.tensor.map
      (Prod.mkHom (𝟙 _) (((integralComparisonSystemComposition l E c.i c.g).symm ≪≫
        eqToIso (congrArg (integralComparisonDerivedSequencePullback l E) c.comm.symm)).hom.app P)))

variable (l E)

/-- Equality required to identify the two presentations of canonical scalar restriction.
It is proof data of a realization, not an additional postponed theorem.
Source: Stacks 03DA, 06YY (blueprint: def-coef-finite-adjunction-system-data). -/
def QuotientRestriction (W : Scheme.{u}) : Prop :=
  ∀ {m n : ℕ} (h : n ≤ m),
    pbcDerivedRestrict ((PurCompactSupport.finiteQuotientChange l E
      (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1)).map W) = normalizedDVRRes l E W h

/-- The actual quotient-transition adjunct, in the finite-Tor full subcategory.
It uses the quotient/restriction adjunction and the system's own transition.
Source: node proof step 7 (blueprint: def-coef-finite-adjunction-system-data). -/
def transition (W : Scheme.{u}) (q : QuotientRestriction l E W) {m n : ℕ} (h : n ≤ m)
    (M : (domain l E W).FullSubcategory) :
    (FiniteExceptional.Q l E W h).obj ((evaluation l E W m).obj M) ⟶
      (evaluation l E W n).obj M :=
  ObjectProperty.homMk
    (((pbcDerivedScalarAdjunction ((PurCompactSupport.finiteQuotientChange l E
      (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1)).map W)).homEquiv _ _).symm
        ((coefficientSequenceDerivedTransition l E W h).app M.obj ≫
          (eqToIso (q h)).inv.app
            ((coefficientSequenceDerivedEvaluation l E W n).obj M.obj)))

/-- Signed tensor symmetry on the existing derived closed structure.
The theorem below supplies it with the simultaneous K-flat normalization.
Source: Stacks 06YN, 08J9
(blueprint: def-coef-finite-adjunction-system-data). -/
def swap {W : Scheme.{u}} (S : CoefficientDerivedSystemCalculus l E W)
    (β : @SymmetricCategory (coefficientSequenceDerived l E W) _ S.systemClosed.monoidal)
    (M N : coefficientSequenceDerived l E W) :
    S.systemClosed.tensor.obj (M, N) ≅ S.systemClosed.tensor.obj (N, M) :=
  β.toBraidedCategory.braiding M N

variable {l E}

/-- Left-oriented compact-support projection, formed using the signed system symmetry.
Source: node proof steps 12--15
(blueprint: def-coef-finite-adjunction-system-data). -/
def Support.leftProjection {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (s : Support l E c SX SZ SY)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (P : coefficientSequenceDerived l E Y) (M : coefficientSequenceDerived l E X) :
    SY.systemClosed.tensor.obj (P, s.functor.obj M) ⟶
      s.functor.obj (SX.systemClosed.tensor.obj
        ((integralComparisonDerivedSequencePullback l E f).obj P, M)) :=
  (swap l E SY βY P (s.functor.obj M)).hom ≫ s.projection M P ≫
    s.functor.map ((swap l E SX βX M
      ((integralComparisonDerivedSequencePullback l E f).obj P)).hom)

variable (l E)
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- Functorial finite operations on the full normalized subcategories, with actual units,
counits, finite operations and scalar-extension transition squares. The ambient support
realization and the normalized right adjoint are data of this conclusion.
Source: node proof steps 2--8 (blueprint: def-coef-finite-adjunction-system-data). -/
structure Realization
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SZ : CoefficientDerivedSystemCalculus l E c.Z)
    (SY : CoefficientDerivedSystemCalculus l E Y) where
  support : Support l E c SX SZ SY
  quotientRestrictionX : QuotientRestriction l E X
  quotientRestrictionY : QuotientRestriction l E Y
  F : (domain l E X).FullSubcategory ⥤ (domain l E Y).FullSubcategory
  G : (domain l E Y).FullSubcategory ⥤ (domain l E X).FullSubcategory
  adjunction : F ⊣ G
  /-- F is this proper/open system functor, on all derived arrows. -/
  supportIso : F ⋙ (domain l E Y).ι ≅ (domain l E X).ι ⋙ support.functor
  supportEvaluation : ∀ n : ℕ,
    F ⋙ evaluation l E Y n ≅ evaluation l E X n ⋙ FiniteExceptional.F l E D hl f c n
  /-- The finite support comparison is this actual proper/open evaluation. -/
  supportEvaluation_canonical : ∀ (n : ℕ) (M : (domain l E X).FullSubcategory),
    ((supportEvaluation n).hom.app M).hom =
      (coefficientSequenceDerivedEvaluation l E Y n).map (supportIso.hom.app M) ≫
        (support.evaluation n).hom.app M.obj
  exceptionalEvaluation : ∀ n : ℕ,
    G ⋙ evaluation l E X n ≅ evaluation l E Y n ⋙ FiniteExceptional.G l E D hl f c n
  /-- Exact finite adjunction, including the evaluated exceptional counit. -/
  counit : ∀ (n : ℕ) (N : (domain l E Y).FullSubcategory),
    (supportEvaluation n).hom.app (G.obj N) ≫
      (FiniteExceptional.F l E D hl f c n).map ((exceptionalEvaluation n).hom.app N) ≫
      (FiniteExceptional.adjunction l E D hl f c n).counit.app ((evaluation l E Y n).obj N) =
        (evaluation l E Y n).map (adjunction.counit.app N)
  /-- The system unit is the unit of that same finite adjunction. -/
  unit : ∀ (n : ℕ) (M : (domain l E X).FullSubcategory),
    (evaluation l E X n).map (adjunction.unit.app M) ≫
      (exceptionalEvaluation n).hom.app (F.obj M) ≫
      (FiniteExceptional.G l E D hl f c n).map ((supportEvaluation n).hom.app M) =
        (FiniteExceptional.adjunction l E D hl f c n).unit.app ((evaluation l E X n).obj M)

  /-- The compact-support quotient square uses the recorded finite coefficient map. -/
  supportTransition : ∀ {m n : ℕ} (h : n ≤ m) (M : (domain l E X).FullSubcategory),
    transition l E Y quotientRestrictionY h (F.obj M) ≫ (supportEvaluation n).hom.app M =
      (FiniteExceptional.Q l E Y h).map ((supportEvaluation m).hom.app M) ≫
        (FiniteExceptional.q l E D hl f c h).hom.app ((evaluation l E X m).obj M) ≫
        (FiniteExceptional.F l E D hl f c n).map (transition l E X quotientRestrictionX h M)
  /-- The exceptional quotient square is the mate of that very coefficient map. -/
  exceptionalTransition : ∀ {m n : ℕ} (h : n ≤ m) (N : (domain l E Y).FullSubcategory),
    transition l E X quotientRestrictionX h (G.obj N) ≫ (exceptionalEvaluation n).hom.app N =
      (FiniteExceptional.Q l E X h).map ((exceptionalEvaluation m).hom.app N) ≫
        (FiniteExceptional.b l E D hl f c h).app ((evaluation l E Y m).obj N) ≫
        (FiniteExceptional.G l E D hl f c n).map (transition l E Y quotientRestrictionY h N)

variable {l E D hl f c}

/-- Termwise ordinary sections of a strict coefficient system, retaining its tower.
Source: Stacks 0941 (blueprint: def-coef-finite-adjunction-system-data). -/
abbrev sections (W : Scheme.{u}) :=
  coefficientSequenceRestriction l E W ⋙ coefficientTowerSections l E W

/-- The existing derived termwise global sections used by H_W.
Source: Stacks 0941 (blueprint: def-coef-finite-adjunction-system-data). -/
def derivedSections (W : Scheme.{u}) :=
  coefficientSequenceDerivedRestriction l E W ⋙ (coefficientTowerSections l E W).rightDerivedFunctor

/-- The universal sections unit, expressed using the exact restriction factorization.
This formula fixes the representative map on every complex, not only its fibers.
Source: Stacks 079P, 0941
(blueprint: def-coef-finite-adjunction-system-data). -/
def sectionsUnitComponent (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    DerivedCategory.Q.obj (((sections (l := l) (E := E) W).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (derivedSections (l := l) (E := E) W).obj (DerivedCategory.Q.obj C) :=
  let RC := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) |>.obj C
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((coefficientTowerSections l E W).mapHomologicalComplex (.up ℤ)).obj RC) ≫
    (coefficientTowerSections l E W).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj RC) ≫
    (coefficientTowerSections l E W).rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app RC) ≫
    (coefficientTowerSections l E W).rightDerivedFunctor.map
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C)

set_option linter.defProp false in
/-- Transport of the published restriction/evaluation object equality to sections.
Source: Stacks 03DA, 0941 (blueprint: def-coef-finite-adjunction-system-data). -/
def restrictionSections (W : Scheme.{u}) (M : coefficientSequenceModules l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) :
    (((coefficientSequenceRestriction l E W).obj M).obj (op n)).val.presheaf.obj U =
      M.val.presheaf.obj (op (n, U.unop)) :=
  congrArg (fun T : scalarReductionSource l E W ↦ T.val.presheaf.obj U)
    ((coefficientSequenceRestriction_exists l E W).exists.choose_spec.1 M n)

/-- Read a global module section as its actual section on the sequence site.
Source: Stacks 03DA, 0941
(blueprint: def-coef-finite-adjunction-system-data). -/
def sectionAt (W : Scheme.{u}) (M : coefficientSequenceModules l E W) (n : ℕ)
    (U : W.ProEtᵒᵖ) (h : ((sections W).obj M).obj (op n)) :
    M.val.obj (op (n, U.unop)) :=
  (eqToHom (restrictionSections W M n U))
    ((h.val.app U) (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U))

/-- Derived sections comparison for the actual sectionwise geometric direct image.
The ordinary equation fixes sections by restriction from the terminal object; the
cochain equation derives that very map with the universal units.
Source: Stacks 03D2, 07A4, 0941; node proof step 15
(blueprint: def-coef-finite-adjunction-system-data). -/
structure SectionsPush {X Y : Scheme.{u}} {f : X ⟶ Y}
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SY : CoefficientDerivedSystemCalculus l E Y} (g : Geometry l E f SX SY) where
  ordinary : integralComparisonSequenceDirectImage l E f ⋙ sections Y ≅ sections X
  ordinary_sections : ∀ (M : coefficientSequenceModules l E X) (n : ℕ)
    (h : ((sections Y).obj ((integralComparisonSequenceDirectImage l E f).obj M)).obj (op n))
    (U : X.ProEt) (a : U ⟶ (proEtaleBaseChange f).obj (Scheme.ProEt.mk (𝟙 Y))),
    sectionAt X M n (op U) (((ordinary.hom.app M).app (op n)) h) =
      (M.val.map (Prod.mkHom (𝟙 n) a).op)
        (sectionAt Y ((integralComparisonSequenceDirectImage l E f).obj M) n
          (op (Scheme.ProEt.mk (𝟙 Y))) h)
  comparison : g.image.direct ⋙ derivedSections Y ≅ derivedSections X
  model : ∀ C : CochainComplex (coefficientSequenceModules l E X) ℤ,
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex ordinary.hom (.up ℤ)).app C) ≫
        sectionsUnitComponent X C =
      sectionsUnitComponent Y
          (((integralComparisonSequenceDirectImage l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (derivedSections Y).map (g.image.directUnit.app C) ≫
        comparison.hom.app (DerivedCategory.Q.obj C)

/-- The ambient compact-support counit is the normalized counit through the support
realization, so its evaluated counit is fixed by `Realization.counit`.
Source: node proof steps 8 and 15
(blueprint: def-coef-finite-adjunction-system-data). -/
def Realization.ambientCounit
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (r : Realization l E D hl f c SX SZ SY)
    (N : (domain l E Y).FullSubcategory) :
    r.support.functor.obj (r.G.obj N).obj ⟶ N.obj :=
  r.supportIso.inv.app (r.G.obj N) ≫ (r.adjunction.counit.app N).hom

/-- The internal enriched map, defined before evaluation or inverse limit.
It is the tensor-Hom transpose of the geometric projection, geometric counit,
internal evaluation, and exceptional counit, in that order.
Source: node proof step 15; Stacks 08J9
(blueprint: def-coef-finite-adjunction-system-data). -/
def Realization.enrichedMap
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (r : Realization l E D hl f c SX SZ SY)
    (g : Geometry l E f SX SY)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (M : (domain l E X).FullSubcategory) (N : (domain l E Y).FullSubcategory) :
    g.image.direct.obj ((coefficientSequenceInternalHom l E X).obj (op M.obj, (r.G.obj N).obj)) ⟶
      (coefficientSequenceInternalHom l E Y).obj (op (r.F.obj M).obj, N.obj) :=
  let H := (coefficientSequenceInternalHom l E X).obj (op M.obj, (r.G.obj N).obj)
  SY.systemClosed.transpose _ _ _
    (SY.systemClosed.tensor.map (Prod.mkHom (𝟙 _) (r.supportIso.hom.app M)) ≫
      r.support.leftProjection βX βY (g.image.direct.obj H) M.obj ≫
      r.support.functor.map
        (SX.systemClosed.tensor.map (Prod.mkHom ((g.adjunction l E).counit.app H) (𝟙 _))) ≫
      r.support.functor.map (SX.systemClosed.evaluation M.obj (r.G.obj N).obj) ≫
      r.ambientCounit N)

/-- The pre-limit global enriched map is derived sections of the inverse internal
transpose followed by the sections/direct-image comparison. Both arrows have their
ordinary and simultaneous-resolution normalizations above.
Source: node proof step 15
(blueprint: def-coef-finite-adjunction-system-data). -/
def Realization.globalMap
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y} (r : Realization l E D hl f c SX SZ SY)
    (g : Geometry l E f SX SY) (s : SectionsPush g)
    (βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal)
    (βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal)
    (M : (domain l E X).FullSubcategory) (N : (domain l E Y).FullSubcategory)
    (h : IsIso (r.enrichedMap g βX βY M N)) :
    (coefficientSequenceGlobalHom l E Y).obj (op (r.F.obj M).obj, N.obj) ⟶
      (coefficientSequenceGlobalHom l E X).obj (op M.obj, (r.G.obj N).obj) :=
  letI := h
  (derivedSections Y).map (inv (r.enrichedMap g βX βY M N)) ≫
    s.comparison.hom.app ((coefficientSequenceInternalHom l E X).obj (op M.obj, (r.G.obj N).obj))


end WeilConjectures.FiniteAdjunctionDiagram
