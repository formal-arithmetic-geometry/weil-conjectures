/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefSupportOpenTensorModel
public import WeilConjectures.SixFunctors.CoefHomTowerScalarModel
public import WeilConjectures.SixFunctors.CoefficientProjectionPointData
public import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal

/-! # Data for projection and evaluation on coefficient systems

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2;
Stacks 07A4, 07A6, 08J9, 0D6D, 0B56
(blueprint: def-sf-coef-projection-evaluation-data).
-/

@[expose] public noncomputable section
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u a b v w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.CoefProjectionEvaluation

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing signed system tensor-Hom model with its universal localization.
The compatibility equation retains precisely the recorded K-flat comparison.
Source: Stacks 06YT, 08J9, 0FPT
(blueprint: def-sf-coef-projection-evaluation-data). -/
structure SystemTensor (W : Scheme.{u}) where
  data : CoefficientDerivedSystemTensors.{u, u} l E W
  localization : TensorLocalization data.systemClosed.tensor
  compatibility : ∀ P Q hP hQ,
    (data.systemTensorModel.iso _ _ _ P Q hP hQ).hom ≫
      localization.comparison.app (P, Q) = 𝟙 _
  symmetry : @SymmetricCategory (coefficientSequenceDerived.{u, u} l E W)
    _ data.systemClosed.monoidal
  signed : RingedDerivedTensorSymmetryModel
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)
    data.systemClosed data.systemTensorModel symmetry

/-- Simultaneous canonical adjunction and tensor data on the specified sequence sites.
All witnesses are conclusions of projectionEvaluation; no flatness or finite-Tor
hypothesis is hidden in the inputs. Ordinary right functors, their scalar actions,
local pure tensors, derived units and open gamma are prescribed.
Source: Stacks 07A4, 07A6, 0B56, 0D6D, 08J9
(blueprint: def-sf-coef-projection-evaluation-data). -/
structure Model {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) where
  point : PointTensor l E
  pointSymmetry : PointSymmetry l E point
  x : SystemTensor l E X
  y : SystemTensor l E Y
  z : SystemTensor l E c.Z
  xLax : SectionsTensor l E X
  yLax : SectionsTensor l E Y
  pLax : PushTensor l E c.g
  rLax : RestrictionTensor l E
  gx : AdjointLocalization (coefHomQuotientSections l E X)
    (coefHomQuotientDerivedSections l E X) (rightUnit (coefHomQuotientSections l E X))
  gy : AdjointLocalization (coefHomQuotientSections l E Y)
    (coefHomQuotientDerivedSections l E Y) (rightUnit (coefHomQuotientSections l E Y))
  p : AdjointLocalization
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g)
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g)
    (rightUnit (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g))
  r : AdjointLocalization (coefHomPointRestriction l E)
    (coefHomPointDerivedRestriction l E) (restrictionUnit l E)
  gxTensor : TensorAdjunction point.qTensor x.data.systemClosed.tensor
    point.quotientLocalization x.localization
    (coefHomQuotientSections l E X) (coefHomQuotientDerivedSections l E X)
    (rightUnit (coefHomQuotientSections l E X)) xLax.map gx
  gyTensor : TensorAdjunction point.qTensor y.data.systemClosed.tensor
    point.quotientLocalization y.localization
    (coefHomQuotientSections l E Y) (coefHomQuotientDerivedSections l E Y)
    (rightUnit (coefHomQuotientSections l E Y)) yLax.map gy
  pTensor : @TensorAdjunction
    (coefficientSequenceModules.{u, u} l E Y) _ _ _ _ _ _
    (coefficientSequenceModules.{u, u} l E c.Z) _ _ _ _ _ _
    y.data.systemClosed.tensor z.data.systemClosed.tensor y.localization z.localization
    (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g) (systemPushAdditive l E c.g)
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g)
    (rightUnit (ProEtale.VaryingRing.push (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g)) pLax.map p
  rTensor : TensorAdjunction point.rTensor point.qTensor
    point.integralLocalization point.quotientLocalization
    (coefHomPointRestriction l E) (coefHomPointDerivedRestriction l E)
    (restrictionUnit l E) rLax.map r
  composition : SectionsComposition l E a
  openTensor : CoefSupportOpenTensor.SystemOpenModel l E c.i x.data z.data

namespace Model
variable {l E} {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
  (m : Model l E c)

/-- Actual quotient compact support: exact open extension, then derived proper image.
Source: Stacks 0941 (blueprint: def-sf-coef-projection-evaluation-data). -/
abbrev support (_m : Model l E c) :
    coefficientSequenceDerived.{u, u} l E X ⥤ coefficientSequenceDerived.{u, u} l E Y :=
  CoefSupportOpenTensor.operation l E c

/-- Actual quotient point sections, retaining the tower and quotient scalars.
Source: Stacks 0941 (blueprint: def-sf-coef-projection-evaluation-data). -/
abbrev sections := coefHomQuotientDerivedSections l E Y

/-- Internal Hom on the whole quotient sequence site.
Source: Stacks 08J9 (blueprint: def-sf-coef-projection-evaluation-data). -/
abbrev hom (U N : coefficientSequenceDerived.{u, u} l E X) :=
  (coefficientSequenceInternalHom l E X).obj (op U, N)

/-- Quotient-linear derived sections of internal Hom, without inverse limit.
Source: Stacks 08J9, 0941 (blueprint: def-sf-coef-projection-evaluation-data). -/
abbrev h (U N : coefficientSequenceDerived.{u, u} l E X) :=
  (coefHomQuotientDerivedSections l E X).obj (hom U N)

/-- Quotient-linear point tower of a compactly supported input.
Source: Stacks 0941 (blueprint: def-sf-coef-projection-evaluation-data). -/
abbrev b (_m : Model l E c) (U : coefficientSequenceDerived.{u, u} l E X) :=
  (coefHomQuotientDerivedSections l E Y).obj ((_m.support).obj U)

/-- Canonical pullback composition, obtained by conjugating the normalized right
composition through the actual derived adjunctions.
Source: Stacks 0D6D (blueprint: def-sf-coef-projection-evaluation-data). -/
def sectionsPullback : m.gy.left ⋙
    ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) a ≅ m.gx.left :=
  Adjunction.leftAdjointCompIso m.gy.adjunction
    (ProEtale.VaryingRing.adj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) a) m.gx.adjunction m.composition.derived

/-- The sections counit after the canonical pullback-composition isomorphism.
Source: Stacks 07A6, 0D6D (blueprint: def-sf-coef-projection-evaluation-data). -/
def t (U N : coefficientSequenceDerived.{u, u} l E X) :
    (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) a).obj (m.gy.left.obj (h U N)) ⟶ hom U N :=
  m.sectionsPullback.hom.app (h U N) ≫ m.gx.adjunction.counit.app (hom U N)

/-- Signed closed evaluation after tensoring the sections counit by U.
Source: Stacks 08J9, 0FPT (blueprint: def-sf-coef-projection-evaluation-data). -/
def v (U N : coefficientSequenceDerived.{u, u} l E X) :
    m.x.data.systemClosed.tensor.obj (U,
      (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) a).obj (m.gy.left.obj (h U N))) ⟶ N :=
  m.x.data.systemClosed.tensor.map (Prod.mkHom (𝟙 U) (m.t U N)) ≫
    (m.x.symmetry.toBraidedCategory.braiding U (hom U N)).hom ≫
    m.x.data.systemClosed.evaluation U N

/-- The canonical tensor pullback for proper image, transported to the recorded
native pullback by the unique adjoint-compatible isomorphism.
Source: Stacks 07A4 (blueprint: def-sf-coef-projection-evaluation-data). -/
def properTensor : m.y.data.systemClosed.tensor ⋙
    ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g ≅
    ((ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).prod
      (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g)) ⋙ m.z.data.systemClosed.tensor :=
  letI := systemPushAdditive l E c.g
  transportTensor _ _ (m.p.adjunction.leftAdjointUniq
    (ProEtale.VaryingRing.adj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g)) m.pTensor.comparison

/-- Pullback composition across the fixed compactification, with its actual factorization.
Source: Stacks 0D6D (blueprint: def-sf-coef-projection-evaluation-data). -/
def compactificationPullback :
    ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g ⋙
      ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ≅
    ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) a :=
  (ProEtale.VaryingRing.gComp (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i c.g).symm ≪≫
    eqToIso (congrArg
      (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E)) c.comm.symm)

/-- The specified support projection word: proper projection mate, actual open gamma,
then the pullback-composition comparison. Neither projection mate is inverted.
Source: Stacks 0B56, 0E8I, 0D6D
(blueprint: def-sf-coef-projection-evaluation-data). -/
def Pi (U : coefficientSequenceDerived.{u, u} l E X)
    (L : coefficientSequenceDerived.{u, u} l E Y) :
    m.y.data.systemClosed.tensor.obj (m.support.obj U, L) ⟶
      m.support.obj (m.x.data.systemClosed.tensor.obj (U,
        (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) a).obj L)) :=
  derivedProjectionFormulaMate
    (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g)
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g)
    (ProEtale.VaryingRing.adj (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g)
    m.y.data.systemClosed.tensor m.z.data.systemClosed.tensor m.properTensor
    ((ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i).obj U) L ≫
    (ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g).map
      ((CoefSupportOpenTensor.systemGamma l E c.i m.x.data m.z.data m.openTensor).hom.app
        (U, (ProEtale.VaryingRing.G (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g).obj L) ≫
        (ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.i).map
            (m.x.data.systemClosed.tensor.map
              (Prod.mkHom (𝟙 U) ((compactificationPullback (l := l) (E := E) (c := c)).hom.app L))))

/-- The quotient-linear evaluation pairing before scalar balancing or inverse limit.
Source: Stacks 0B56, 08J9 (blueprint: def-sf-coef-projection-evaluation-data). -/
def q (U N : coefficientSequenceDerived.{u, u} l E X) :
    m.point.qTensor.obj (m.b U, h U N) ⟶ m.b N :=
  projection m.gyTensor (m.support.obj U) (h U N) ≫
    (coefHomQuotientDerivedSections l E Y).map
      (m.Pi U (m.gy.left.obj (h U N)) ≫ m.support.map (m.v U N))

/-- The scalar balancing composite: the restriction projection mate followed by
restriction of one tensor the scalar-extension counit.
Source: Stacks 0B56, 07A6 (blueprint: def-sf-coef-projection-evaluation-data). -/
def balance (H B : DerivedCategory (coefHomQuotientPointModules.{u, u} l E)) :
    m.point.rTensor.obj ((coefHomPointDerivedRestriction l E).obj H,
      (coefHomPointDerivedRestriction l E).obj B) ⟶
    (coefHomPointDerivedRestriction l E).obj (m.point.qTensor.obj (H, B)) :=
  projection m.rTensor H ((coefHomPointDerivedRestriction l E).obj B) ≫
    (coefHomPointDerivedRestriction l E).map
      (m.point.qTensor.map (Prod.mkHom (𝟙 H) (m.r.adjunction.counit.app B)))

/-- The entire representative-independent derived system word, with the required
order of factors: scalar balance, signed point symmetry, and quotient evaluation.
Source: blueprint paragraph 2; Stacks 0B56, 08J9
(blueprint: def-sf-coef-projection-evaluation-data). -/
def beta (U N : coefficientSequenceDerived.{u, u} l E X) :
    m.point.rTensor.obj ((coefHomPointDerivedRestriction l E).obj (h U N),
      (coefHomPointDerivedRestriction l E).obj (m.b U)) ⟶
    (coefHomPointDerivedRestriction l E).obj (m.b N) :=
  m.balance (h U N) (m.b U) ≫ (coefHomPointDerivedRestriction l E).map
    ((m.pointSymmetry.symmetry.toBraidedCategory.braiding (h U N) (m.b U)).hom ≫ m.q U N)

end Model
/-- Compatibility with the recorded compact-support point-sections presentation.
Both ordinary sides keep precisely the same sections and integral action. The
unit equation fixes the whole-derived comparison, before any coefficient evaluation.
Source: Stacks 0D6E, 0941 (blueprint: def-sf-coef-projection-evaluation-data). -/
structure SupportSections (W : Scheme.{u}) where
  ordinary : coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E ≅
    CoefSupportOpenTensor.ordinaryQuotientSections l E W
  sections : ∀ (M : coefficientSequenceModules.{u, u} l E W) (n : ℕ)
    (x : (((coefHomQuotientSections l E W ⋙ coefHomPointRestriction l E).obj M).obj
      (op n))), HEq (((ordinary.hom.app M).app (op n)) x) x
  comparison : coefHomRestrictedQuotientSections l E W ≅
    CoefSupportOpenTensor.quotientSections l E W
  normalization : DerivedCompositionNormalization
    (coefHomQuotientSections l E W) (coefHomPointRestriction l E)
    (CoefSupportOpenTensor.ordinaryQuotientSections l E W)
    (coefHomQuotientDerivedSections l E W) (coefHomPointDerivedRestriction l E)
    (CoefSupportOpenTensor.quotientSections l E W)
    (rightUnit (coefHomQuotientSections l E W)) (restrictionUnit l E)
    (rightUnit (CoefSupportOpenTensor.ordinaryQuotientSections l E W)) ordinary comparison
  pointModel : CoefSupportOpenTensor.SectionsModel l E W

/-- The scalar specialization, retaining the Hom comparison's prescribed inverse,
its scalar-adjunction normalization, and the actual simultaneous reduction model.
Source: blueprint paragraph 2; Stacks 07A6, 08J9, 0941
(blueprint: def-sf-coef-projection-evaluation-data). -/
structure ScalarSpecialization {X Y : Scheme.{u}} {a : X ⟶ Y}
    {c : Compactification a} (m : Model l E c) where
  supportSections : SupportSections l E Y
  scalar : ScalarHomModels.{u + 1, u, u, u + 2}
    (coefficientSequenceTopology (ProEt.topology X))
  tensor : ∀ {R T : Sheaf (coefficientSequenceTopology (ProEt.topology X))
    CommRingCat.{u + 1}} (a : R ⟶ T), ScalarHomTensorComparison.{u + 1, u, u, u + 2} scalar a
  homAdjunction : ScalarInternalHomAdjunction.{u + 1, u, u, u + 2} scalar tensor
  comparison : coefHomTower l E X ≅ coefHomScalarTower l E X scalar
  normalization : ∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (N : coefficientSequenceDerived.{u, u} l E X),
    comparison.inv.app (op K, N) =
      (coefHomDerivedFactorization l E X).hom.app
        ((coefficientSequenceInternalHom l E X).obj
          (op ((scalar.scalar (coefHomScalarMap l E X)).derived.obj
            ((coefHomDerivedConstant l E X).obj K)), N)) ≫
      (coefHomConstantDerivedSections l E X).map
        ((homAdjunction.iso (coefHomScalarMap l E X)).hom.app
          (op ((coefHomDerivedConstant l E X).obj K), N))
  reductionEvaluation : ∀ n : ℕ,
    coefHomDerivedConstant l E X ⋙ (scalar.scalar (coefHomScalarMap l E X)).derived ⋙
      coefficientSequenceDerivedEvaluation l E X n ≅ coefficientFiniteDerivedExtension l E X n
  reductionModel : CoefficientReductionModels l E X
    (coefHomDerivedConstant l E X ⋙ (scalar.scalar (coefHomScalarMap l E X)).derived)
    reductionEvaluation

namespace ScalarSpecialization
variable {l E} {X Y : Scheme.{u}} {a : X ⟶ Y} {c : Compactification a}
  {m : Model l E c} (s : ScalarSpecialization l E m)

/-- M is derived scalar extension of the actual constant completed-coefficient system.
Its finite evaluations and quotient transitions are fixed by reductionModel.
Source: Stacks 06YY, 0941 (blueprint: def-sf-coef-projection-evaluation-data). -/
abbrev reduced (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
  (s.scalar.scalar (coefHomScalarMap l E X)).derived.obj
    ((coefHomDerivedConstant l E X).obj K)

/-- The compact-support R-linear point tower B_K, before inverse limit.
It uses the native compact-support composite on the actual reduction system.
Source: blueprint paragraph 2; Stacks 0941
(blueprint: def-sf-coef-projection-evaluation-data). -/
abbrev supportTower (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :=
  (coefHomPointDerivedRestriction l E).obj (m.b (reduced s K))

/-- The compact-support point comparison identifies B_K with sections of the
native completed-coefficient compact-support reduction tower, on the whole category.
Source: Stacks 0D6E, 0941 (blueprint: def-sf-coef-projection-evaluation-data). -/
def supportComparison :
    (coefHomDerivedConstant l E X ⋙ (s.scalar.scalar (coefHomScalarMap l E X)).derived) ⋙
      m.support ⋙ coefHomRestrictedQuotientSections l E Y ≅
    (coefHomDerivedConstant l E X ⋙ (s.scalar.scalar (coefHomScalarMap l E X)).derived) ⋙
      m.support ⋙ coefficientSequenceDerivedRestriction l E Y ⋙
        CoefSupportOpenTensor.integralSections l E Y :=
  Functor.isoWhiskerLeft
    ((coefHomDerivedConstant l E X ⋙ (s.scalar.scalar (coefHomScalarMap l E X)).derived) ⋙
      m.support)
    (s.supportSections.comparison ≪≫ s.supportSections.pointModel.comparison)

/-- Transport of the system pairing by the normalized Hom isomorphism, with the
native compact-support realization. The factor order and scalar balance are unchanged.
Source: blueprint paragraph 2; Stacks 08J9, 0B56
(blueprint: def-sf-coef-projection-evaluation-data). -/
def transported (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (N : coefficientSequenceDerived.{u, u} l E X) :
    m.point.rTensor.obj ((coefHomTower l E X).obj (op K, N), supportTower s K) ⟶
      (coefHomPointDerivedRestriction l E).obj (m.b N) :=
  m.point.rTensor.map (Prod.mkHom (s.comparison.hom.app (op K, N)) (𝟙 _)) ≫
    m.beta (reduced s K) N

end ScalarSpecialization

end WeilConjectures.CoefProjectionEvaluation
