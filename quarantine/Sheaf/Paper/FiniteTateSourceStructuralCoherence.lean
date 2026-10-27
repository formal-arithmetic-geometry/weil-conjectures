/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.PurityTateDatum
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.SixFunctors.SchemeGeometricFrobenius
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteTensorReductionData
public import Sheaf.Paper.FiniteTensorSignedReduction
public import Sheaf.Paper.FiniteSignedTwistProducts
public import Sheaf.Paper.FinitePositiveRootCharts
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.FiniteTensorFixedComparisons
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.CartesianCoefficientTwists
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.FiniteDerivedComparisonNormalization
import Sheaf.Algebra.Homology.TotalTensorSignedCoherence
import Sheaf.Paper.AmbientPullbackTensorCoherence
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence
import Sheaf.Paper.PullbackTensorCanonicalShiftUnit

/-! # Coherence of the finite Tate-source structural comparison

Source: latest blueprint, def-pur-tate-datum, first arrow of the displayed source datum;
prop-pur-weil-equivariance-compatibilities, constituent-compatibility assembly.
(blueprint: lem-pur-finite-tate-source-structural-coherence).

The equations use the fixed-scalar realization of the small pro-etale derived category.
All tensorators, scalar mates, compositors and line comparisons are the published maps.
The root chart in geometric transport describes the canonical pullback of a positive line.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.defProp false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting.FiniteTateSource

/-- Fixed-scalar coordinates of the existing pro-etale derived category.
Source: def-pur-tate-datum (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
abbrev D (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))

/-- The hypotheses on one smooth morphism and its two finite-field models.
Source: the finite Tate source (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
structure Model (P : PurityFiniteSetting.{u}) (d : ℕ) where
  X₀ : Over (Spec (.of P.field.k₀))
  Y₀ : Over (Spec (.of P.field.k₀))
  f₀ : X₀ ⟶ Y₀
  [finiteX : LocallyOfFiniteType X₀.hom]
  [compactX : QuasiCompact X₀.hom]
  [separatedX : IsSeparated X₀.hom]
  [finiteY : LocallyOfFiniteType Y₀.hom]
  [compactY : QuasiCompact Y₀.hom]
  [separatedY : IsSeparated Y₀.hom]
  [finiteMap : LocallyOfFiniteType f₀.left]
  [compactMap : QuasiCompact f₀.left]
  [separatedMap : IsSeparated f₀.left]
  [smooth : SmoothOfRelativeDimension d (P.frobeniusMap f₀)]

attribute [instance] Model.finiteX Model.compactX Model.separatedX Model.finiteY
  Model.compactY Model.separatedY Model.finiteMap Model.compactMap Model.separatedMap
  Model.smooth

/-- Geometric source. Source: def-pur-scheme-geometric-frobenius
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
abbrev Model.X {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) :=
  (P.frobeniusFiber M.X₀).left

/-- Geometric target. Source: def-pur-scheme-geometric-frobenius
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
abbrev Model.Y {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) :=
  (P.frobeniusFiber M.Y₀).left

/-- The actual geometric pullback. Source: def-weil-derived-pullback-tensor-hom
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
abbrev Model.F {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) :=
  P.smoothPurityPullback (P.frobeniusMap M.f₀)

/-- Geometric Frobenius on the source. Source: def-pur-scheme-geometric-frobenius
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
abbrev Model.GX {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) :=
  P.smoothPurityPullback (P.frobeniusGaloisMap M.X₀)

/-- Geometric Frobenius on the target. Source: def-pur-scheme-geometric-frobenius
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
abbrev Model.GY {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) :=
  P.smoothPurityPullback (P.frobeniusGaloisMap M.Y₀)

/-- Comparison of equal paths, made from the two prescribed compositors.
Source: Stacks 0D6D (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def square (P : PurityFiniteSetting.{u}) {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (w : u ≫ f = f' ≫ v) (K : D P Y) :
    (P.smoothPurityPullback u).obj ((P.smoothPurityPullback f).obj K) ≅
      (P.smoothPurityPullback f').obj ((P.smoothPurityPullback v).obj K) :=
  ((compositionFixedPullbackComp P.Ring u f).app K).symm ≪≫
    eqToIso (congrArg (fun h ↦ (P.smoothPurityPullback h).obj K) w) ≪≫
    (compositionFixedPullbackComp P.Ring f' v).app K

/-- The commuting-pullback comparison c_f, with the orientation in the node.
Source: def-pur-tate-datum (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Model.c {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) (K : D P M.Y) :
    M.GX.obj (M.F.obj K) ≅ M.F.obj (M.GY.obj K) :=
  square P (P.frobeniusGaloisMap M.X₀) (P.frobeniusMap M.f₀)
    (P.frobeniusMap M.f₀) (P.frobeniusGaloisMap M.Y₀)
    (P.field.frobenius_square_cartesian M.X₀ M.Y₀ M.f₀).2.2.2.2.1 K

/-- P_f, with the existing degree-zero positive Tate line and even shift.
Source: def-pur-tate-datum (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Model.source {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) :
    D P M.Y ⥤ D P M.X :=
  M.F ⋙ tensorRight (P.finiteTensorFixedLine M.X d) ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- H_f, before inserting either the Weil datum or the Tate action.
Source: def-pur-tate-datum (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Model.target {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) :
    D P M.Y ⥤ D P M.X :=
  M.GY ⋙ M.F ⋙ tensorRight (M.GX.obj (P.finiteTensorFixedLine M.X d)) ⋙
    shiftFunctor _ (2 * (d : ℤ))

/-- The termwise shift comparison on the actual exact pullback presentation.
Source: Stacks 0D6D (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
instance pullbackCommShift (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (P.smoothPurityPullback f).CommShift ℤ :=
  inferInstanceAs ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f
    ).mapDerivedCategory.CommShift ℤ)

/-- The specified first arrow b: shift, canonical tensorator, then c_f tensor identity.
Source: displayed first arrow in def-pur-tate-datum
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Model.b {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) (K : D P M.Y) :
    M.GX.obj (M.source.obj K) ≅ M.target.obj K :=
  (M.GX.commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (P.finiteTensorPullbackTensor (P.frobeniusGaloisMap M.X₀)
          (M.F.obj K) (P.finiteTensorFixedLine M.X d) ≪≫
        tensorIso (M.c K) (Iso.refl _))

/-- The same models at a smaller positive quotient level.
Source: finite reduction clause (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Model.reduce {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d)
    (m : ℕ) (hm : 1 ≤ m) : Model (P.finiteReductionSetting m hm) d where
  X₀ := M.X₀
  Y₀ := M.Y₀
  f₀ := M.f₀
  smooth := M.smooth

/-- Constituent comparisons used in the displayed square. This is comparison data,
not a coherence assumption: both constructors below supply the actual canonical maps.
Source: the definitions of a_P and a_H in the node
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
structure Change {P P' : PurityFiniteSetting.{u}} {d : ℕ}
    (M : Model P d) (N : Model P' d) where
  QX : D P M.X ⥤ D P' N.X
  QY : D P M.Y ⥤ D P' N.Y
  q : ∀ U V, QX.obj (U ⊗ V) ≅ QX.obj U ⊗ QX.obj V
  shift : ∀ s : ℤ, shiftFunctor _ s ⋙ QX ≅ QX ⋙ shiftFunctor _ s
  sigma : ∀ K, QX.obj (M.F.obj K) ≅ N.F.obj (QY.obj K)
  CX : ∀ U, QX.obj (M.GX.obj U) ≅ N.GX.obj (QX.obj U)
  CY : ∀ K, QY.obj (M.GY.obj K) ≅ N.GY.obj (QY.obj K)
  t : QX.obj (P.finiteTensorFixedLine M.X d) ≅ P'.finiteTensorFixedLine N.X d

/-- Canonical a_P, assembled in the stated order from q, sigma, t and shift.
Source: displayed square (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Change.aP {P P' : PurityFiniteSetting.{u}} {d : ℕ}
    {M : Model P d} {N : Model P' d} (A : Change M N) (K : D P M.Y) :
    A.QX.obj (M.source.obj K) ≅ N.source.obj (A.QY.obj K) :=
  (A.shift (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (A.q (M.F.obj K) _ ≪≫ tensorIso (A.sigma K) A.t)

/-- Canonical a_H, using C_Y on the input and G'_X(t) C_X on the line factor.
Source: displayed square (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Change.aH {P P' : PurityFiniteSetting.{u}} {d : ℕ}
    {M : Model P d} {N : Model P' d} (A : Change M N) (K : D P M.Y) :
    A.QX.obj (M.target.obj K) ≅ N.target.obj (A.QY.obj K) :=
  (A.shift (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (A.q (M.F.obj (M.GY.obj K)) _ ≪≫
        tensorIso (A.sigma (M.GY.obj K) ≪≫ N.F.mapIso (A.CY K))
          (A.CX _ ≪≫ N.GX.mapIso A.t))

/-- The equality in the node, with its actual independently assembled boundary maps.
Source: displayed square (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Change.Square {P P' : PurityFiniteSetting.{u}} {d : ℕ}
    {M : Model P d} {N : Model P' d} (A : Change M N) (K : D P M.Y) : Prop :=
  A.QX.map (M.b K).hom ≫ (A.aH K).hom =
    (A.CX (M.source.obj K)).hom ≫ N.GX.map (A.aP K).hom ≫ (N.b (A.QY.obj K)).hom

/-- Finite quotient change, retaining the B-action in the derived extension of scalars.
Source: lem-fix-operation-reduction and normalized finite comparisons
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def reductionChange {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d)
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) : Change M (M.reduce m hm) where
  QX := P.finiteTensorReduction m hm hmn M.X
  QY := P.finiteTensorReduction m hm hmn M.Y
  q U V := ((P.finiteTensorCore m hm hmn M.X).μIso U V).symm
  shift := P.finiteTensorScalarShift m hm hmn M.X
  sigma := P.finiteTensorPullbackComparison m hm hmn (P.frobeniusMap M.f₀)
  CX := P.finiteTensorPullbackComparison m hm hmn (P.frobeniusGaloisMap M.X₀)
  CY := P.finiteTensorPullbackComparison m hm hmn (P.frobeniusGaloisMap M.Y₀)
  t := P.finiteTensorLineComparison m hm hmn M.X d

/-- Exact pullback of the unit, using the published left-derived/exact identification.
Source: Stacks 07A4 (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def pullbackUnit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (P.smoothPurityPullback f).obj (𝟙_ (D P Y)) ≅ 𝟙_ (D P X) :=
  ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) f).app _).symm ≪≫
    ProEtale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) f

/-- Canonical positive-line pullback in any common primitive-root chart. The map
pulls the root section back along the k-linear base change, hence uses the same root.
Source: det-prop-sfb-cartesian-coefficients-twists, positive powers
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def linePullback (P : PurityFiniteSetting.{u})
    {X₀ Y₀ : Over (Spec (.of P.field.k₀))} (f₀ : X₀ ⟶ Y₀)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (r : ℕ) :
    (P.smoothPurityPullback (P.frobeniusMap f₀)).obj
        (P.finiteTensorFixedLine (P.frobeniusFiber Y₀).left r) ≅
      P.finiteTensorFixedLine (P.frobeniusFiber X₀).left r :=
  (P.smoothPurityPullback (P.frobeniusMap f₀)).mapIso
      (P.finiteTensorPositiveChart (P.frobeniusFiber Y₀).left ζ hζ r) ≪≫
    pullbackUnit P (P.frobeniusMap f₀) ≪≫
    (P.finiteTensorPositiveChart (P.frobeniusFiber X₀).left ζ hζ r).symm

/-- Base change of the model square, including its canonical commutativity equality.
Source: def-weil-pbc-cartesian-square
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def modelSquare {P : PurityFiniteSetting.{u}} {d : ℕ} (M N : Model P d)
    (u₀ : N.X₀ ⟶ M.X₀) (v₀ : N.Y₀ ⟶ M.Y₀)
    (sq : ChosenCartesianSquare u₀.left N.f₀.left M.f₀.left v₀.left) :
    P.frobeniusMap u₀ ≫ P.frobeniusMap M.f₀ =
      P.frobeniusMap N.f₀ ≫ P.frobeniusMap v₀ := by
  have w : u₀ ≫ M.f₀ = N.f₀ ≫ v₀ := Over.OverMorphism.ext sq.w
  simpa only [Functor.map_comp, Over.comp_left] using
    congrArg (fun a ↦ ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap P.field.k₀ P.field.k)))).map a).left) w

/-- Geometric Cartesian change, using the actual maps of the model square.
Source: def-weil-pbc-cartesian-square and def-pur-tate-datum
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def geometricChange {P : PurityFiniteSetting.{u}} {d : ℕ} (M N : Model P d)
    (u₀ : N.X₀ ⟶ M.X₀) (v₀ : N.Y₀ ⟶ M.Y₀)
    (sq : ChosenCartesianSquare u₀.left N.f₀.left M.f₀.left v₀.left)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) : Change M N where
  QX := P.smoothPurityPullback (P.frobeniusMap u₀)
  QY := P.smoothPurityPullback (P.frobeniusMap v₀)
  q := P.finiteTensorPullbackTensor (P.frobeniusMap u₀)
  shift := (P.smoothPurityPullback (P.frobeniusMap u₀)).commShiftIso
  sigma := square P _ _ _ _ (modelSquare M N u₀ v₀ sq)
  CX := square P _ _ _ _
    (P.field.frobenius_square_cartesian N.X₀ M.X₀ u₀).2.2.2.2.1.symm
  CY := square P _ _ _ _
    (P.field.frobenius_square_cartesian N.Y₀ M.Y₀ v₀).2.2.2.2.1.symm
  t := linePullback P u₀ ζ hζ d



/-- A second smooth model morphism with exactly the required common middle scheme.
Source: composition clause (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
structure Following {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) (e : ℕ) where
  Z₀ : Over (Spec (.of P.field.k₀))
  h₀ : M.Y₀ ⟶ Z₀
  [finiteZ : LocallyOfFiniteType Z₀.hom]
  [compactZ : QuasiCompact Z₀.hom]
  [separatedZ : IsSeparated Z₀.hom]
  [finiteMap : LocallyOfFiniteType h₀.left]
  [compactMap : QuasiCompact h₀.left]
  [separatedMap : IsSeparated h₀.left]
  [smooth : SmoothOfRelativeDimension e (P.frobeniusMap h₀)]

attribute [instance] Following.finiteZ Following.compactZ Following.separatedZ
  Following.finiteMap Following.compactMap Following.separatedMap Following.smooth

/-- The second arrow, retaining its actual common middle model.
Source: composition clause (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Following.model {P : PurityFiniteSetting.{u}} {d e : ℕ} {M : Model P d}
    (N : Following M e) : Model P e where
  X₀ := M.Y₀
  Y₀ := N.Z₀
  f₀ := N.h₀

/-- The composite arrow; the smooth dimension is the sum of the two given dimensions.
Source: composition clause (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Following.composite {P : PurityFiniteSetting.{u}} {d e : ℕ} {M : Model P d}
    (N : Following M e) : Model P (d + e) where
  X₀ := M.X₀
  Y₀ := N.Z₀
  f₀ := M.f₀ ≫ N.h₀
  finiteMap := inferInstanceAs (LocallyOfFiniteType (M.f₀.left ≫ N.h₀.left))
  compactMap := inferInstanceAs (QuasiCompact (M.f₀.left ≫ N.h₀.left))
  separatedMap := inferInstanceAs (IsSeparated (M.f₀.left ≫ N.h₀.left))
  smooth := by
    simpa only [frobeniusMap, Functor.map_comp, Over.comp_left] using
      (inferInstance : SmoothOfRelativeDimension (d + e)
        (P.frobeniusMap M.f₀ ≫ P.frobeniusMap N.h₀))

/-- The prescribed compositor with the base-change functor's composition equality.
Source: Stacks 0D6D (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def Following.compositor {P : PurityFiniteSetting.{u}} {d e : ℕ} {M : Model P d}
    (N : Following M e) (K : D P N.model.Y) :
    N.composite.F.obj K ≅ M.F.obj (N.model.F.obj K) :=
  eqToIso (congrArg (fun f ↦ (P.smoothPurityPullback f).obj K)
    (congrArg (fun f ↦ f.left)
      ((Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap P.field.k₀ P.field.k)))).map_comp M.f₀ N.h₀))) ≪≫
    (compositionFixedPullbackComp P.Ring (P.frobeniusMap M.f₀)
      (P.frobeniusMap N.h₀)).app K

/-- Extract both termwise even shifts and split the pullback of the inner tensor.
Source: composition and shift clauses
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def expand (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d e : ℕ) (U V : D P Y) (W : D P X) :
    (((P.smoothPurityPullback f).obj ((U ⊗ V)⟦2 * (e : ℤ)⟧)) ⊗ W)⟦2 * (d : ℤ)⟧ ≅
      (((P.smoothPurityPullback f).obj U ⊗
        (P.smoothPurityPullback f).obj V) ⊗ W)⟦2 * ((d + e : ℕ) : ℤ)⟧ :=
  (shiftFunctor _ (2 * (d : ℤ))).mapIso
    (tensorIso
        (((P.smoothPurityPullback f).commShiftIso (2 * (e : ℤ))).app _)
        (Iso.refl W) ≪≫
      tensorIso ((shiftFunctor _ (2 * (e : ℤ))).mapIso
        (P.finiteTensorPullbackTensor f U V)) (Iso.refl W) ≪≫
      ((tensorRight W).commShiftIso (2 * (e : ℤ))).app _) ≪≫
    ((shiftFunctorAdd' _ (2 * (e : ℤ)) (2 * (d : ℤ))
      (2 * ((d + e : ℕ) : ℤ)) (by omega)).app _).symm

/-- Split T_(d+e) in the order (f^*T_e,T_d), using the actual signed product and
root-restriction map, with the unit case included.
Source: composition clause and coefficient-twist additivity
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def splitLine {P : PurityFiniteSetting.{u}} {d e : ℕ} (M : Model P d)
    (_N : Following M e) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :
    P.finiteTensorFixedLine M.X (d + e) ≅
      M.F.obj (P.finiteTensorFixedLine M.Y e) ⊗ P.finiteTensorFixedLine M.X d :=
  eqToIso (congrArg (P.finiteTensorFixedLine M.X)
    (by omega : ((d + e : ℕ) : ℤ) = (e : ℤ) + (d : ℤ))) ≪≫
    (P.finiteTensorProduct M.X e d).symm ≪≫
    tensorIso (linePullback P M.f₀ ζ hζ e).symm (Iso.refl _)

/-- Expand the composite source to the unambiguously parenthesized triple tensor.
Source: composition clause (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def compositeSourceExpansion {P : PurityFiniteSetting.{u}} {d e : ℕ} (M : Model P d)
    (N : Following M e) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (K : D P N.model.Y) :
    N.composite.source.obj K ≅
      ((M.F.obj (N.model.F.obj K) ⊗ M.F.obj (P.finiteTensorFixedLine M.Y e)) ⊗
        P.finiteTensorFixedLine M.X d)⟦2 * ((d + e : ℕ) : ℤ)⟧ :=
  (shiftFunctor _ (2 * ((d + e : ℕ) : ℤ))).mapIso
    (tensorIso (N.compositor K) (splitLine M N ζ hζ) ≪≫ (α_ _ _ _).symm)

/-- The canonical composition map P_f P_h -> P_(hf), including tensor and shift maps.
Source: composition clause (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def compositionSource {P : PurityFiniteSetting.{u}} {d e : ℕ} (M : Model P d)
    (N : Following M e) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (K : D P N.model.Y) :
    M.source.obj (N.model.source.obj K) ≅ N.composite.source.obj K :=
  expand P (P.frobeniusMap M.f₀) d e (N.model.F.obj K)
      (P.finiteTensorFixedLine M.Y e) (P.finiteTensorFixedLine M.X d) ≪≫
    (compositeSourceExpansion M N ζ hζ K).symm

/-- Expand b_f and f^*(b_h), then use c_f inverse on the middle Tate factor.
Source: the first composition route in the node
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def iteratedRoute {P : PurityFiniteSetting.{u}} {d e : ℕ} (M : Model P d)
    (N : Following M e) (K : D P N.model.Y) :
    M.GX.obj (M.source.obj (N.model.source.obj K)) ≅
      ((M.F.obj (N.model.F.obj (N.model.GY.obj K)) ⊗
        M.GX.obj (M.F.obj (P.finiteTensorFixedLine M.Y e))) ⊗
          M.GX.obj (P.finiteTensorFixedLine M.X d))⟦2 * ((d + e : ℕ) : ℤ)⟧ :=
  M.b (N.model.source.obj K) ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (tensorIso (M.F.mapIso (N.model.b K)) (Iso.refl _)) ≪≫
    expand P (P.frobeniusMap M.f₀) d e (N.model.F.obj (N.model.GY.obj K))
      (N.model.GX.obj (P.finiteTensorFixedLine M.Y e))
      (M.GX.obj (P.finiteTensorFixedLine M.X d)) ≪≫
    (shiftFunctor _ (2 * ((d + e : ℕ) : ℤ))).mapIso
      (tensorIso (tensorIso (Iso.refl _) (M.c (P.finiteTensorFixedLine M.Y e)).symm)
        (Iso.refl _))

/-- Expand the target of b_(hf) using the compositor, pullback-tensor and twist addition.
Source: the second composition route in the node
(blueprint: lem-pur-finite-tate-source-structural-coherence). -/
def compositeTargetExpansion {P : PurityFiniteSetting.{u}} {d e : ℕ} (M : Model P d)
    (N : Following M e) (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (K : D P N.model.Y) :
    N.composite.target.obj K ≅
      ((M.F.obj (N.model.F.obj (N.model.GY.obj K)) ⊗
        M.GX.obj (M.F.obj (P.finiteTensorFixedLine M.Y e))) ⊗
          M.GX.obj (P.finiteTensorFixedLine M.X d))⟦2 * ((d + e : ℕ) : ℤ)⟧ :=
  (shiftFunctor _ (2 * ((d + e : ℕ) : ℤ))).mapIso
    (tensorIso (N.compositor (N.model.GY.obj K)) (M.GX.mapIso (splitLine M N ζ hζ)) ≪≫
      tensorIso (Iso.refl _)
        (P.finiteTensorPullbackTensor (P.frobeniusGaloisMap M.X₀)
          (M.F.obj (P.finiteTensorFixedLine M.Y e)) (P.finiteTensorFixedLine M.X d)) ≪≫
      (α_ _ _ _).symm)


/-- The termwise shift structure on the actual source functor.
Source: shift clause (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
instance Model.sourceCommShift {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) :
    M.source.CommShift ℤ :=
  inferInstanceAs ((M.F ⋙ tensorRight (P.finiteTensorFixedLine M.X d) ⋙
    shiftFunctor _ (2 * (d : ℤ))).CommShift ℤ)

/-- The termwise shift structure on the structural target functor.
Source: shift clause (blueprint: lem-pur-finite-tate-source-structural-coherence). -/
instance Model.targetCommShift {P : PurityFiniteSetting.{u}} {d : ℕ} (M : Model P d) :
    M.target.CommShift ℤ :=
  inferInstanceAs ((M.GY ⋙ M.F ⋙ tensorRight (M.GX.obj (P.finiteTensorFixedLine M.X d)) ⋙
    shiftFunctor _ (2 * (d : ℤ))).CommShift ℤ)


/-- Coherence of the actual finite Tate-source structural comparison: finite reduction,
Cartesian pullback, smooth composition, naturality and termwise shifts.
Source: latest def-pur-tate-datum, displayed first arrow; the constituent-compatibility
assembly in prop-pur-weil-equivariance-compatibilities
(blueprint: lem-pur-finite-tate-source-structural-coherence).

Proof: (1) Suppress shifts. On flat-term K-flat models the canonical tensorator
splits s tensor (x tensor y) as (s tensor x) tensor (1 tensor y), and the
compositors multiply scalar factors. The finite derived normalization supplies
the corresponding coefficient square even for nonflat quotient maps.
(2) For reduction C_X is the inverse coefficient association, so that square
says (C_U tensor C_V) q Q(mu) = mu' G'(q) C_(U tensor V). For geometric
pullback, the same identity follows by monoidality of the two compositors
comparing the equal scheme paths. Both equations are natural in U,V.
(3) The commuting-input cube gives
F'(C_Y) sigma_(G_Y K) Q(c_f) = c'_f G'_X(sigma_K) C_(F_f K).
For geometric pullback, expand each face into compositors, apply associativity
and cancel inverse pairs. For reduction, both maps on a generalized pure tensor
multiply by the same quotient product, since bar(a) bar(b) = bar(ab).
(4) Expand a_H Q(b). Naturality moves Q(c_f tensor 1) through q. Substitute
(3), then (2), and use naturality of mu' at (sigma,t). This is exactly
b' G'(a_P) C_X, with the independently constructed a_P,a_H above.
(5) For composition put U=f^*h^*K, V=f^*T_e, W=T_d. Both routes split
G_X((U tensor V) tensor W) by two tensorators and apply (f^*c_h)c_f on the
first factor. The iterated route uses monoidality of c_f and its inverse on
T_e; the composite route uses compositor associativity and naturality at the
twist-additivity map. Associativity of mu identifies the triple splittings.
The ordered-power product and root restriction are precisely splitLine;
zero powers use the normalized unit. These give the stated two actual maps.
(6) Restore the canonical termwise shifts. All compositors and balanced
coefficient maps preserve cochain degree. The tensor-shift coefficient is
(-1)^(bp); in composition b=2d or 2e, hence it is 1. The signed addition
law gives the shift 2(d+e), and the pullback-tensor shift normalization gives
the displayed arbitrary-input-shift equation. Naturality of each constituent
gives naturality of b. The argument takes place in the ambient categories
and restricts to the indicated finite-Tor domains, including identity and
zero-dimensional cases; it assumes no flatness of the quotient coefficient ring. -/
theorem finiteTateSourceStructuralCoherence (P : PurityFiniteSetting.{u}) :
    (∀ (d : ℕ) (M : Model P d) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
      (K : D P M.Y),
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos M.Y
        ((sfIntrinsicDerivedEquivalence M.Y P.Ring).functor.obj K) →
      (reductionChange M m hm hmn).Square K) ∧
    (∀ (d : ℕ) (M N : Model P d) (u₀ : N.X₀ ⟶ M.X₀) (v₀ : N.Y₀ ⟶ M.Y₀)
      (sq : ChosenCartesianSquare u₀.left N.f₀.left M.f₀.left v₀.left)
      (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (K : D P M.Y),
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos M.Y
        ((sfIntrinsicDerivedEquivalence M.Y P.Ring).functor.obj K) →
      (geometricChange M N u₀ v₀ sq ζ hζ).Square K) ∧
    (∀ (d e : ℕ) (M : Model P d) (N : Following M e)
      (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent) (K : D P N.model.Y),
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos N.model.Y
        ((sfIntrinsicDerivedEquivalence N.model.Y P.Ring).functor.obj K) →
      (iteratedRoute M N K).hom =
        M.GX.map (compositionSource M N ζ hζ K).hom ≫ (N.composite.b K).hom ≫
          (compositeTargetExpansion M N ζ hζ K).hom) ∧
    ∀ (d : ℕ) (M : Model P d) (K : D P M.Y),
      finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos M.Y
        ((sfIntrinsicDerivedEquivalence M.Y P.Ring).functor.obj K) →
      (∀ (L : D P M.Y),
        finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos M.Y
          ((sfIntrinsicDerivedEquivalence M.Y P.Ring).functor.obj L) →
        ∀ a : K ⟶ L,
          M.GX.map (M.source.map a) ≫ (M.b L).hom = (M.b K).hom ≫ M.target.map a) ∧
      ∀ s : ℤ,
        M.GX.map ((M.source.commShiftIso s).hom.app K) ≫
          (M.GX.commShiftIso s).hom.app (M.source.obj K) ≫ ((M.b K).hom)⟦s⟧' =
            (M.b (K⟦s⟧)).hom ≫ (M.target.commShiftIso s).hom.app K := by
  sorry

end WeilConjectures.PurityFiniteSetting.FiniteTateSource
