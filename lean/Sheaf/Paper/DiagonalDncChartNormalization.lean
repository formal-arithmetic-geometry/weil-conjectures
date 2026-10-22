module

public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.VectorBundlePurity
public import Sheaf.Paper.ProjectionPurityAgreement
public import Sheaf.Paper.StandingExceptionalComposition
public import Sheaf.Paper.PurityNormalProjection
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
public import Sheaf.Paper.PurityNormalCone
import Sheaf.AlgebraicGeometry.SmoothSectionCentredCoordinates
public import Sheaf.AlgebraicGeometry.ReesConeNormalization
public import Sheaf.AlgebraicGeometry.ReesConeNormalizedExistence
public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

/-! # Normalized diagonal/DNC assemblies on affine coordinate charts

Source: main-20261015, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, Steps 1--4; projection-purity-agreement.
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

The arrows below retain the canonical comparison-unit and root-line maps.
No frame, scalar, or orientation is supplied by the caller.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary presentation of the specified diagonal orientation. Its defining
comparison equation determines this presentation: comparison is fully faithful on
these bounded-below objects. Source: chart proof, Step 3
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartOrdinaryOrientation (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    letI := P.noetherian aY
    letI := Dnc.compactifiable P f aY
    P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d :=
  letI := P.noetherian aY
  letI := Dnc.compactifiable P f aY
  ((P.existsUnique_diagonalDualizingObject d f aY).exists.choose_spec).choose

/-- Conversion from the derived tensor unit to the degree-zero coefficient object.
Source: chart proof, source comparison in Step 3
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDualizingUnit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f ≅
      P.diagonalOrdinaryDualizing f :=
  (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).mapIso
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).symm

/-- Alpha is the inverse smooth base-change mate pulled along the actual diagonal,
followed by its section identity and the coefficient-unit comparison.
Source: chart proof, Step 3; diagonal-dualizing-object proof, Step 1
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDiagonalAlpha (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV] :
    letI := P.noetherian aV
    letI := Dnc.compactifiable P h aV
    Dnc.sourceSection P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≅
      P.diagonalDualizing h :=
  letI := P.noetherian aV
  letI := P.noetherian (h ≫ aV)
  letI := Dnc.compactifiable P h aV
  letI := (P.comparedDiagonalBaseChange d h (h ≫ aV) aV rfl).2.2.2.1
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.diagonalComparedRestriction h
          (asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
            (IsPullback.of_hasPullback h h).flip)) ≪≫ P.chartDualizingUnit h) ≪≫
    (P.diagonalDualizingComparison h).symm

/-- Delta is selected only from the unique, coordinate-normalized DNC comparison.
Its defining equation reads the same family trivialization at t=1 and t=0.
Source: chart proof, Step 3 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDiagonalDelta (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [IsSeparated (h ≫ aV)]
    [LocallyOfFiniteType aV] [QuasiCompact aV] :=
  (Dnc.existsUnique_dncInvariance P d (pullback.fst h h) (h ≫ aV)
    (pullback.diagonal h) (pullback.diagonal_fst h)).exists.choose

/-- Pulling the specified orientation of a smooth projection to its section,
including the canonical Tate restriction. The vector-purity normalization below
identifies this arrow with zero-section restriction of integration-transposed purity.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartSectionOrientation (P : PurityFiniteSetting.{u})
    {N B : Scheme.{u}} (d : ℕ) (q : N ⟶ B)
    [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
    [SmoothOfRelativeDimension d q]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (z : B ⟶ N)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := Dnc.compactifiable P q aB
    Etale.sectionInvariant P.Coefficient q z ≅ P.diagonalTwistEtale B d :=
  letI := Dnc.compactifiable P q aB
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) z).leftDerivedFunctor.mapIso
      (P.chartDualizingUnit q ≪≫ P.chartOrdinaryOrientation d q aB) ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t z (P.diagonalExponent_isUnit (q ≫ aB)) d

/-- Beta on the actual associated-graded normal cone and its augmentation section.
The normal projection is the one constructed from the diagonal ideal, including rank zero.
Source: chart proof, Steps 2 and 4
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDiagonalBeta (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  let s := pullback.diagonal h
  let g := pullback.fst h h
  let hs := pullback.diagonal_fst h
  letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj g s) :=
    (Scheme.Hom.normalConeData d hs).smoothOfRelativeDimension_proj
  letI := Dnc.normalQuasiCompact d g s hs
  letI := Dnc.normalCompactifiable P d g (h ≫ aV) s hs
  Dnc.normalComparison P d g (h ≫ aV) s hs ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.chartSectionOrientation d (Scheme.Hom.normalConeProj g s) (h ≫ aV)
          s.normalConeZeroSection t)

/-- The local assembly uses alpha inverse, then normalized delta, then beta.
Source: chart proof, Steps 3--4
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartDiagonalAssembly (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [IsSeparated (h ≫ aV)]
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  (P.chartDiagonalAlpha d h aV).symm ≪≫ P.chartDiagonalDelta d h aV ≪≫
    P.chartDiagonalBeta d h aV t

/-- The specified diagonal orientation equals its three canonical local factors,
for every finite coefficient stage and every normalized root-line presentation.
Source: chart proof, Steps 1--4 and diagonal-dualizing-object proof, Steps 1--2
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: form the self-product and pull the inverse smooth base-change mate along
its diagonal (lem-pur-diagonal-base-change). The smooth diagonal is regular, and
its associated-graded normal cone is the relative tangent bundle
(lem-pur-diagonal-regular-immersion; def-pur-normal-bundle). Apply the unique
normalized DNC comparison to this closed section (thm-pur-dnc-invariance).
Vector-bundle purity, restricted to the augmentation section, gives beta
(cor-pur-vector-bundle-purity). These are exactly the three factors in the
specified diagonal orientation. Their canonical unit and site comparisons are
the displayed factors, so composing them yields equality of isomorphisms.
The proof works for d=0, empty schemes, and every positive level without a
ramification divisibility hypothesis. -/
theorem diagonal_dnc_chart_normalization (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    P.diagonalDualizingObject d h aV = P.chartDiagonalAssembly d h aV t := by
  sorry

/-- The selected ordinary arrow has the full counit normalization, and realizes
exactly the specified pro-etale arrow. Source: chart proof, Steps 3--4
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: use the witness equation in existsUnique_diagonalDualizingObject. Its
ordinary witness satisfies DiagonalOrientationNormalization. The same witness is
chosen in chartOrdinaryOrientation, so the comparison equation is unchanged. -/
theorem chartOrdinaryOrientation_spec (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := Dnc.compactifiable P f aY
    P.DiagonalOrientationNormalization d f aY (P.chartOrdinaryOrientation d f aY) ∧
      P.diagonalDualizingObject d f aY = P.diagonalDualizingComparison f ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
            (P.chartOrdinaryOrientation d f aY) := by
  sorry

/-- Source-etale restriction of the normalized arrow. Open restriction is the
special case of an open immersion; the equation also covers every etale change
of coordinate chart. Source: chart proof, final compatibility paragraph
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: cover the source by etale coordinate charts over affine opens of Y.
The two inverse arrows have the same affine counit normalization by
chartOrdinaryOrientation_spec, canonical etale locality and mate pasting.
Remove the common even shift and glue the maps between the Tate-line sheaves.
The comparison-unit equation transports this equality to the pro-etale site. -/
theorem chartOrientation_etale_restriction (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [SmoothOfRelativeDimension d (j ≫ f)]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aY
    letI := P.noetherian (f ≫ aY)
    letI := P.noetherian ((j ≫ f) ≫ aY)
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P (j ≫ f) aY
    (Etale.ordinaryFinitePullback P.Coefficient j).map
        (P.chartOrdinaryOrientation d f aY).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom =
      (P.diagonalEtaleLocality N j f).hom ≫
        (P.chartOrdinaryOrientation d (j ≫ f) aY).hom := by
  sorry

/-- Smooth base change on ordinary dualizing objects, retaining the actual
inverse-compact-support mate and the degree-zero coefficient-unit comparisons.
Source: chart proof, Step 3 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartOrdinaryBaseChange (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (b : Y' ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X)
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback a f' f b) :
    letI := Dnc.compactifiable P f aY
    (Etale.ordinaryFinitePullback P.Coefficient a).obj
      (P.diagonalOrdinaryDualizing f) ≅ P.diagonalOrdinaryDualizing f' :=
  letI := Dnc.compactifiable P f aY
  letI := Dnc.invertibleExponent P (f ≫ aY)
  letI := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    P.Coefficient f d sq
  letI := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
    (inferInstanceAs (IsIso
      ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app (𝟙_ _))))
  (Etale.ordinaryFinitePullback P.Coefficient a).mapIso (P.chartDualizingUnit f).symm ≪≫
    asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq) ≪≫
      P.chartDualizingUnit f'

/-- Target-open restriction of the orientation; combined with source restriction
this is the arbitrary pair of affine opens U and V in the node.
Source: chart proof, final restriction paragraph
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: base change the diagonal square and its inverse smooth base-change mate.
The normalized DNC arrow is unchanged by its base-change characterization.
Vector integration and the pure-root Tate restriction commute with this base
change. Therefore the three factors pull back to the three new factors.
Apply the defining assembly equality locally and glue on affine opens. -/
theorem chartOrientation_open_baseChange (P : PurityFiniteSetting.{u})
    {X Y X' V : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (v : V ⟶ Y) [IsOpenImmersion v] [QuasiCompact v]
    (h : X' ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (j : X' ⟶ X) (sq : IsPullback j h f v)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := Dnc.compactifiable P f aY
    letI := Dnc.compactifiable P h (v ≫ aY)
    (Etale.ordinaryFinitePullback P.Coefficient j).map
        (P.chartOrdinaryOrientation d f aY).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom =
      (P.chartOrdinaryBaseChange d f aY v h j sq).hom ≫
        (P.chartOrdinaryOrientation d h (v ≫ aY)).hom := by
  sorry

/-- The actual coordinate differences y_i-x_i, based at the first projection.
Source: chart proof, Steps 1--2
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartCoordinateDifferences {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) :
    pullback h h ⟶ AffineSpace (ULift.{u} (Fin d)) U :=
  AffineSpace.homOfVector (pullback.fst h h) fun i ↦
    (pullback.snd h h ≫ u).appTop (AffineSpace.coord V i) -
      (pullback.fst h h ≫ u).appTop (AffineSpace.coord V i)

/-- Differences give a Cartesian centred etale neighbourhood of the entire diagonal.
The zero fibre is exactly the diagonal after discarding its other etale components.
Source: chart proof, Step 1 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: the product of the coordinate etale map with itself is etale. The inverse
image of the affine diagonal is U times_A U; its own diagonal U is open and
closed because u is separated etale. Remove its complementary closed component.
On the resulting open, subtraction makes the displayed zero square Cartesian.
The shear (x,y) -> (x,y-x) is an affine-space automorphism; base change of u and
this shear show that the displayed difference map is etale there. At d=0 the
same argument gives the identity pair, and it also applies to empty U. -/
theorem chartCoordinateDifferences_neighbourhood {U V : Scheme.{u}}
    (d : ℕ) (h : U ⟶ V) (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [Etale u] [IsSeparated u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃ (O : (pullback h h).Opens) (s : U ⟶ O.toScheme),
      s ≫ O.ι = pullback.diagonal h ∧
      Etale (O.ι ≫ chartCoordinateDifferences d h u) ∧
      IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h u)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) U) := by
  sorry

/-- The actual diagonal normal cone is the symmetric total space of the diagonal
conormal module, including the empty regular sequence when d=0. Thus it is the
relative tangent bundle, rather than a separately chosen rank-d bundle.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: apply centred smooth-section coordinates to the first projection and its
diagonal. The coordinate ideal is a regular sequence of length d, including
length zero. Its degree-one classes give the conormal frame and its homogeneous
monomials identify Sym(I/I^2) with the associated graded algebra. Relative Spec
of this canonical comparison, composed with the homogeneous-normalized Rees
comparison, identifies the actual normal cone and preserves augmentation. -/
theorem chartDiagonalNormalBundle {U V : Scheme.{u}} [IsNoetherian U]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    [QuasiCompact h] :
    (ConormalGradedAlgebra.piece (pullback.diagonal h) 1).IsFiniteLocallyFreeOfRank d ∧
      IsIso (ConormalGradedAlgebra.symmetricComparison (pullback.diagonal h)) := by
  sorry

/-- The constant ordinary coefficient complex is constructible of Tor amplitude
[0,0]. Source: the coefficient-unit input in chart proof, Step 4
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: the constant sheaf A is locally free of rank one. Its degree-zero complex
is bounded constructible and tensoring with it is the identity, giving [0,0]. -/
theorem chartCoefficientUnit_finiteTor (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y
      (Etale.ordinaryFiniteUnit P.Coefficient Y) := by
  sorry

/-- Pullback of the compared coefficient unit, with the canonical monoidal map.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartUnitPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (P.smoothPurityPullback f).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y)) ≅
      𝟙_ (_root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :=
  (P.smoothPurityPullback f).mapIso (projectionUnitRaw P.Coefficient Y) ≪≫
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) f).symm.app _ ≪≫
    ProEtale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) f

attribute [local irreducible] chartUnitPullback projectionUnitRaw

/-- Shift cancellation followed by the specified unit comparison and left unitor.
Source: projection-purity-agreement unit normalization
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartProjectionUnitSourceGeneric (C : Type v) [Category.{w} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [_root_.DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (r : ℤ) (M T : _root_.DerivedCategory C)
    (e : M ≅ 𝟙_ (_root_.DerivedCategory C)) :=
  smoothPurityTensorShiftGeneric C r M T ≪≫
    ((curriedTensor (_root_.DerivedCategory C)).mapIso e).app T ≪≫ (λ_ T)

/-- The actual shift, tensor-unit and pullback-unit composite, retaining its
computed endpoints. Source: projection-purity-agreement, coefficient-unit case
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartProjectionUnitSourceRaw (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) (d : ℕ) :
    Σ M N : ProEtale.AffineSpacePurity.C P.Coefficient (iteratedAffineLine Y d), M ≅ N :=
  ⟨_, _, chartProjectionUnitSourceGeneric
      (Sheaf (Scheme.ProEt.topology (iteratedAffineLine Y d))
        (ModuleCat.{u + 1} P.Coefficient)) (2 * (d : ℤ)) _
      (P.diagonalTwist (iteratedAffineLine Y d) d)
      (P.chartUnitPullback (iteratedAffineLineProj Y d))⟩

/-- The canonical source composite has the recorded cached endpoints, uniquely
as its actual raw map. Source: projection-purity-agreement unit normalization
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: rewrite the cached tensor by smoothPurityTensorPresentation. Its
second-variable shift comparison is exactly smoothPurityTensorShiftGeneric.
The remaining factors are the same pullback-unit comparison and left unitor.
Thus the raw endpoints are the displayed ones; transport gives reflexive HEq.
Two proposed transports have the same raw isomorphism, giving uniqueness. -/
theorem chartProjectionUnitSource_existsUnique (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (d : ℕ) :
    ∃! e : projectionSmoothSource P Y
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y)) d ≅
      P.diagonalTwist (iteratedAffineLine Y d) d,
      HEq e (P.chartProjectionUnitSourceRaw Y d).2.2 := by
  sorry

/-- Cancel only the published pullback, tensor-unit and even-shift coordinates
at A. The raw-map equality determines the isomorphism uniquely and involves
no purity arrow. Source: projection-purity-agreement normalization
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartProjectionUnitSource (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) (d : ℕ) :
    projectionSmoothSource P Y
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y)) d ≅
      P.diagonalTwist (iteratedAffineLine Y d) d :=
  (P.chartProjectionUnitSource_existsUnique Y d).exists.choose

/-- The recorded ordered affine comparison at A, in diagonal dualizing coordinates.
Positive level n+1 enumerates every allowed stage for every finite extension E.
Only the published root-power, unit, shift and exceptional-identity transports
are applied to affineSpacePurityComparison.
Source: chart proof, Step 4; projection-purity-agreement
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartGamma (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY] (d : ℕ) :
    letI := (ProEtale.AffineSpacePurity.projection_geometry Y d).2
    (projectionSetting F C E n).diagonalTwist (iteratedAffineLine Y d) d ⟶
      (projectionSetting F C E n).diagonalDualizing (iteratedAffineLineProj Y d) :=
  let P := projectionSetting F C E n
  letI := (ProEtale.AffineSpacePurity.projection_geometry Y d).2
  (P.chartProjectionUnitSource Y d).inv ≫
    projectionAffineInPresentation F C E n Y aY
      ⟨(ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
            (Etale.ordinaryFiniteUnit P.Coefficient Y),
        (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
          (P.diagonalUnitPlus Y)).plus⟩
      (Etale.ordinaryFiniteUnit P.Coefficient Y)
      (P.chartCoefficientUnit_finiteTor Y) (Iso.refl _) d

/-- The ordered map is the inverse specified orientation, at all positive stages.
Source: chart proof, Step 4; projection-purity-agreement at A_Y
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: apply projection_purity_agreement to the coefficient unit. Its finite Tor
interval is [0,0]. The smooth-purity tensor map at the unit is the inverse
diagonal orientation, by the adjunction triangle after cancelling the canonical
unit, even-shift and Tate tensor coordinates. These are precisely the maps in
chartProjectionUnitSource and projectionAffineInPresentation. Rank zero uses
the published exceptional-identity comparison and ordered comparisonZero. -/
theorem chartGamma_eq_inverseOrientation
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) [IsAffine Y] (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ) :
    letI := projection_smooth Y d
    HEq (chartGamma F C E n Y aY d)
      ((projectionSetting F C E n).diagonalDualizingObject d
        (iteratedAffineLineProj Y d) aY).inv := by
  sorry

/-- The ordinary counit mate and the ordered pro-etale affine comparison have
identical maps after the canonical coefficient transport. The two recursive
coordinate towers have the same ordered polynomial coordinates.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: both traces are the ordered iteration of the normalized P1 trace and the
open counit. The affine-line Kummer normalization identifies their first factors.
Induct on dimension using compact-support composition and adjunction pasting.
The root-power comparison is projectionRootTransition and is identity on pure
root tensors on a primitive-root cover; hence it introduces no scalar. Compare
exceptional units by diagonalDualizingComparison. Zero is the identity adjunct. -/
theorem chartGamma_counit_normalization
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) [IsAffine Y] (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport (projectionSetting F C E n).Coefficient
      (projectionSetting F C E n).diagonalExponent
      (projectionSetting F C E n).diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit ((projectionSetting F C E n).diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum (projectionSetting F C E n).Coefficient
        (projectionSetting F C E n).diagonalExponent
        (projectionSetting F C E n).diagonalExponent_annihilates t T hT) :
    letI := (projectionSetting F C E n).noetherian aY
    HEq
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient)
          (affineTraceTower Y d)).mapDerivedCategory.map
            ((projectionSetting F C E n).diagonalAffineMate t D Y
              ((projectionSetting F C E n).diagonalExponent_isUnit aY) d) ≫
        ((projectionSetting F C E n).diagonalDualizingComparison
          (affineTraceProjection Y d)).inv)
      (chartGamma F C E n Y aY d) := by
  sorry

/-- Inverse-arrow form of theta_h = Lu*(Gamma^-1) epsilon_u, with the
canonical Tate pullback written explicitly. Locality is the normalized mate of
compact-support composition and the etale sum/evaluation adjunction.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: apply chartOrdinaryOrientation_spec with the identity source chart and
coordinate chart u. Normalize identity locality using the adjunction triangle.
The result is precisely the displayed inverse-arrow equality. The preceding
counit-normalization theorem identifies its affine mate with the existing
ordered Gamma. Invert this equality to obtain the formula in the node. -/
theorem chartOrientation_coordinate_formula (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ affineTraceTower V d) [Etale u] [IsSeparated u]
    [LocallyOfFiniteType u] [QuasiCompact u]
    (w : u ≫ affineTraceProjection V d = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    letI := P.noetherian aV
    letI := P.noetherian (h ≫ aV)
    letI := affineTraceNoetherian V d
    letI := Dnc.compactifiable P h aV
    letI : HasCompactification (u ≫ affineTraceProjection V d) :=
      HasCompactification.of_eq w.symm
    (P.chartOrdinaryOrientation d h aV).inv =
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t u
          (affineTraceInvertible P.diagonalExponent V (P.diagonalExponent_isUnit aV) d)
            d).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient u).map
        (P.diagonalAffineMate t D V (P.diagonalExponent_isUnit aV) d) ≫
      (P.diagonalEtaleLocality N u (affineTraceProjection V d)).hom ≫
      (P.diagonalDualizingCongr w).hom := by
  sorry

/-- Beta is vector integration-transposed purity restricted to the actual normal
zero section. The formula is asserted in every vector-bundle presentation over U;
consequently its value is independent of a frame. No presentation is used to
choose beta. Source: chart proof, Steps 2 and 4
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: the canonical symmetric comparison for the diagonal conormal identifies
the actual normal cone with its vector-bundle model. On each affine frame the
normalized integration is the ordered affine trace. Apply the coordinate formula
and chartGamma_counit_normalization; the exceptional adjunction identifies the
inverse orientation with the integration adjunct displayed below. Vector purity
base change identifies these adjuncts on common frames. They glue because the
unshifted Tate line is a sheaf. Changing the bundle presentation pulls back this
same equation by normalized etale locality. Finally pull back along zero and
apply the canonical Tate restriction; this is chartDiagonalBeta. Rank zero is
the empty ordered trace and the identity adjunction. -/
theorem chartNormal_vectorPurity_normalization (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (M : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := P.noetherian (h ≫ aV)
    letI : SmoothOfRelativeDimension d
        (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h)) :=
      (Scheme.Hom.normalConeData d (pullback.diagonal_fst h)).smoothOfRelativeDimension_proj
    letI := Dnc.normalQuasiCompact d (pullback.fst h h)
      (pullback.diagonal h) (pullback.diagonal_fst h)
    letI := Dnc.normalCompactifiable P d (pullback.fst h h) (h ≫ aV)
      (pullback.diagonal h) (pullback.diagonal_fst h)
    letI := P.noetherian
      (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ≫ (h ≫ aV))
    ∀ (F : U.Modules) [F.IsFiniteLocallyFreeOfRank d]
      (e : VectorBundleZeroSection.scheme U d F ≅ (pullback.diagonal h).ker.normalCone)
      (w : e.hom ≫ Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) =
        VectorBundleZeroSection.π U d F),
      letI := (Etale.vectorIntegration_geometry U d F).1
      letI := (Etale.vectorIntegration_geometry U d F).2.1
      letI := P.noetherian (VectorBundleZeroSection.π U d F ≫ (h ≫ aV))
      letI := Dnc.compactifiable P (VectorBundleZeroSection.π U d F) (h ≫ aV)
      letI : HasCompactification (e.hom ≫
          Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h)) :=
        HasCompactification.of_eq w.symm
      (Etale.ordinaryFinitePullback P.Coefficient e.hom).map
          (P.chartOrdinaryOrientation d
            (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h))
            (h ≫ aV)).inv ≫
        (P.diagonalEtaleLocality M e.hom
          (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h))).hom ≫
        (P.diagonalDualizingCongr w).hom =
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t e.hom
          (P.diagonalExponent_isUnit
            (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ≫
              (h ≫ aV))) d).hom ≫
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t (VectorBundleZeroSection.π U d F)
          (P.diagonalExponent_isUnit (h ≫ aV)) d).inv ≫
        (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient)
          (VectorBundleZeroSection.π U d F)).homEquiv _ _
            (Etale.vectorBundleIntegration P.diagonalExponent
              (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
              P.diagonalExponent_annihilates U (P.diagonalExponent_isUnit (h ≫ aV)) d F) := by
  sorry

/-- Relative Spec of the canonical symmetric comparison, followed by the normalized
Rees comparison, from the actual cone to its conormal vector bundle. Its homogeneous
normalization fixes every ideal class, so it contains no arbitrary bundle automorphism.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartNormalModelRaw {U V : Scheme.{u}} [IsNoetherian U]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    [QuasiCompact h] :
    letI := (chartDiagonalNormalBundle d h).1
    (pullback.diagonal h).ker.normalCone ≅ VectorBundleZeroSection.scheme U d
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) :=
  letI := (chartDiagonalNormalBundle d h).1
  let e : VectorBundleZeroSection.algebraObject U d
        (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ≅
      PurityNormalBundle.algebraObject (pullback.diagonal h) :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _
      (ConormalGradedAlgebra.symmetricComparison (pullback.diagonal h))
      (chartDiagonalNormalBundle d h).2)
  let eOver := (ObjectProperty.ι (fun Y : Over U ↦ IsAffineHom Y.hom)).mapIso
    (((VectorBundleZeroSection.antiEquivalence U).inverse.mapIso e).unop)
  (Etale.FiniteSmoothPurity.reesConeComparison_exists (pullback.diagonal h)).choose ≪≫
    (Over.forget U).mapIso eOver

/-- The conormal vector-bundle model exists for the actual diagonal normal cone,
with its actual projection and zero section. This makes the preceding universal
presentation equation nonvacuous also in rank zero.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: take the inverse of chartNormalModelRaw. Its specified value gives uniqueness.
chartDiagonalNormalBundle gives finite local freeness and invertibility
of the canonical symmetric comparison. Apply the relative Spec anti-equivalence
and compose with the homogeneous-normalized Rees comparison. Both algebra maps
preserve constants and augmentation, so projection and zero commute. Their
coordinate formulas identify this with the differential normal-bundle map. -/
theorem chartNormal_model_exists {U V : Scheme.{u}} [IsNoetherian U]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    [QuasiCompact h] :
    letI := (chartDiagonalNormalBundle d h).1
    ∃! e : VectorBundleZeroSection.scheme U d
        (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ≅
          (pullback.diagonal h).ker.normalCone,
      e = (chartNormalModelRaw d h).symm ∧
      e.hom ≫ Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) =
        VectorBundleZeroSection.π U d (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ∧
      VectorBundleZeroSection.zero U d (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ≫
        e.hom = (pullback.diagonal h).normalConeZeroSection := by
  sorry

/-- The affine counit mate is invertible at every finite coefficient stage.
Source: chart proof, Step 4; projection-purity-agreement
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: chartGamma_counit_normalization identifies the realization of this mate
with the existing ordered comparison at the unit. Projection-purity-agreement
identifies that map with inverse smooth orientation. Finite site comparison
reflects isomorphisms on the bounded-below etale objects, giving the assertion. -/
theorem chartAffineMate_isIso (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    letI := P.noetherian aB
    IsIso (P.diagonalAffineMate t D B (P.diagonalExponent_isUnit aB) r) := by
  sorry

/-- Gamma in the ordinary-etale coefficient presentation, with its actual
ordered-counit hom. Source: chart proof, Step 4
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartAffineGamma (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :=
  letI := P.noetherian aB
  letI := P.chartAffineMate_isIso B aB r t D
  asIso (P.diagonalAffineMate t D B (P.diagonalExponent_isUnit aB) r)

/-- Epsilon is the exceptional-composition mate followed by etale identification,
in its normalized ordinary presentation. The normalized locality iso is defined
by transposing the actual compact-support compositor and sum-extension counit.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartEpsilon (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ affineTraceTower V d) [Etale u] [IsSeparated u]
    [LocallyOfFiniteType u] [QuasiCompact u]
    (w : u ≫ affineTraceProjection V d = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  letI := P.noetherian aV
  letI := P.noetherian (h ≫ aV)
  letI := affineTraceNoetherian V d
  letI := Dnc.compactifiable P h aV
  letI : HasCompactification (u ≫ affineTraceProjection V d) :=
    HasCompactification.of_eq w.symm
  (P.diagonalDualizingCongr w).symm ≪≫
    (P.diagonalEtaleLocality N u (affineTraceProjection V d)).symm

/-- The requested forward coordinate formula, including the canonical Tate
restriction. Gamma has exactly its ordered counit hom, and epsilon its
composition/etale-adjunction hom. Source: chart proof, Step 4
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: invert chartOrientation_coordinate_formula and use chartAffineMate_isIso.
The inverse of a composite reverses its order. The three resulting factors are
exactly chartEpsilon, pullback of chartAffineGamma.symm, and the canonical Tate
pullback. The normalized counit comparison identifies Gamma with the published
ordered map at every positive level, without restriction on ramification. -/
theorem chartOrientation_coordinate_formula_forward (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ affineTraceTower V d) [Etale u] [IsSeparated u]
    [LocallyOfFiniteType u] [QuasiCompact u]
    (w : u ≫ affineTraceProjection V d = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    P.chartOrdinaryOrientation d h aV = P.chartEpsilon d h aV u w N ≪≫
      (Etale.ordinaryFinitePullback P.Coefficient u).mapIso
        (P.chartAffineGamma V aV d t D).symm ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t u
          (affineTraceInvertible P.diagonalExponent V (P.diagonalExponent_isUnit aV) d) d := by
  sorry

/-- Ordered affine space is smooth of its coordinate dimension.
Source: chart proof, Step 1 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: transport projection_smooth through the coordinate-preserving isomorphism
between the two ordered affine towers. It is the identity at zero; at a
successor both towers adjoin the same final polynomial variable. -/
theorem chartTraceProjection_smooth (B : Scheme.{u}) (r : ℕ) :
    SmoothOfRelativeDimension r (affineTraceProjection B r) := by
  sorry

/-- The standard zero section in the ordered affine coordinate tower.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartTraceZero (B : Scheme.{u}) : (r : ℕ) → B ⟶ affineTraceTower B r
  | 0 => 𝟙 B
  | r + 1 => AffineSpace.homOfVector (chartTraceZero B r) (fun _ ↦ 0)

/-- The standard b_r is precisely the zero pullback of the inverse ordered
comparison, followed by the same Tate restriction. The zero section is the recursive
zero vector, with no section chosen by the caller.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: take the identity coordinate map of affine space in the forward chart
formula. Identity exceptional composition and etale locality are the canonical
identity-adjunction comparisons. Pull the resulting equality along chartTraceZero,
precede with chartDualizingUnit, and compose the canonical Tate restriction.
This is exactly chartSectionOrientation and is the zero-section vector purity
normalization, by the integration-adjunction equation; at rank zero all factors
reduce to the identity-unit constraints. -/
theorem chartStandardSection_formula (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (r : ℕ)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    letI := chartTraceProjection_smooth B r
    P.chartSectionOrientation r (affineTraceProjection B r) aB (chartTraceZero B r) t =
      (Etale.ordinaryFinitePullback P.Coefficient (chartTraceZero B r)).mapIso
        (P.chartDualizingUnit (affineTraceProjection B r) ≪≫
          (P.chartAffineGamma B aB r t D).symm) ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t (chartTraceZero B r)
          (affineTraceInvertible P.diagonalExponent B (P.diagonalExponent_isUnit aB) r) r := by
  sorry

/-- The comparison image of A[0] lies in the actual bounded constructible
category used by standingExceptionalComposition.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: the ordinary constant coefficient sheaf is finite locally constant,
hence constructible; its single complex is bounded. The pro-etale bounded
constructibility predicate is its comparison-image predicate. -/
theorem chartCoefficientUnit_constructible (P : PurityFiniteSetting.{u}) (V : Scheme.{u}) :
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} P.Coefficient) V
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) V).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient V)) := by
  sorry

/-- The coefficient unit in the standing bounded constructible category.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartCoefficientUnit (P : PurityFiniteSetting.{u}) (V : Scheme.{u}) :
    ProEtale.DerivedCategoryBoundedConstructible (ModuleCat.{u + 1} P.Coefficient) V :=
  ⟨_, P.chartCoefficientUnit_constructible V⟩

/-- The etale exceptional identification on any specified bounded-below etale
presentation. It is the unique counit-preserving adjunction comparison of the
normalized sum-extension comparison, transported through the comparison unit.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartEtaleIdentification (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} [IsNoetherian U] [IsNoetherian X]
    (u : U ⟶ X) [Etale u] [IsSeparated u] [HasCompactification u]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (K : Etale.DerivedCategoryModule P.Coefficient X)
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) u).obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) u).leftDerivedFunctor.obj
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj K) :=
  let A := ModuleCat.{u + 1} P.Coefficient
  letI := ProEtale.isIso_derivedComparisonAdjunction_unit_app A X K hK
  let ρ := (N.adjunction u (HasCompactification.compactification u)
    (Etale.rightDerivedUpperShriek A u)
    (Etale.rightDerivedUpperShriekAdjunction A u)).exists.choose
  (ProEtale.comparisonUpperStar A U).mapDerivedCategory.mapIso
      ((Etale.rightDerivedUpperShriek A u).mapIso
        (asIso ((ProEtale.derivedComparisonAdjunction A X).unit.app K)).symm ≪≫
        ρ.app K ≪≫ (Etale.leftDerivedUpperStarIsoMapDerivedCategory A u).symm.app K) ≪≫
    (Dnc.pullComparison P u K).symm

/-- The epsilon used in the coordinate formula is exactly the standing pur9
composition map followed by the canonical etale identification. This compares
actual maps, including every comparison unit; it is not an endpoint existence.
Source: chart proof, Step 4 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: unfold standingExceptionalComposition: it transposes the compact-support
compositor and the composite counit through the two standing Hom bijections.
Transport each bijection to its ordinary-etale representative. Comparison units
cancel by the triangle identities. The normalized etale adjunction then turns
the first compact-support factor into sum extension with its evaluation counit.
The resulting conjugate is precisely tensorMateEtalePrecompLocalityIso inverse,
which defines chartEpsilon. Pasting the displayed comparisons gives the equation.
The unit is bounded constructible by chartCoefficientUnit_constructible, so the
standing map has exactly its prescribed domain. -/
theorem chartEpsilon_standing_composition (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (d : ℕ)
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ affineTraceTower V d) [Etale u] [IsSeparated u]
    [LocallyOfFiniteType u] [QuasiCompact u]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := P.noetherian aV
    letI := affineTraceNoetherian V d
    letI := P.noetherian ((u ≫ affineTraceProjection V d) ≫ aV)
    letI := Dnc.compactifiable P u (affineTraceProjection V d ≫ aV)
    letI := Dnc.compactifiable P (u ≫ affineTraceProjection V d) aV
    letI : V.Over (Spec (.of P.field.k)) := ⟨aV⟩
    letI : (affineTraceTower V d).Over (Spec (.of P.field.k)) :=
      ⟨affineTraceProjection V d ≫ aV⟩
    letI : U.Over (Spec (.of P.field.k)) := ⟨u ≫ (affineTraceProjection V d ≫ aV)⟩
    letI : LocallyOfFiniteType (U ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (LocallyOfFiniteType (u ≫ (affineTraceProjection V d ≫ aV)))
    letI : QuasiCompact (U ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (QuasiCompact (u ≫ (affineTraceProjection V d ≫ aV)))
    letI : LocallyOfFiniteType (affineTraceTower V d ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (LocallyOfFiniteType (affineTraceProjection V d ≫ aV))
    letI : QuasiCompact (affineTraceTower V d ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (QuasiCompact (affineTraceProjection V d ≫ aV))
    letI : LocallyOfFiniteType (V ↘ Spec (.of P.field.k)) :=
      inferInstanceAs (LocallyOfFiniteType aV)
    letI : QuasiCompact (V ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aV)
    letI : u.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
    letI : (affineTraceProjection V d).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
    (P.diagonalDualizingComparison (u ≫ affineTraceProjection V d)).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.map
          (P.chartEpsilon d (u ≫ affineTraceProjection V d) aV u rfl N).hom ≫
      (Dnc.pullComparison P u (P.diagonalOrdinaryDualizing
        (affineTraceProjection V d))).inv ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) u).leftDerivedFunctor.map
        (P.diagonalDualizingComparison (affineTraceProjection V d)).inv =
      ProEtale.standingExceptionalComposition P u (affineTraceProjection V d)
          (P.chartCoefficientUnit V) ≫
        (ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) u).map
          (P.diagonalDualizingComparison (affineTraceProjection V d)).hom ≫
        (P.chartEtaleIdentification u N
          (P.diagonalOrdinaryDualizing (affineTraceProjection V d))
          (Etale.plus_rightDerivedUpperShriek_obj (ModuleCat.{u + 1} P.Coefficient)
            (affineTraceProjection V d) _ (P.diagonalUnitPlus V))).hom ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) u).leftDerivedFunctor.map
          (P.diagonalDualizingComparison (affineTraceProjection V d)).inv := by
  sorry

/-- The degree-one identification defining N_Delta = T_(U/V). Its normalization
is [y(a)-x(a)] -> da, so its symmetric relative Spec is the canonical tangent
identification used in the normal model, with the same sign as chart differences.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: on the affine tensor-product ring the diagonal ideal is the kernel of
multiplication. The universal derivation sends a to the class of 1 tensor a
minus a tensor 1. Its universal property identifies I/I^2 with the relative
Kahler module; these classes generate and their relations are additivity and
the Leibniz rule. Sheafify this affine identification. Under the canonical
associated-graded comparison the representative of the same difference has
exactly this class. This gives the stated iso and normalization; generation by
the differentials gives uniqueness. Taking symmetric algebras and relative Spec
identifies the cone with Spec Sym(Omega), preserving projection and augmentation.
The empty affine scheme and the empty rank-zero list cause no exception. -/
theorem chartDiagonalConormal_differentials {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (h : U ⟶ V) [IsSeparated h] :
    ∃! e : ConormalGradedAlgebra.piece (pullback.diagonal h) 1 ≅ h.relativeDifferentials,
      ∀ a : Γ(U, ⊤),
        ∃ b : (ConormalGradedAlgebra.power (pullback.diagonal h) 1).val.obj
            (Opposite.op ⊤),
          (ConormalGradedAlgebra.powerInclusion (pullback.diagonal h) 1).val.app
              (Opposite.op ⊤) b =
            (pullback.snd h h).appTop a - (pullback.fst h h).appTop a ∧
          e.hom.val.app (Opposite.op ((pullback.diagonal h) ⁻¹ᵁ ⊤))
              (ConormalGradedAlgebra.representative (pullback.diagonal h) 1 ⊤ b) =
            h.relativeDifferentials.val.map (homOfLE le_top).op
              (h.relativeDifferentialsDerivation.d (X := Opposite.op ⊤) a) := by
  sorry

/-- Gamma_0 is the identity after the exceptional-identity adjunction comparison.
Source: chart proof, rank-zero clause
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: the ordered affine comparison at dimension zero is comparisonZero, the
literal identity. The comparison-unit and exceptional-identity factors in
projectionAffineInPresentation and chartProjectionUnitSource cancel by the
adjunction triangles. The remaining iso is precisely the displayed identity
exceptional comparison, in inverse direction. -/
theorem chartAffineGamma_zero (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    P.chartAffineGamma B aB 0 t D =
      ((Etale.rightDerivedUpperShriekIsoOfIso
        (ModuleCat.{u + 1} P.Coefficient) (Iso.refl B)).app
          (Etale.ordinaryFiniteUnit P.Coefficient B) ≪≫
        (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
          (Etale.ordinaryFiniteUnit P.Coefficient B)).symm := by
  sorry

/-- The rank-zero section orientation is the identity with only the canonical
identity-pullback, exceptional-identity and coefficient-unit constraints shown.
Source: chart proof, rank-zero clause
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: apply chartStandardSection_formula at rank zero. The coordinate tower
and zero section are identities. Substitute chartAffineGamma_zero, and the
zero-th Tate tensor and its restriction are the canonical coefficient-unit
map. The displayed composite is therefore the identity in normalized coordinates. -/
theorem chartStandardSection_zero (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    P.chartSectionOrientation 0 (𝟙 B) aB (𝟙 B) t =
      (Etale.ordinaryFinitePullback P.Coefficient (𝟙 B)).mapIso
        (P.chartDualizingUnit (𝟙 B) ≪≫
          (Etale.rightDerivedUpperShriekIsoOfIso
            (ModuleCat.{u + 1} P.Coefficient) (Iso.refl B)).app
              (Etale.ordinaryFiniteUnit P.Coefficient B) ≪≫
          (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
            (Etale.ordinaryFiniteUnit P.Coefficient B)) ≪≫
      (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) B).app
        (Etale.ordinaryFiniteUnit P.Coefficient B) := by
  sorry

/-- The ordered differential frame induced by an etale coordinate chart. Combined
with chartDiagonalConormal_differentials and the canonical symmetric comparison,
its relative Spec is N_h = O_U^d with the specified normal-coordinate basis.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: the etale transitivity sequence identifies Omega_U/V with pullback of
the differentials of affine d-space. The latter is free on the ordered dx_i.
The universal derivation commutes with pullback, giving exactly this generator
formula. The free-sheaf universal property makes the normalized map unique;
etale-local invertibility makes it an isomorphism. At d=0 both differential
modules are zero and the unique map is their identity. -/
theorem chartCoordinateDifferentialFrame {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [Etale u] (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃! e : SheafOfModules.free (R := U.ringCatSheaf) (ULift.{u} (Fin d)) ≅
        h.relativeDifferentials,
      ∀ i : ULift.{u} (Fin d),
        e.hom.val.app (Opposite.op ⊤)
            ((SheafOfModules.ιFree (R := U.ringCatSheaf) i).val.app (Opposite.op ⊤)
              (1 : U.ringCatSheaf.obj.obj (Opposite.op ⊤))) =
          h.relativeDifferentialsDerivation.d (X := Opposite.op ⊤)
            (u.appTop (AffineSpace.coord V i)) := by
  sorry

/-- The conormal model with its value fixed by relative Spec and homogeneous Rees
coordinates. The equality in chartNormal_model_exists determines the selected object.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartNormalModel {U V : Scheme.{u}} [IsNoetherian U]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [SmoothOfRelativeDimension d h]
    [QuasiCompact h] :
    letI := (chartDiagonalNormalBundle d h).1
    VectorBundleZeroSection.scheme U d
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ≅
        (pullback.diagonal h).ker.normalCone :=
  (chartNormal_model_exists d h).exists.choose

/-- The ordered conormal frame: dx_i is carried back along [y(a)-x(a)] -> da.
Both isomorphisms are uniquely determined by their displayed generator formulas.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartConormalFrame {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    SheafOfModules.free (R := U.ringCatSheaf) (ULift.{u} (Fin d)) ≅
      ConormalGradedAlgebra.piece (pullback.diagonal h) 1 :=
  (chartCoordinateDifferentialFrame d h u w).exists.choose ≪≫
    (chartDiagonalConormal_differentials h).exists.choose.symm

/-- Degree-one functions on Spec Sym(I/I²) in the ordered conormal frame.
This is homOfVector of the symmetric-algebra generators, not a chosen scheme iso.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartConormalCoordinateMap {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    [IsNoetherian U] (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    [SmoothOfRelativeDimension d h] [QuasiCompact h]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    letI := (chartDiagonalNormalBundle d h).1
    VectorBundleZeroSection.scheme U d
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1) ⟶
        AffineSpace (ULift.{u} (Fin d)) U :=
  letI := (chartDiagonalNormalBundle d h).1
  AffineSpace.homOfVector
    (VectorBundleZeroSection.π U d (ConormalGradedAlgebra.piece (pullback.diagonal h) 1))
    fun i ↦ (VectorBundleZeroSection.algebraIso U d
      (ConormalGradedAlgebra.piece (pullback.diagonal h) 1)).hom.right.hom.app (Opposite.op ⊤)
        ((SymmetricAlgebraSheaf.inclusion
          (ConormalGradedAlgebra.piece (pullback.diagonal h) 1)).val.app (Opposite.op ⊤)
            ((chartConormalFrame d h u w).hom.val.app (Opposite.op ⊤)
              ((SheafOfModules.ιFree (R := U.ringCatSheaf) i).val.app (Opposite.op ⊤)
                (1 : U.ringCatSheaf.obj.obj (Opposite.op ⊤)))))

/-- Actual normal-cone coordinates: the canonical conormal model followed by the
ordered differential frame. In particular no arbitrary zero-preserving bundle map occurs.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartNormalCoordinateMap {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    [IsNoetherian U] (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    [SmoothOfRelativeDimension d h] [QuasiCompact h]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    (pullback.diagonal h).ker.normalCone ⟶ AffineSpace (ULift.{u} (Fin d)) U :=
  (chartNormalModel d h).inv ≫ chartConormalCoordinateMap d h u w

/-- The constructed coordinates identify projection and zero, including the empty frame.
Source: chart proof, Step 2 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: chartNormal_model_exists identifies the selected model with the relative Spec of
Sym(I/I²) -> gr(I), normalized by a -> a/t on Rees charts. The conormal-differential iso
and chartCoordinateDifferentialFrame give the ordered degree-one generators. On each
frame Sym is the polynomial algebra, so homOfVector is invertible. The degree-zero
structure map gives the projection equality, and augmentation kills every generator,
giving the zero equality. For d=0 this is the empty polynomial algebra and identity. -/
theorem chartNormalCoordinateMap_spec {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    [IsNoetherian U] (d : ℕ) (h : U ⟶ V) [IsSeparated h]
    [SmoothOfRelativeDimension d h] [QuasiCompact h]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    IsIso (chartNormalCoordinateMap d h u w) ∧
    chartNormalCoordinateMap d h u w ≫ (AffineSpace (ULift.{u} (Fin d)) U ↘ U) =
      Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ∧
    (pullback.diagonal h).normalConeZeroSection ≫ chartNormalCoordinateMap d h u w =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) U := by
  sorry

/-- Canonical restriction of a section invariant through an etale map over its base.
The map is the normalized exceptional-adjunction mate pulled back to the section,
with the two pullback-composition constraints explicitly included.
Source: chart proof, Step 3 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartSectionEtaleRestriction (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {W X B : Scheme.{u}} [IsNoetherian W] [IsNoetherian X] [IsNoetherian B]
    (e : W ⟶ X) [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (f : X ⟶ B) (q : W ⟶ B) [HasCompactification f] [HasCompactification q]
    (w : e ≫ f = q) (s : B ⟶ X) (s' : B ⟶ W) (hs : s' ≫ e = s) :
    Etale.sectionInvariant P.Coefficient f s ≅ Etale.sectionInvariant P.Coefficient q s' :=
  letI : HasCompactification (e ≫ f) := HasCompactification.of_eq w.symm
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) s' e s hs.symm).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) s').leftDerivedFunctor.mapIso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} P.Coefficient) e).app _ ≪≫
        (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N e f).app (𝟙_ _) ≪≫
        eqToIso (by cases w; rfl))

/-- The standard zero-section invariant, before site comparison. Compactifiability
is derived from the finite-type base, not supplied as additional data.
Source: chart proof, Step 3 (blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartStandardSection (P : PurityFiniteSetting.{u}) (B : Scheme.{u}) (d : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :=
  letI := Dnc.compactifiable P (AffineSpace (ULift.{u} (Fin d)) B ↘ B) aB
  Etale.sectionInvariant P.Coefficient (AffineSpace (ULift.{u} (Fin d)) B ↘ B)
    (AffineSpace.zeroSection (ULift.{u} (Fin d)) B)

/-- Coordinate differences preserve the first projection, including after restriction.
Source: chart proof, Step 1 (blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: chartCoordinateDifferences is homOfVector with base map the first projection.
Its projection composite is therefore that base map by homOfVector_over. Precompose
with the open inclusion and reassociate. The argument does not require d positive. -/
theorem chartCoordinateDifferences_over {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) (O : (pullback h h).Opens) :
    (O.ι ≫ chartCoordinateDifferences d h u) ≫
        (AffineSpace (ULift.{u} (Fin d)) U ↘ U) = O.ι ≫ pullback.fst h h := by
  sorry

/-- Source coordinates on the actual diagonal section invariant. First restrict to
O, then use the normalized etale restriction along its coordinate-difference map.
The Cartesian zero square fixes the section comparison, and no purity arrow is used.
Source: chart proof, Steps 1 and 3
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartSourceCoordinateComparison (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    (O : (pullback h h).Opens) (s : U ⟶ O.toScheme)
    (hs : s ≫ O.ι = pullback.diagonal h)
    (hc : Etale (O.ι ≫ chartCoordinateDifferences d h u))
    (sq : IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h u)
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) U))
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    Dnc.sourceSection P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.obj
          (P.chartStandardSection U d (h ≫ aV)) :=
  letI := P.noetherian aV
  letI := P.noetherian (h ≫ aV)
  letI := P.noetherian (pullback.fst h h ≫ (h ≫ aV))
  letI := P.noetherian ((O.ι ≫ pullback.fst h h) ≫ (h ≫ aV))
  letI := Dnc.compactifiable P (pullback.fst h h) (h ≫ aV)
  letI := Dnc.compactifiable P (O.ι ≫ pullback.fst h h) (h ≫ aV)
  letI := Dnc.compactifiable P (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (h ≫ aV)
  letI := P.noetherian ((AffineSpace (ULift.{u} (Fin d)) U ↘ U) ≫ (h ≫ aV))
  letI := hc
  letI : IsSeparated ((O.ι ≫ chartCoordinateDifferences d h u) ≫
      (AffineSpace (ULift.{u} (Fin d)) U ↘ U)) :=
    (chartCoordinateDifferences_over d h u O).symm ▸
      inferInstanceAs (IsSeparated (O.ι ≫ pullback.fst h h))
  letI := IsSeparated.of_comp (O.ι ≫ chartCoordinateDifferences d h u)
    (AffineSpace (ULift.{u} (Fin d)) U ↘ U)
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.chartSectionEtaleRestriction N O.ι (pullback.fst h h)
            (O.ι ≫ pullback.fst h h) rfl (pullback.diagonal h) s hs ≪≫
          (P.chartSectionEtaleRestriction N (O.ι ≫ chartCoordinateDifferences d h u)
            (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (O.ι ≫ pullback.fst h h)
            (chartCoordinateDifferences_over d h u O)
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) U) s
            (sq.w.trans (Category.id_comp _))).symm)

/-- Normal coordinates on the actual normal-section invariant, using the conormal
model and the ordered differential frame, followed by normalized etale locality.
Source: chart proof, Steps 2 and 3
(blueprint: lem-pur-diagonal-dnc-chart-normalization). -/
def chartNormalCoordinateComparison (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    Dnc.normalSection P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h)
        (pullback.diagonal_fst h) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.obj
          (P.chartStandardSection U d (h ≫ aV)) :=
  letI := P.noetherian (h ≫ aV)
  letI : SmoothOfRelativeDimension d
      (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h)) :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst h)).smoothOfRelativeDimension_proj
  letI := Dnc.normalQuasiCompact d (pullback.fst h h)
    (pullback.diagonal h) (pullback.diagonal_fst h)
  letI := Dnc.normalCompactifiable P d (pullback.fst h h) (h ≫ aV)
    (pullback.diagonal h) (pullback.diagonal_fst h)
  letI := P.noetherian
    (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h) ≫ (h ≫ aV))
  letI := Dnc.compactifiable P (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (h ≫ aV)
  letI := P.noetherian ((AffineSpace (ULift.{u} (Fin d)) U ↘ U) ≫ (h ≫ aV))
  letI := (chartNormalCoordinateMap_spec d h u w).1
  Dnc.normalComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h)
      (pullback.diagonal_fst h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.chartSectionEtaleRestriction N (chartNormalCoordinateMap d h u w)
          (AffineSpace (ULift.{u} (Fin d)) U ↘ U)
          (Scheme.Hom.normalConeProj (pullback.fst h h) (pullback.diagonal h))
          (chartNormalCoordinateMap_spec d h u w).2.1
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) U)
          (pullback.diagonal h).normalConeZeroSection
          (chartNormalCoordinateMap_spec d h u w).2.2).symm

/-- Delta is the identity of the standard pair in the actual source and normal
coordinate comparisons. The same assertion includes d=0 with its empty frame.
Source: chart proof, Steps 1--3
(blueprint: lem-pur-diagonal-dnc-chart-normalization).

Proof: take any centred neighbourhood from chartCoordinateDifferences_neighbourhood.
The source comparison is its open restriction followed by the etale exceptional mate.
The actual normal comparison is relative Spec of the canonical symmetric comparison,
the homogeneous-normalized Rees isomorphism, and the ordered differential frame.
Its degree-one coordinates are the classes of y_i-x_i, hence the DNC coordinates
are (y_i-x_i)/t. The etale map of deformations carries both endpoint comparisons
to the same standard zero-section invariant. The standard-family comparison is the
identity at t=1; uniqueness in thm-pur-dnc-invariance forces identity at t=0 in
these very comparisons. This gives the displayed conjugation equation. Restriction
uses these same etale mates and homogeneous generators, so any centred neighbourhood
and normalized compact-support presentation gives the same result. At d=0 the
empty symmetric algebra is O_U, the centred etale zero square is the identity
pair, and all three displayed factors give the identity with their unit constraints. -/
theorem chartDiagonalDelta_coordinate_identity (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [Etale u] [IsSeparated u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h)
    (O : (pullback h h).Opens) (s : U ⟶ O.toScheme)
    (hs : s ≫ O.ι = pullback.diagonal h)
    (hc : Etale (O.ι ≫ chartCoordinateDifferences d h u))
    (sq : IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h u)
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) U))
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    (P.chartSourceCoordinateComparison d h aV u O s hs hc sq N).symm ≪≫
      P.chartDiagonalDelta d h aV ≪≫ P.chartNormalCoordinateComparison d h aV u w N =
        Iso.refl _ := by
  sorry

end WeilConjectures.PurityFiniteSetting
