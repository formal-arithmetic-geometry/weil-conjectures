/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LegacySitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.PurAdicReconstruction
public import WeilConjectures.AlgebraicGeometry.RationalSmoothPurityCanonical
public import WeilConjectures.AlgebraicGeometry.CoefficientDuality
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.OrientedPerfectDuality
public import WeilConjectures.AlgebraicGeometry.SixFunctorDatum
public import WeilConjectures.AlgebraicGeometry.OrientationCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.SixFunctorOrientationFiniteFamily
public import WeilConjectures.AlgebraicGeometry.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.FiniteReductionRootCharts

import WeilConjectures.AlgebraicGeometry.FiniteCoefficientSmoothPurity
import WeilConjectures.AlgebraicGeometry.FiniteReductionOfPurity
import WeilConjectures.AlgebraicGeometry.CoefficientFrobenius
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor

/-! # Normalized orientation, trace and independent perfect evaluation

Source: main-20261015, sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md,
clause (6) and the point/site-perfect part of (7)
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).

The inverse comparison retains the forward purity map, rather than choosing an
isomorphism of its endpoints. Point duality uses derived Hom at integral coefficients.
The closed structures in the site-perfect clause are asserted construction data only; no
SixFunctorDatum, general geometric biduality, or orientation datum is a hypothesis.

## Main definitions and statement
* `sfPackageNormalizedOrientationPerfectDuality`: the complete package below.
* `SfPackageFiniteOrientationTrace`: the finite maps, inverses and quotient squares.
* `SfPackageIntegralOrientation`: the strict reconstructed map and inverse reductions.
* `SfPackageIntegralOrientationTrace`: the reconstructed map, its trace and lattice realization.
* `SfPackageRationalOrientationTrace`: rationalization of that same trace.
* `SfPackageFieldOrientationTrace`: the three finite-field extension equations.
* `SfPackageCommonOrientation`: the common-stage inverse and counit trace.
* `SfPackagePointEvaluation`: independent coefficient double-dual evaluation.
* `SfPackageSmoothSitePerfect`: the evaluation identification on site-perfect inputs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u a b v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
attribute [local irreducible] purAdicSource
  RationalSmoothPurityCanonical.integralSource

/-- The objectwise content of the identification of oriented double duality with
coefficient double duality. Theta and cancellation are fixed by their actual maps;
the final equality is an equality of evaluation transposes, not an unspecified iso.
Source: clause (7), local perfect-complex evaluation
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
def SfPackagePerfectEvaluation {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (M : CoefficientClosedStructure H) (s : @SymmetricCategory B _ M.monoidal)
    {L W : B} (gamma : L ≅ W) (K : B) : Prop :=
  IsIso (ringedSiteBidual M s W K) ∧
  IsIso (ringedSiteBidual M s M.monoidal.tensorUnit K) ∧
  ∃ theta : H.obj (op K, W) ≅ M.tensor.obj (H.obj (op K, M.monoidal.tensorUnit), L),
    theta.inv = sfPerfectThetaInverse M s gamma K ∧
    ∃ c : H.obj (op (H.obj (op K, M.monoidal.tensorUnit)), M.monoidal.tensorUnit) ≅
        H.obj (op (M.tensor.obj (H.obj (op K, M.monoidal.tensorUnit), L)), L),
      c.hom = sfPerfectLineCancellation M (H.obj (op K, M.monoidal.tensorUnit)) L ∧
      ringedSiteBidual M s W K ≫
        (((Functor.curry.obj H).flip.obj W).mapIso theta.op).inv ≫
        H.map (Prod.mkHom (𝟙 _) gamma.inv) ≫ c.inv =
          ringedSiteBidual M s M.monoidal.tensorUnit K

section Finite
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- Finite purity with its specified inverse, counit trace and all finite quotient squares.
Source: clause (6), finite coefficients
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: apply finite smooth purity to gamma and take its inverse. The trace is its
compact-support image followed by the exceptional counit. Finite reduction of purity
and of smooth trace gives the two forward squares. Multiply the purity square by
both inverses to obtain the inverse square; no quotient-flatness is used. -/
def SfPackageFiniteOrientationTrace (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) : Prop :=
    ∃ e : _ ≅ _, e.hom = P.smoothPurityMap f d K hK ∧
      P.coefficientValuedSmoothTrace f d K hK =
        (P.smoothCompactSupport f).map e.hom ≫ P.smoothExceptionalCounit f K ∧
      ∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level),
        ∃ e' : _ ≅ _,
          e'.hom = (P.finiteReductionSetting m hm).smoothPurityMap f d
            ((P.finiteReduction m hm hmn Y).obj K)
            (P.finiteReduction_preserves_ctf m hm hmn Y K hK) ∧
          (P.finiteReduction m hm hmn X).map e.hom ≫
              P.finiteReductionExceptionalComparison m hm hmn f d K hK =
            (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫ e'.hom ∧
          (P.finiteReduction m hm hmn X).map e.inv ≫
              (P.finiteReductionSourceComparison m hm hmn f d K).hom =
            P.finiteReductionExceptionalComparison m hm hmn f d K hK ≫ e'.inv ∧
          (P.finiteReduction m hm hmn Y).map
              (P.coefficientValuedSmoothTrace f d K hK) =
            P.finiteReductionCompactSupportComparison m hm hmn f
                ((P.compositionShiftedPullback f d).obj K) ≫
              ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
                (P.finiteReductionSourceComparison m hm hmn f d K).hom ≫
              (P.finiteReductionSetting m hm).coefficientValuedSmoothTrace f d
                ((P.finiteReduction m hm hmn Y).obj K)
                (P.finiteReduction_preserves_ctf m hm hmn Y K hK)
end Finite

section Integral
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- Every integral constructible input is admissible and its reconstructed inverse
orientation has exactly the specified finite reductions. No uniqueness of a lift is claimed.
Source: clause (6), integral reconstruction
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: integral residue Tor identifies the full integral constructible category with
the uniform finite-Tor category. Apply adic reconstruction to obtain gamma from a
strict-tower morphism, and invert it. Its source and target reduction comparisons are
invertible by normalized effectivity. Inverting their forward square gives the displayed
inverse square. This construction uses the same reconstructed family at every level. -/
def SfPackageIntegralReconstruction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hTor : finiteTorConstructibleIntegral C.l E Y K)
    (e : purAdicSource D C E f d K ≅ purAdicTarget D C E f K) : Prop :=
    (∃ G : (coefficientSequenceDerivedRestriction C.l E X).obj
        ((pullbackTensorCalculus C.l E X).reduction.obj (purAdicSource D C E f d K)) ⟶
      (coefficientSequenceDerivedRestriction C.l E X).obj
        ((integralExceptionalSystem C.l E D C.different f).obj K),
      e.hom = (pullbackTensorCalculus C.l E X).adjunction.unit.app _ ≫
        (coefficientConstantTowerLimit C.l E X).map G ∧
      ∀ n : ℕ,
        (coefficientConstantTowerEvaluation C.l E X n).map G ≫
          (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
          (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
            (purAdicExceptionalEvaluation D C E f K n).hom =
        (purAdicRestrictedEvaluation C.l E X n).hom.app _ ≫
          (scalarReductionRestriction C.l E X n).mapDerivedCategory.map
            (((pullbackTensorCalculus C.l E X).reductionEvaluation n).hom.app _ ≫
              purAdicSourceReduction D C E f d K hTor n ≫
              (purAdicFiniteArrow D C E f d K hTor n).hom)) ∧
    ∀ n : ℕ, ∃ e' : (purAdicFiniteArrow D C E f d K hTor n).left ≅
        (purAdicFiniteArrow D C E f d K hTor n).right,
      e'.hom = (purAdicFiniteArrow D C E f d K hTor n).hom ∧
      IsIso (purAdicSourceReduction D C E f d K hTor n) ∧
      IsIso (purAdicTargetReduction D C E f d K hTor n) ∧
      (scalarReductionDerivedExtension C.l E X n).map e.hom ≫
          purAdicTargetReduction D C E f d K hTor n =
        purAdicSourceReduction D C E f d K hTor n ≫
          (purAdicFiniteArrow D C E f d K hTor n).hom ∧
      (scalarReductionDerivedExtension C.l E X n).map e.inv ≫
          purAdicSourceReduction D C E f d K hTor n =
        purAdicTargetReduction D C E f d K hTor n ≫
          e'.inv

attribute [local irreducible] purAdicTarget

/-- Every integral constructible input admits the specified strict reconstructed comparison.
Source: clause (6), integral reconstruction
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
def SfPackageIntegralOrientation (K : DerivedCategory (scalarReductionSource C.l E Y))
    (_hK : sfIntegralConstructible C.l E Y K) : Prop :=
  ∃ hTor : finiteTorConstructibleIntegral C.l E Y K,
    ∃ e : purAdicSource D C E f d K ≅ purAdicTarget D C E f K,
      SfPackageIntegralReconstruction D C E f d K hTor e

attribute [local irreducible] PurCompactSupport.image PurCompactSupport.comparison
  PurCompactSupport.finiteImageIso PurCompactSupport.finiteReductionIso
  scalarReductionExistence scalarReductionDerivedExistence HasDerivedCategory.standard

/-- Reduction of the counit trace of the very same reconstructed comparison, at every
positive exponent. The finite-stage package additionally records its purity, inverse,
and trace squares for every further quotient, including the identity quotient.
Source: clause (6), integral trace reduction
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
def SfPackageIntegralTraceReduction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hTor : finiteTorConstructibleIntegral C.l E Y K)
    (t : (PurCompactSupport.image (PurCompactSupport.completed C.l E)
      (integralExceptionalCompactification D f)).obj (purAdicSource D C E f d K) ⟶ K) :
    Prop :=
  ∀ n : ℕ,
    (scalarReductionDerivedExtension C.l E Y n).map t =
      (PurCompactSupport.finiteReductionIso C.l E Y n).inv.app
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E)
          (integralExceptionalCompactification D f)).obj (purAdicSource D C E f d K)) ≫
      (PurCompactSupport.comparison
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
        (integralExceptionalCompactification D f)).app (purAdicSource D C E f d K) ≫
      (PurCompactSupport.finiteImageIso C.l E n
        (integralExceptionalCompactification D f)).hom.app _ ≫
      ((purAdicFiniteSetting D C E n).smoothCompactSupport f).map
        ((PurCompactSupport.finiteReductionIso C.l E X n).hom.app (purAdicSource D C E f d K) ≫
          purAdicSourceReduction D C E f d K hTor n) ≫
      (purAdicFiniteSetting D C E n).coefficientValuedSmoothTrace f d
        ((scalarReductionDerivedExtension C.l E Y n).obj K)
        (purAdicReductionFiniteTor D C E Y K hTor n) ∧
    SfPackageFiniteOrientationTrace (purAdicFiniteSetting D C E n) f d
      ((scalarReductionDerivedExtension C.l E Y n).obj K)
      (purAdicReductionFiniteTor D C E Y K hTor n)

/-- The exceptional target realization preserves the actual finite counits. This is
precisely the scalar-adjoint normalization of the exceptional comparison, expressed
without unfolding its restricted scalar functors.
Source: clause (6), coefficient-counit reduction
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
def SfPackageIntegralCounitReduction
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hTor : finiteTorConstructibleIntegral C.l E Y K)
    (epsilon : (PurCompactSupport.image (PurCompactSupport.completed C.l E)
      (integralExceptionalCompactification D f)).obj (purAdicTarget D C E f K) ⟶ K) :
    Prop :=
  ∀ n : ℕ,
    (scalarReductionDerivedExtension C.l E Y n).map epsilon =
      (PurCompactSupport.finiteReductionIso C.l E Y n).inv.app
        ((PurCompactSupport.image (PurCompactSupport.completed C.l E)
          (integralExceptionalCompactification D f)).obj (purAdicTarget D C E f K)) ≫
      (PurCompactSupport.comparison
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
        (integralExceptionalCompactification D f)).app (purAdicTarget D C E f K) ≫
      (PurCompactSupport.finiteImageIso C.l E n
        (integralExceptionalCompactification D f)).hom.app _ ≫
      ((purAdicFiniteSetting D C E n).smoothCompactSupport f).map
        ((PurCompactSupport.finiteReductionIso C.l E X n).hom.app (purAdicTarget D C E f K) ≫
          purAdicTargetReduction D C E f d K hTor n) ≫
      (purAdicFiniteSetting D C E n).smoothExceptionalCounit f
        ((scalarReductionDerivedExtension C.l E Y n).obj K)

end Integral

/-- Evaluate the recorded functor with its category parameters inferred from the
functor itself, rather than synthesized again from the coefficient object type.
Source: clause (6), native coefficient-category presentations
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
abbrev sfPackageFunctorObject {B : Type a} {C : Type b}
    {bcat : Category.{v} B} {ccat : Category.{w} C}
    (F : @CategoryTheory.Functor B bcat C ccat) (K : B) : C :=
  @CategoryTheory.Functor.obj B bcat C ccat F K

/-- Map in the category presentations recorded by the functor.
Source: clause (6), native coefficient-category presentations
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
abbrev sfPackageFunctorMap {B : Type a} {C : Type b}
    {bcat : Category.{v} B} {ccat : Category.{w} C}
    (F : @CategoryTheory.Functor B bcat C ccat) {K L : B}
    (t : @Quiver.Hom B bcat.toQuiver K L) :
    @Quiver.Hom C ccat.toQuiver (sfPackageFunctorObject F K) (sfPackageFunctorObject F L) :=
  @CategoryTheory.Functor.map B bcat C ccat F K L t

/-- The forward map in the category presentation recorded by the isomorphism.
Source: clause (6), native coefficient-category presentations
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
abbrev sfPackageIsoHom {B : Type a} {cat : Category.{v} B} {K L : B}
    (e : @Iso B cat K L) : @Quiver.Hom B cat.toQuiver K L :=
  @Iso.hom B cat K L e

/-- The inverse map in the category presentation recorded by the isomorphism.
Source: clause (6), native coefficient-category presentations
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
abbrev sfPackageIsoInv {B : Type a} {cat : Category.{v} B} {K L : B}
    (e : @Iso B cat K L) : @Quiver.Hom B cat.toQuiver L K :=
  @Iso.inv B cat K L e

/-- A component in the category presentations recorded by the natural transformation.
Source: clause (6), native coefficient-category presentations
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
abbrev sfPackageNatTransApp {B : Type a} {C : Type b}
    {bcat : Category.{v} B} {ccat : Category.{w} C}
    {F G : @CategoryTheory.Functor B bcat C ccat}
    (t : @CategoryTheory.NatTrans B bcat C ccat F G) (K : B) :
    @Quiver.Hom C ccat.toQuiver (sfPackageFunctorObject F K) (sfPackageFunctorObject G K) :=
  @CategoryTheory.NatTrans.app B bcat C ccat F G t K

/-- An isomorphism component with its recorded category presentations.
Source: clause (6), native coefficient-category presentations
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
abbrev sfPackageIsoApp {B : Type a} {C : Type b}
    {bcat : Category.{v} B} {ccat : Category.{w} C}
    {F G : @CategoryTheory.Functor B bcat C ccat}
    (e : @Iso (@CategoryTheory.Functor B bcat C ccat)
      (@CategoryTheory.Functor.category B bcat C ccat) F G) (K : B) :
    @Iso C ccat (sfPackageFunctorObject F K) (sfPackageFunctorObject G K) :=
  @CategoryTheory.Iso.app B bcat C ccat F G e K

/-- Compose in an explicitly recorded coefficient-category presentation.
Source: clause (6), native coefficient-category presentations
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
abbrev sfPackageCompose {B : Type a} (cat : Category.{v} B) {K L M : B}
    (t : @Quiver.Hom B cat.toQuiver K L) (s : @Quiver.Hom B cat.toQuiver L M) :
    @Quiver.Hom B cat.toQuiver K M :=
  @CategoryStruct.comp B cat.toCategoryStruct K L M t s

section Fields
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))
  (d : ℕ) [SmoothOfRelativeDimension d f]
open RationalSmoothPurityCanonical

attribute [local irreducible] PurCompactSupport.image
  RationalSmoothPurityCanonical.integralMap
  RationalSmoothPurityCanonical.rationalIso
  RationalSmoothPurityCanonical.commonIso
  RationalSmoothPurityCanonical.smallModelIso

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedPullback commonStageDerivedTensor sfRationalScalarExtension
  RationalSmoothPurityCanonical.rationalSource
  RationalSmoothPurityCanonical.sourceScalar
  RationalSmoothPurityCanonical.rationalSourceComparison
  RationalSmoothPurityCanonical.commonSource
  RationalSmoothPurityCanonical.commonSourceComparison

/-- The ordinary support coordinates of the actual integral exceptional counit trace.
Source: clause (6), integral counit trace
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
@[irreducible]
def sfPackageIntegralCounitTrace
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
      c).obj (integralSource P f d K).obj ⟶ K.obj :=
  (S.ring.left c (.integral (AdicSmoothDualizing.fieldStage P))).inv.app
      (integralSource P f d K) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι.map
      ((operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).F.map
          (integralMap P f c S d K) ≫
        (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app K)

/-- The actual operation counit in the reconstructed target's coordinates.
The following predicate normalizes this realization by its full finite counit square.
Source: clause (6), integral exceptional counit
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
@[irreducible]
def sfPackageReconstructedIntegralCounit
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y)
    (b : purAdicTarget P.field P.coefficients P.extension f K.obj ≅
      ((operation P f (integralExceptionalCompactification P.field f) S
        (.integral (AdicSmoothDualizing.fieldStage P))).G.obj K).obj) :
    (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
      (integralExceptionalCompactification P.field f)).obj
        (purAdicTarget P.field P.coefficients P.extension f K.obj) ⟶ K.obj :=
  (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
    (integralExceptionalCompactification P.field f)).map b.hom ≫
  (S.ring.left (integralExceptionalCompactification P.field f)
    (.integral (AdicSmoothDualizing.fieldStage P))).inv.app
      ((operation P f (integralExceptionalCompactification P.field f) S
        (.integral (AdicSmoothDualizing.fieldStage P))).G.obj K) ≫
  (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι.map
    ((operation P f (integralExceptionalCompactification P.field f) S
      (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app K)

/-- The trace of the strict reconstructed map itself, using the normalized target
realization and the operation datum's actual exceptional counit. Its source is the
original adic source; no independent trace map is selected.
Source: clause (6), counit trace of the reconstructed comparison
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
@[irreducible]
def sfPackageReconstructedIntegralTrace
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y)
    (eR : purAdicSource P.field P.coefficients P.extension f d K.obj ≅
      purAdicTarget P.field P.coefficients P.extension f K.obj)
    (b : purAdicTarget P.field P.coefficients P.extension f K.obj ≅
      ((operation P f (integralExceptionalCompactification P.field f) S
        (.integral (AdicSmoothDualizing.fieldStage P))).G.obj K).obj) :
    (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
      (integralExceptionalCompactification P.field f)).obj
        (purAdicSource P.field P.coefficients P.extension f d K.obj) ⟶ K.obj :=
  (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
    (integralExceptionalCompactification P.field f)).map eR.hom ≫
    sfPackageReconstructedIntegralCounit P f S K b

/-- Integral purity and its general-input counit trace are jointly realized by one strict
reconstruction witness. The source and target identifications link the constructed lattice
map to that witness by an equality of actual morphisms. Pulling its counit trace to the
reconstructed source gives exactly the finite traces through the canonical support and
source comparisons, and these finite traces obey all further-quotient squares.
Source: clause (6), integral trace and lattice normalization
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: integral residue Tor admits every input. Use the simultaneous normalized integral
family of lem-sf-normalized-integral-purity-trace, with its strict reconstruction witness.
Transport its completed tensor source and exceptional target into the operation datum's
coordinates. The trace-transpose construction identifies integralMap with this same map.
Apply the exceptional counit after support pushforward. Its normalized scalar mate and
source reduction give Q(t_R) = c ; P(a) ; t_n for every input and exponent. Finite reduction
of purity and trace gives all further quotients, preserving the coefficient counits. -/
def SfPackageIntegralOrientationTrace
    (K : sfIntegralConstructibleCategory P.coefficients.l P.extension Y) : Prop :=
  ∃ hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y K.obj,
    ∃ eR : purAdicSource P.field P.coefficients P.extension f d K.obj ≅
        purAdicTarget P.field P.coefficients P.extension f K.obj,
      SfPackageIntegralReconstruction P.field P.coefficients P.extension f d K.obj hK eR ∧
      ∃ s : purAdicSource P.field P.coefficients P.extension f d K.obj ≅
          (integralSource P f d ⟨K.obj, hK⟩).obj,
        ∃ b : purAdicTarget P.field P.coefficients P.extension f K.obj ≅
            ((operation P f (integralExceptionalCompactification P.field f) S
              (.integral (AdicSmoothDualizing.fieldStage P))).G.obj ⟨K.obj, hK⟩).obj,
          s.hom ≫ (integralMap P f (integralExceptionalCompactification P.field f) S d
              ⟨K.obj, hK⟩).hom = eR.hom ≫ b.hom ∧
          SfPackageIntegralCounitReduction P.field P.coefficients P.extension f d K.obj hK
            (sfPackageReconstructedIntegralCounit P f S ⟨K.obj, hK⟩ b) ∧
          ∃ e : (operation P f (integralExceptionalCompactification P.field f) S
              (.integral (AdicSmoothDualizing.fieldStage P))).G.obj ⟨K.obj, hK⟩ ≅
              integralSource P f d ⟨K.obj, hK⟩,
            e.inv = integralMap P f (integralExceptionalCompactification P.field f) S d
              ⟨K.obj, hK⟩ ∧
            sfPackageReconstructedIntegralTrace P f S d ⟨K.obj, hK⟩ eR b =
              (PurCompactSupport.image
                (PurCompactSupport.completed P.coefficients.l P.extension)
                (integralExceptionalCompactification P.field f)).map s.hom ≫
                sfPackageIntegralCounitTrace P f (integralExceptionalCompactification P.field f)
                  S d ⟨K.obj, hK⟩ ∧
            SfPackageIntegralTraceReduction P.field P.coefficients P.extension f d K.obj hK
              (sfPackageReconstructedIntegralTrace P f S d ⟨K.obj, hK⟩ eR b)

attribute [local irreducible] ScalarLocalization.category SheafOfModules.instAbelian
  SheafOfModules.instCategory scalarReductionSourceDerived

/-- The specified rational purity map and its inverse, with the trace of the chosen
integral lattice. The comparison is the counit-preserving rationalization comparison.
Source: clause (6), rational coefficients
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: rationalize the normalized integral trace transpose and compose with the
canonical source and exceptional comparisons. This is rationalIso by definition.
Apply the counit equation to identify its trace with the rationalized integral trace.
Inverting the equality gives the inverse orientation on the same lattice. -/
def SfPackageRationalOrientationTrace
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) : Prop :=
  let CY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y (.rational (AdicSmoothDualizing.fieldStage P))
  let H := rationalSource P.coefficients.l P.extension f d
  let A := operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))
  let gamma := rationalIso P f c S d K
  let source := rationalSourceComparison P f d K
  let q := (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).q
  let RY := ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P) Y
  let lattice := representative P K
  let latticeSource := integralSource P f d lattice
  let trace := integralTraceTranspose P f c S d lattice
  ∃ e : @Iso _ (ConstructibleExceptionalCoefficients.category P.coefficients.l
        P.coefficients.Qbar X (.rational (AdicSmoothDualizing.fieldStage P)))
      (sfPackageFunctorObject A.G K)
      (sfPackageFunctorObject H K),
    e = (@Iso.symm _ _ _ _ gamma) ∧
    sfPackageCompose CY (sfPackageFunctorMap A.F (sfPackageIsoInv e))
      (sfPackageNatTransApp A.adjunction.counit K) =
      sfPackageCompose CY (sfPackageFunctorMap A.F (sfPackageIsoHom source))
        (sfPackageCompose CY (sfPackageIsoInv (sfPackageIsoApp q latticeSource))
          (sfPackageCompose CY (sfPackageFunctorMap RY trace)
            (@eqToHom _ CY.toCategoryStruct _ _ (representative_eq P K))))

attribute [local instance 1000] IntermediateField.algebra'
attribute [local instance 1000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] ConstructibleExceptionalCoefficients.FieldComparison.b
  ConstructibleExceptionalCoefficients.FieldComparison.q
  AlgebraicGeometry.Scheme.ProEt AlgebraicGeometry.Scheme.instCategoryProEt
  AlgebraicGeometry.Scheme.ProEt.precoverage
  completedIntegralCommRingSheafUnrestricted

/-- Purity, inverse purity and trace commute with every finite field enlargement.
Source: clause (6), coefficient-field transport
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: scalar naturality of the normalized integral family gives the forward square
on the unit, then on lattices by projection. Rationalize and apply rationalIso_scalar.
Multiply by inverses for the second square. Naturality of the support comparison and
the exceptional counit identity give the third square. -/
def SfPackageFieldOrientationTrace
    (L : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (a : P.extension →ₐ[Padic P.coefficients.l] L.val)
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) : Prop :=
  let CY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y (.rational (AdicSmoothDualizing.fieldStage P))
  let DX := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar X (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
  let DY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
  let A := operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))
  let B := operation (stageSetting P L) f c S
    (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
  let TX := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
    (AdicSmoothDualizing.fieldStage (stageSetting P L)) a X
  let TY := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
    P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
    (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y
  let gamma := rationalIso P f c S d K
  let gamma' := rationalIso (stageSetting P L) f c S d (sfPackageFunctorObject TY K)
  let source := sourceScalar P.coefficients.l P.extension L.val a f d K
  let H := rationalSource P.coefficients.l P.extension f d
  let comparison := S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
    (AdicSmoothDualizing.fieldStage (stageSetting P L)) a
  let b := ConstructibleExceptionalCoefficients.FieldComparison.b
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (X := X) (Y := Y)
    (s := .rational (AdicSmoothDualizing.fieldStage P))
    (t := .rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
    (A := A) (B := B) (TX := TX) (TY := TY) comparison
  let q := ConstructibleExceptionalCoefficients.FieldComparison.q
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (X := X) (Y := Y)
    (s := .rational (AdicSmoothDualizing.fieldStage P))
    (t := .rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
    (A := A) (B := B) (TX := TX) (TY := TY) comparison
  sfPackageCompose DX (sfPackageFunctorMap TX (sfPackageIsoHom gamma))
      (sfPackageIsoHom (sfPackageIsoApp b K)) =
    sfPackageCompose DX (sfPackageIsoHom source) (sfPackageIsoHom gamma') ∧
  sfPackageFunctorMap TY
    (sfPackageCompose CY (sfPackageFunctorMap A.F (sfPackageIsoHom gamma))
      (sfPackageNatTransApp A.adjunction.counit K)) =
    sfPackageCompose DY (sfPackageIsoHom (sfPackageIsoApp q (sfPackageFunctorObject H K)))
      (sfPackageCompose DY (sfPackageFunctorMap B.F (sfPackageIsoHom source))
        (sfPackageCompose DY (sfPackageFunctorMap B.F (sfPackageIsoHom gamma'))
          (sfPackageNatTransApp B.adjunction.counit (sfPackageFunctorObject TY K)))) ∧
  sfPackageCompose DX (sfPackageFunctorMap TX (sfPackageIsoInv gamma))
      (sfPackageIsoHom source) =
    sfPackageCompose DX (sfPackageIsoHom (sfPackageIsoApp b K)) (sfPackageIsoInv gamma')

/-- Purity in the literal finite field representing this common-stage object.
This is the published normalized lattice map transported by the fixed field-model
roundtrip; the abbreviation fixes its target before the support functor is elaborated.
Source: clause (6), common-stage presentation
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
@[irreducible]
def sfPackageCommonStagePurity
    (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) :
    @Iso _ (ConstructibleExceptionalCoefficients.category P.coefficients.l
      P.coefficients.Qbar X (.rational (ConstructibleExceptionalCoefficients.commonField
        P.coefficients.l P.coefficients.Qbar K.stage)))
    ((sfPackageFunctorObject (rationalSource P.coefficients.l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
        P.coefficients.Qbar K.stage) f d)) K.obj)
      ((sfPackageFunctorObject (S.ring.operation c (.rational
        (ConstructibleExceptionalCoefficients.commonField
        P.coefficients.l P.coefficients.Qbar K.stage))).G) K.obj) := by
  have e := smallModelIso (stageSetting P K.stage) f c S d K.obj
  dsimp only [stageSetting, AdicSmoothDualizing.fieldIndex,
    commonModelField, commonModelAlgebra, commonModelFinite] at e
  exact e

/-- Transport a morphism between the two inherited presentations of one category.
Source: clause (6), common-stage coefficient presentation; the same transport as
RationalSmoothPurityCanonical.transportIsoCategory on the hom field
(blueprint: lem-sf-package-normalized-orientation-perfect-duality). -/
def sfPackageTransportHomCategory {B : Type a} (cat cat' : Category.{b} B)
    (h : cat = cat') {K L : B} (t : @Quiver.Hom B cat.toQuiver K L) :
    @Quiver.Hom B cat'.toQuiver K L := h ▸ t

/-- The inverse-direction common-stage identification uses the actual finite-stage
representative and the fixed common exceptional comparison.
Source: clause (6), algebraically closed coefficients
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: represent the object and each arrow over a common finite coefficient field.
Use rational purity and its scalar square there. The common-stage cocycle and the
counit-normalized exceptional comparison identify enlargements. This is commonIso;
its inverse is therefore the requested inverse-direction identification. -/
def SfPackageCommonOrientation (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) : Prop :=
  let CX := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar X .closed
  let CY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y .closed
  let DY := ConstructibleExceptionalCoefficients.category P.coefficients.l
    P.coefficients.Qbar Y (.rational (ConstructibleExceptionalCoefficients.commonField
      P.coefficients.l P.coefficients.Qbar K.stage))
  let A := S.ring.operation c .closed
  let B := S.ring.operation c (.rational (ConstructibleExceptionalCoefficients.commonField
    P.coefficients.l P.coefficients.Qbar K.stage))
  let H := commonSource P.coefficients.l P.coefficients.Qbar f d
  let HY := rationalSource P.coefficients.l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
      P.coefficients.Qbar K.stage) f d
  let J := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := Y) K.stage
  let q := (S.common.commonComparison c K.stage).q
  ∃ e : @Iso _ CX (sfPackageFunctorObject A.G K) (sfPackageFunctorObject H K),
    sfPackageIsoInv e = sfPackageIsoHom (commonIso P f c S d K) ∧
    sfPackageCompose CY (sfPackageFunctorMap A.F (sfPackageIsoInv e))
        (sfPackageNatTransApp A.adjunction.counit K) =
      sfPackageCompose CY
        (sfPackageFunctorMap A.F
          (sfPackageIsoHom (commonSourceComparison P.coefficients.l
            P.coefficients.Qbar f d K)))
        (sfPackageCompose CY
          (sfPackageIsoInv (sfPackageIsoApp q (sfPackageFunctorObject HY K.obj)))
          (sfPackageFunctorMap J
            (sfPackageTransportHomCategory _ _ (commonCategory_eq P Y K.stage)
              (sfPackageCompose DY
                (sfPackageFunctorMap B.F (sfPackageIsoHom (sfPackageCommonStagePurity P f c S d K)))
                (sfPackageNatTransApp B.adjunction.counit K.obj)))))

end Fields

/-- Point evaluation at all coefficient stages, with the coefficient ring as
its dualizing object. Integral modules use derived Hom, including torsion modules.
Source: clause (7), independent point duality
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: the finite quotient is self-injective Artinian, so finite-module duality is
exact and evaluation is bijective. At fields use finite-dimensional vector duality.
The DVR has length-one finite-free resolutions of finite modules; assemble these
for bounded cohomology and apply signed finite-projective complex evaluation.
These are the coefficient Frobenius and integral derived-duality results; no
geometric biduality assertion enters. -/
def SfPackagePointEvaluation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (n : ℕ) (_hn : 1 ≤ n)
    [HasDerivedCategory.{u} (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E))]
    [HasDerivedCategory.{u} (ModuleCat.{u} E)]
    [HasDerivedCategory.{u} (ModuleCat.{u} Ω)] : Prop :=
    (∀ M : ModuleCat.{u} (Padic.coefficientExtensionRing l E n),
      Module.Finite (Padic.coefficientExtensionRing l E n) M →
      Function.Bijective (Module.Dual.eval (Padic.coefficientExtensionRing l E n) M)) ∧
    (∀ K : DerivedCategory.{u} (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)),
      boundedFiniteCoefficientComplex (Padic.coefficientExtensionIntegers l E) K →
      IsIso (coefficientDerivedEvaluation K)) ∧
    (∀ K : DerivedCategory.{u} (ModuleCat.{u} E), boundedFiniteCoefficientComplex E K →
      IsIso (coefficientDerivedEvaluation K)) ∧
    (∀ K : DerivedCategory.{u} (ModuleCat.{u} Ω),
      boundedFiniteCoefficientComplex Ω K →
      IsIso (coefficientDerivedEvaluation K))

/-- Site-perfect biduality at the four actual coefficient stages, under the
smooth purity identification. The asserted closed presentations only specify tensor,
Hom and signed evaluation; no general geometric biduality is assumed.
Source: clause (7), smooth site-perfect sentence
(blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: restrict to a covering with a bounded finite-projective model. Dualizing its
terms and the signed differential gives the coefficient dual, and termwise evaluation
is an isomorphism. The opposite Tate line and shift cancel. The inverse theta is the
transpose of coefficient evaluation tensored with the chosen purity orientation.
Naturality of transposition identifies geometric evaluation with coefficient evaluation
through theta and the canonical line-cancellation map. Exact restriction detects
isomorphisms. Integrally the same calculation uses the completed ring. Localize it
at rational coefficients, then pass to a common finite stage for algebraically closed
coefficients. Neither general biduality nor finite-Tor equals site-perfect is used. -/
def SfPackageSmoothSitePerfect {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] (n : ℕ)
    (S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
    (c : Compactification (sixFunctorStructure X).hom.left) : Prop :=
    ∃ (MF : SixFunctorClosedDomain (S.finiteTorDomain X)
      (sixFunctorFiniteHomPairs D C E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X)
      (S.finiteInternalHom X))
    (MI : SixFunctorClosedDomain (S.integralFiniteTorDomain X)
      (constructibleIntegralHomPairs C.l E X.obj.left)
      (constructibleIntegralHom C.l E X.obj.left))
    (MR : SixFunctorClosedDomain (⊤ : ObjectProperty
      (sfRationalConstructibleCategory C.l E X.obj.left))
      (constructibleRationalHomPairs C.l E X.obj.left)
      (rationalDerivedInternalHom C.l E X.obj.left))
    (MC : SixFunctorClosedDomain (⊤ : ObjectProperty
      (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left))
      (commonStageHomPairs C.l C.Qbar X.obj.left)
      (commonStageDerivedInternalHom C.l C.Qbar X.obj.left)),
    (∃ NF : sixFunctorRingedModel.{u, u+1, u} (ProEt.topology X.obj.left)
        ((constantSheaf (ProEt.topology X.obj.left) CommRingCat.{u+1}).obj
          (.of (ULift.{u+1, u} (Padic.coefficientExtensionRing C.l E (n + 1))))),
      Nonempty (SixFunctorAmbientClosedModel MF NF.closed NF.symmetric
        (intrinsicFiniteTorsionConstructible C.l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) X.obj.left).ι)) ∧
    (∃ NI : sixFunctorRingedModel.{u, u+1, u} (ProEt.topology X.obj.left)
        (completedIntegralCommRingSheafUnrestricted C.l E X.obj.left),
      Nonempty (SixFunctorAmbientClosedModel MI NI.closed NI.symmetric
        (sfIntegralConstructible C.l E X.obj.left).ι)) ∧
    Nonempty (SixFunctorClosedChange MI MR
      (sfRationalConstructibleLocalization C.l E X.obj.left)) ∧
    (∃ models : ∀ F : Padic.FiniteCoefficientFields C.l C.Qbar,
        SixFunctorCoefficientClosedModels C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X.obj.left,
      ∀ F : Padic.FiniteCoefficientFields C.l C.Qbar,
        Nonempty (SixFunctorClosedChange (models F).rational MC
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F))) ∧
    (∃ (hL : S.finiteTorDomain X (sfOrientationReducedLine D C E n X d))
      (hW : S.finiteTorDomain X (S.finiteDuality.dualizing X c)),
      Nonempty (sfOrientationReducedLine D C E n X d ≅ S.finiteDuality.dualizing X c) ∧
      ∀ (gamma : sfOrientationReducedLine D C E n X d ≅ S.finiteDuality.dualizing X c)
      (K : (S.finiteTorDomain X).FullSubcategory),
      IsFiniteCoefficientSitePerfect C.l E X.obj.left n K.obj.obj →
      SfPackagePerfectEvaluation MF.closed MF.symmetric
        (ObjectProperty.isoMk (S.finiteTorDomain X)
          (X := ⟨_, hL⟩) (Y := ⟨_, hW⟩) gamma) K) ∧
    (∃ (hL : S.integralFiniteTorDomain X (sfOrientationIntegralLineOn D C E X d))
      (hW : S.integralFiniteTorDomain X (S.higher.integralDuality.dualizing X c)),
      Nonempty (sfOrientationIntegralLineOn D C E X d ≅
        S.higher.integralDuality.dualizing X c) ∧
      ∀ (gamma : sfOrientationIntegralLineOn D C E X d ≅
        S.higher.integralDuality.dualizing X c)
      (K : (S.integralFiniteTorDomain X).FullSubcategory),
      IsIntegralCoefficientSitePerfect C.l E X.obj.left K.obj.obj →
      SfPackagePerfectEvaluation MI.closed MI.symmetric
        (ObjectProperty.isoMk (S.integralFiniteTorDomain X)
          (X := ⟨_, hL⟩) (Y := ⟨_, hW⟩) gamma) K) ∧
    (Nonempty ((sfRationalConstructibleLocalization C.l E X.obj.left).obj
        (sfOrientationIntegralLineOn D C E X d) ≅ S.higher.rationalDuality.dualizing X c) ∧
      ∀ (gamma : (sfRationalConstructibleLocalization C.l E X.obj.left).obj
          (sfOrientationIntegralLineOn D C E X d) ≅
        S.higher.rationalDuality.dualizing X c)
      (K : ObjectProperty.FullSubcategory (⊤ : ObjectProperty
        (sfRationalConstructibleCategory C.l E X.obj.left))),
      IsSfRationalCoefficientSitePerfect C.l E X.obj.left K.obj →
      SfPackagePerfectEvaluation MR.closed MR.symmetric
        (ObjectProperty.isoMk ⊤ (X := ⟨_, trivial⟩) (Y := ⟨_, trivial⟩) gamma) K) ∧
    (Nonempty ((sfQbarTwistingCoefficient C.l X.obj.left C.Qbar (d : ℤ))⟦2 * (d : ℤ)⟧ ≅
        S.closure.commonStageDuality.dualizing X c) ∧
      ∀ (gamma : (sfQbarTwistingCoefficient C.l X.obj.left C.Qbar (d : ℤ))⟦2 * (d : ℤ)⟧ ≅
        S.closure.commonStageDuality.dualizing X c)
      (K : ObjectProperty.FullSubcategory (⊤ : ObjectProperty
        (generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left))),
      IsGeneralAlgebraicallyClosedCoefficientSitePerfect C.l C.Qbar X.obj.left K.obj →
      SfPackagePerfectEvaluation MC.closed MC.symmetric
        (ObjectProperty.isoMk ⊤ (X := ⟨_, trivial⟩) (Y := ⟨_, trivial⟩) gamma) K)

/-- Normalized inverse orientation and trace at all coefficient stages, independent
point evaluation, and its smooth site-perfect geometric specialization.
Each component predicate spells out the actual maps and coefficient comparisons.
Source: prop-functor-package.proof.md, clause (6) and the point/site-perfect sentence
of (7) (blueprint: lem-sf-package-normalized-orientation-perfect-duality).
Proof: finite smooth purity inverts the specified gamma. Finite reduction of purity
and trace gives the forward and trace squares; compose with the inverses for the
inverse square. Integral residue Tor admits every bounded complete constructible
input. Reconstruct its compatible finite arrows by a strict coefficient-tower map
and the derived-completion unit; normalized effectivity gives its exact reductions.
The integral trace is the counit transpose of the same finite-trace-normalized unit
orientation tensored with the input, through inverse projection. Rationalize this
fixed lattice map. Exceptional coefficient comparisons preserve counits, which gives
the trace equation; the scalar purity square and its inverse give the other two.
Include a literal finite-field representative to obtain the common-stage equations;
identity and triple-extension compatibility follow from the specified cocycles.
At a point apply coefficient_frobenius and integral derived duality; the latter uses
finite free resolutions over the DVR and derived Hom, including for torsion modules.
For the smooth site-perfect assertion choose the actual ambient closed models and
their evaluation-preserving coefficient comparisons. On a local bounded complex of
finite projectives, termwise duality and the signed differential give invertible
coefficient evaluation. Transpose evaluation tensored with the oriented Tate line
to obtain theta, and cancel the opposite line and shift. The displayed equality of
transposes identifies geometric evaluation with coefficient evaluation. Exact local
restriction detects its invertibility. Completed coefficients, rational localization
and one common finite field preserve these maps. This uses the perfect-pair calculation
of sk-thm-sf-dual-perfect without assuming the general A6 biduality axiom. -/
theorem sfPackageNormalizedOrientationPerfectDuality :
    (∀ (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (d : ℕ) [SmoothOfRelativeDimension d f]
      (K : Scheme.proEtaleDerivedCategory Y P.Ring)
      (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K),
      SfPackageFiniteOrientationTrace P f d K hK) ∧
    (∀ (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
      (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
      {X Y : Scheme.{u}}
      [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
      [IsSeparated (X ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
      [IsSeparated (Y ↘ Spec (.of D.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (d : ℕ) [SmoothOfRelativeDimension d f]
      (K : DerivedCategory (scalarReductionSource C.l E Y))
      (hK : sfIntegralConstructible C.l E Y K),
      SfPackageIntegralOrientation D C E f d K hK) ∧
    (∀ (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := f))
      (d : ℕ) [SmoothOfRelativeDimension d f]
      (K : sfIntegralConstructibleCategory P.coefficients.l P.extension Y),
      SfPackageIntegralOrientationTrace P f S d K) ∧
    (∀ (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := f))
      (d : ℕ) [SmoothOfRelativeDimension d f]
      (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y),
      SfPackageRationalOrientationTrace P f c S d K) ∧
    (∀ (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := f))
      (d : ℕ) [SmoothOfRelativeDimension d f]
      (L : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
      (a : P.extension →ₐ[Padic P.coefficients.l] L.val)
      (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y),
      SfPackageFieldOrientationTrace P f c S d L a K) ∧
    (∀ (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different (f := f))
      (d : ℕ) [SmoothOfRelativeDimension d f]
      (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y),
      SfPackageCommonOrientation P f c S d K) ∧
    (∀ (l : ℕ) [Fact l.Prime]
      (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
      (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
      (n : ℕ) (hn : 1 ≤ n)
      [HasDerivedCategory.{u} (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E))]
      [HasDerivedCategory.{u} (ModuleCat.{u} E)]
      [HasDerivedCategory.{u} (ModuleCat.{u} Ω)],
      SfPackagePointEvaluation l E Ω n hn) ∧
    (∀ {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
      [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] (n : ℕ)
      (S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
      (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
      (d : ℕ) [SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]
      (c : Compactification (sixFunctorStructure X).hom.left),
      SfPackageSmoothSitePerfect n S X d c) := by
      sorry

end WeilConjectures
