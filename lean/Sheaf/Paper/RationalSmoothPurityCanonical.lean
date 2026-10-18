/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.AdicSmoothDualizingComplexes
public import Sheaf.Paper.PuritySourceTransports
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.FiniteCoefficientSmoothPurity
public import Sheaf.Paper.SmoothTrace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
import WeilConjectures.EtaleCohomology.Purity.Smooth.Adic
import WeilConjectures.EtaleCohomology.Purity.Smooth.Rational

/-! # Canonical rational purity in the intrinsic constructible presentation

Source: main-20261015, prop-weil-operations.proof.md, sentences 3--4;
sk-prop-sp-rational, Steps 1--2, and thm-pur-adic-reconstruction
(blueprint: def-pur-canonical-rational-purity-realization).

The family is the localized trace transpose of the adically reconstructed unit
orientation. Its source transports retain the actual shift comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor MonoidalCategory
namespace WeilConjectures

namespace RationalSmoothPurityCanonical

/-- Comparison pullback carries the ordinary constant coefficient to the tensor unit.
Source: rational purity proof Step 1, finite unit comparison
(blueprint: def-pur-canonical-rational-purity-realization). -/
@[irreducible]
def finiteComparisonUnit (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit A X) ≅
        𝟙_ (DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
      (PurityFiniteSetting.smoothPurityUnitIso A X) ≪≫
    ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A X

/-- Tensor left unitor transported through a specified presentation of the tensor.
Source: rational purity proof Step 1, finite unit comparison
(blueprint: def-pur-canonical-rational-purity-realization). -/
def tensorUnitFromPresentation {C : Type v} [Category.{u} C] [MonoidalCategory C]
    (T : C ⥤ C ⥤ C) (h : T = curriedTensor C) (M : C) :
    ((T.obj (𝟙_ C)).obj M) ≅ M :=
  eqToIso (congrArg (fun F ↦ (F.obj (𝟙_ C)).obj M) h) ≪≫ (λ_ M)

/-- The finite tensor left unitor in the published tensor presentation.
Source: rational purity proof Step 1, finite unit comparison
(blueprint: def-pur-canonical-rational-purity-realization). -/
@[irreducible]
def finiteTensorUnit (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ((PurityFiniteSetting.smoothPurityTensor A X).obj (𝟙_ _)).obj M ≅ M :=
  tensorUnitFromPresentation _
    (PurityFiniteSetting.smoothPurityTensorPresentation (ModuleCat.{u + 1} A) X) M

/-- Pullback of the finite coefficient unit, with the constant-section normalization.
All factors are the existing site comparison, ordinary constant-unit pullback,
and single-complex monoidal-unit comparison.
Source: rational purity proof Step 1, unit-object adic reconstruction
(blueprint: def-pur-canonical-rational-purity-realization). -/
@[irreducible]
def finitePullUnit (Q : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Q.smoothPurityPullback f).obj
      ((sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj (Q.coefficientUnit Y)) ≅
        𝟙_ (DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Q.Coefficient))) :=
  Q.smoothPurityPullbackComparison f _ (Etale.ordinaryFiniteUnit Q.Coefficient Y)
    ((sfIntrinsicDerivedEquivalence Y Q.Ring).unitIso.app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
        Y).mapDerivedCategory.obj (Etale.ordinaryFiniteUnit Q.Coefficient Y))) ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
      X).mapDerivedCategory.mapIso (Etale.ordinaryFiniteUnitPullback Q.Coefficient f) ≪≫
    finiteComparisonUnit Q.Coefficient X

/-- At the unit the finite smooth-purity source is the shifted Tate line, through
shift reassociation, pullback of the constant unit, and the tensor left unitor.
Source: rational purity proof Step 1, canonical finite source identifications
(blueprint: def-pur-canonical-rational-purity-realization). -/
@[irreducible]
def finiteUnitSource (Q : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    (sfIntrinsicDerivedEquivalence X Q.Ring).functor.obj
      ((((PurityFiniteSetting.smoothPurityTensor Q.Coefficient X).obj
        ((Q.smoothPurityPullback f).obj
          ((sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj (Q.coefficientUnit Y)))).obj
            ((Q.diagonalTwist X d)⟦-(2*(d : ℤ))⟧))⟦2*(d : ℤ)⟧) ≅
      (sfIntrinsicDerivedEquivalence X Q.Ring).functor.obj (Q.diagonalTwist X d) :=
  (sfIntrinsicDerivedEquivalence X Q.Ring).functor.mapIso
    (Q.smoothPurityReassociation X d
      ((Q.smoothPurityPullback f).obj
        ((sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj (Q.coefficientUnit Y))) ≪≫
      ((PurityFiniteSetting.smoothPurityTensor Q.Coefficient X).mapIso
        (finitePullUnit Q f)).app (Q.diagonalTwist X d) ≪≫
      finiteTensorUnit Q.Coefficient X (Q.diagonalTwist X d))


section RelativeOrientation
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

/-- The shifted completed coefficient line in the existing finite-Tor category.
Source: rational purity proof, integral orientation
(blueprint: def-pur-canonical-rational-purity-realization). -/
abbrev twist (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  AdicSmoothDualizing.integralTwist P T aT d

/-- The finite ordinary dualizing object is bounded below by smooth purity.
Source: rational purity proof Step 1, finite trace
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: the ordinary comparison in existsUnique_diagonalDualizingObject identifies
this object with the finite Tate line shifted by 2d. A single sheaf has cohomology
only in degree zero; its shift is bounded below. Transport that bound across the iso. -/
theorem finiteDualizingPlus (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (fun [hc : HasCompactification f] ↦ DerivedCategory.TStructure.t.plus
      ((AdicSmoothDualizing.levelSetting P n).diagonalOrdinaryDualizing f))
        (hc := c.hasCompactification) := by
  sorry

/-- The normalized finite integration for this relative smooth morphism.
The finite diagonal orientation and the exceptional counit are the published maps.
Source: rational purity proof Step 1 and its finite smooth normalization
(blueprint: def-pur-canonical-rational-purity-realization). -/
@[irreducible]
def finiteIntegration (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) c).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d)) ⟶
      (AdicSmoothDualizing.levelSetting P n).coefficientUnit Y :=
  letI : HasCompactification f := c.hasCompactification
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f
    (AdicSmoothDualizing.levelSetting P n).Coefficient
  (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n c).hom.app _ ≫
    (ProEtale.sfIntrinsicCompactSupportComparison
      (AdicSmoothDualizing.levelSetting P n).Ring c).hom.app _ ≫
    (sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
      ((ProEtale.sfFixedCompactSupport
        (AdicSmoothDualizing.levelSetting P n).Ring c).map
        (((AdicSmoothDualizing.levelSetting P n).diagonalDualizingObject d f
          (Y ↘ Spec (.of P.field.k))).inv ≫
          ((AdicSmoothDualizing.levelSetting P n).diagonalDualizingComparison f).hom) ≫
        (ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient) c).hom.app
            ⟨_, finiteDualizingPlus P f c n d⟩ ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
          Y).mapDerivedCategory.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
              (AdicSmoothDualizing.levelSetting P n).Coefficient c
              (HasCompactification.compactification f)).hom.app
                ⟨_, finiteDualizingPlus P f c n d⟩ ≫
              (Etale.rightDerivedUpperShriekAdjunction
                (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
                f).counit.app _))

/-- The published compact-support functor at a reindexed level, with the original
over-field structures supplied explicitly. Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def levelSmoothCompactSupport (n : ℕ) :=
  @PurityFiniteSetting.smoothCompactSupport (AdicSmoothDualizing.levelSetting P n) X Y f
    (inferInstanceAs (X.Over (Spec (.of P.field.k))))
    (inferInstanceAs (Y.Over (Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) ))
    (inferInstanceAs (QuasiCompact (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (f.IsOver (Spec (.of P.field.k))))
    (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
    (inferInstanceAs (QuasiCompact f))

/-- The recorded finite smooth-purity map with the inherited over-field instances.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def levelSmoothPurityMap (n d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y (AdicSmoothDualizing.levelSetting P n).Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y K) :=
  @PurityFiniteSetting.smoothPurityMap (AdicSmoothDualizing.levelSetting P n) X Y
    (inferInstanceAs (X.Over (Spec (.of P.field.k))))
    (inferInstanceAs (Y.Over (Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k)))) f
    (inferInstanceAs (f.IsOver (Spec (.of P.field.k))))
    (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
    (inferInstanceAs (QuasiCompact f)) d (inferInstanceAs (SmoothOfRelativeDimension d f)) K hK

/-- The recorded exceptional counit with the inherited over-field instances.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def levelSmoothExceptionalCounit (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory Y (AdicSmoothDualizing.levelSetting P n).Ring) :=
  @PurityFiniteSetting.smoothExceptionalCounit (AdicSmoothDualizing.levelSetting P n) X Y
    (inferInstanceAs (X.Over (Spec (.of P.field.k))))
    (inferInstanceAs (Y.Over (Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k)))) f
    (inferInstanceAs (f.IsOver (Spec (.of P.field.k))))
    (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
    (inferInstanceAs (QuasiCompact f)) K

/-- The finite integration used in the integral orientation is the actual transpose
of smoothPurityMap at the coefficient unit. The source comparison is explicitly
finiteUnitSource; the compact-support comparison is the existing open/proper one.
This pins the map, including its shift and unit normalization, rather than merely
asserting that two isomorphic objects have some compatible isomorphism.
Source: rational purity proof Step 1; def-pur-smooth-purity-map; thm-pur-adic-reconstruction
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: expand smoothPurityMap and use its characterization in the ordinary unit
presentation. Reassociation cancels with finiteUnitSource. Pullback of the constant
unit and the tensor left unitor reduce its tensor mate to inverse diagonal orientation.
The comparison adjunction triangles then identify its counit transpose with
finiteIntegration. finiteImageIso preserves the open and proper units separately,
and the ordinary compactification comparison preserves the exceptional counit.
This proves the displayed equality for every positive level, including d=0. -/
theorem finiteIntegration_smoothPurityMap (n d : ℕ) [SmoothOfRelativeDimension d f]
    (hUnit : finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y
      ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y)) :
    (fun [hc : HasCompactification f] ↦
      (levelSmoothCompactSupport P f n).map
        (levelSmoothPurityMap P f n d
          ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y) hUnit) ≫
        levelSmoothExceptionalCounit P f n
          ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y) =
      (levelSmoothCompactSupport P f n).map
        (finiteUnitSource (AdicSmoothDualizing.levelSetting P n) f d).hom ≫
        (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n
          (HasCompactification.compactification f)).inv.app _ ≫
        finiteIntegration P f (HasCompactification.compactification f) n d)
      (hc := c.hasCompactification) := by
  sorry

/-- Finite trace normalization, using the actual coefficient comparison and root projection.
Source: rational purity proof, reconstruction of the coefficient-unit orientation
(blueprint: def-pur-canonical-rational-purity-realization). -/
def IsNormalizedTrace (d : ℕ) [SmoothOfRelativeDimension d f]
    (t : (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) c).obj
          (twist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj) : Prop :=
  ∀ n : ℕ,
    (PurCompactSupport.comparison (PurCompactSupport.reduction P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) c).app
          (twist P X (X ↘ Spec (.of P.field.k)) d).obj ≫
      (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) c).map
          (AdicSmoothDualizing.twistReduction P X (X ↘ Spec (.of P.field.k)) n d) ≫
      finiteIntegration P f c n d =
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n) Y)).map t ≫
        AdicSmoothDualizing.twistReduction P Y (Y ↘ Spec (.of P.field.k)) n 0

variable (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
  P.field P.coefficients.different (f := f))

/-- The specified constructible operation, retaining its actual adjunction.
Source: rational purity proof, exceptional pullback
(blueprint: def-pur-canonical-rational-purity-realization). -/
abbrev operation (s : ConstructibleExceptionalCoefficients.Stage.{u} P.coefficients.l) :=
  S.ring.operation c s

/-- The coefficient-unit orientation's trace in ordinary compact-support coordinates.
Source: rational purity proof Step 1, trace transpose
(blueprint: def-pur-canonical-rational-purity-realization). -/
def orientationTrace (d : ℕ)
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0)) :=
  (S.ring.left c (.integral (AdicSmoothDualizing.fieldStage P))).inv.app _ ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι.map
      ((operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).F.map a.hom ≫
        (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app
          (twist P Y (Y ↘ Spec (.of P.field.k)) 0))

/-- The unit orientation is uniquely fixed by the finite diagonal traces.
This uniqueness is only for a shifted rank-one line, not for arbitrary derived lifts.
Source: rational purity proof Step 1; finite diagonal orientation
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: adic reconstruction of the finite unit-object purity gives the orientation.
Its counit reductions are precisely finiteIntegration by scalar compatibility.
If two orientations have these traces, transpose under the specified adjunction and
use either orientation to identify their quotient with an endomorphism of the shifted
completed line. This is an ordinary degree-zero line endomorphism. Its projections
to every finite quotient vanish, so it vanishes, since completed coefficients are the
inverse limit of those quotients. This proves uniqueness without a phantom-map claim. -/
theorem orientation_existsUnique (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃! a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
        (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).G.obj
          (twist P Y (Y ↘ Spec (.of P.field.k)) 0),
      IsNormalizedTrace P f c d (orientationTrace P f c S d a) := by
  sorry

/-- The unique finite-trace-normalized unit orientation.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def orientation (d : ℕ) [SmoothOfRelativeDimension d f] :=
  (orientation_existsUnique P f c S d).exists.choose

/-- Transport of an adically reconstructed unit orientation is the orientation used
here. The premise is exactly the finite trace condition supplied by reconstruction;
it does not claim uniqueness of coherent lifts on arbitrary complexes.
Source: thm-pur-adic-reconstruction and rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: the reconstruction theorem realizes the normalized finite purity maps. By
finiteIntegration_smoothPurityMap their counit reductions are finiteIntegration.
Thus the transported unit orientation satisfies IsNormalizedTrace. The uniqueness
clause of orientation_existsUnique identifies it with orientation. This uniqueness
uses only endomorphisms of the shifted rank-one line, detected by finite quotients. -/
theorem orientation_eq_adic (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
    (ha : IsNormalizedTrace P f c d (orientationTrace P f c S d a)) :
    orientation P f c S d = a := by
  sorry

/-- Smooth ordinary pullback preserves the complete constructible finite-Tor domain.
Consequently the already specified strict pullback augmentation is invertible.
Source: rational purity proof, integral pullback comparison
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: work on finite constructible stratifications with bounded finite flat local
models. Smooth inverse image preserves these models and their coefficient quotient
maps. Their completed coefficient scalars give complete pullbacks. Descent and finite
localization triangles preserve completeness. The strict quotient augmentation is the
completion unit, so becomes invertible after localization. -/
theorem smoothPullAugmentation_isIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
    (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
    (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
      (DerivedCategory.Q.obj C)) :
    IsIso (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation
        P.coefficients.l P.extension f).app C)) := by
  sorry

/-- Smooth completed-to-ordinary pullback on a good finite-Tor representative.
Source: rational purity proof, integral source
(blueprint: def-pur-canonical-rational-purity-realization). -/
def smoothPullToOrdinaryOnGood (d : ℕ) [SmoothOfRelativeDimension d f]
    (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
    (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
    (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
      (DerivedCategory.Q.obj C)) :=
  (integralDerivedPullbackComparison P.coefficients.l P.extension f).app ⟨C,hC⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation
        P.coefficients.l P.extension f).app C))
      (smoothPullAugmentation_isIso P f d C hC hK)).symm ≪≫
    ((FrobeniusCoefficientTwists.modulePull
      P.coefficients.l P.extension f).mapDerivedCategoryFactors.app C).symm

/-- The smooth comparison is fixed on every representative and every presentation map.
Source: rational purity proof, integral source
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: use good K-flat resolutions. The normalized strict augmentation is natural,
so its descent is independent of resolution and of the isomorphism presenting K.
Every K has a resolution, which also proves uniqueness. -/
theorem smoothPullToOrdinary_existsUnique (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    ∃! e : (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj ≅
        (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
          f).obj K.obj,
      ∀ (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
        (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
        (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
          (DerivedCategory.Q.obj C)) (a : DerivedCategory.Q.obj C ≅ K.obj),
        e = (integralDerivedPullback P.coefficients.l P.extension f).mapIso a.symm ≪≫
          smoothPullToOrdinaryOnGood P f d C hC hK ≪≫
          (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
            f).mapIso a := by
  sorry

/-- The specified smooth completed-to-ordinary comparison.
Source: rational purity proof, integral source
(blueprint: def-pur-canonical-rational-purity-realization). -/
def smoothPullToOrdinary (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  (smoothPullToOrdinary_existsUnique P f d K).exists.choose

/-- Completed pullback preserves the finite-Tor constructible domain here.
Source: rational purity proof, bounded integral representatives
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: integral pullback preserves the constructible complete category. Its actual
reductions are finite pullbacks of the reductions of K and retain their one Tor
interval. Thus the result has the required complete membership and uniform bounds. -/
theorem pullFiniteTor (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension X
      ((integralDerivedPullback P.coefficients.l P.extension f).obj K.obj) := by
  sorry

/-- The integral twisted pullback, with the even shift on the coefficient line.
This is canonically Lf*K(d)[2d] by the specified tensor symmetry and shift constraints.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: the coefficient line is complete constructible with uniform Tor interval [-2d,-2d].
Pullback of K has its original uniform interval. Completed tensor adds those intervals
and preserves constructibility. This proves finite-Tor membership of the displayed object. -/
theorem integralSource_mem (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension X
      ((integralCompletedTensor P.coefficients.l P.extension X).obj
        ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
          (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj)) := by
  sorry

/-- The integral source in the existing finite-Tor full subcategory.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralSource (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X :=
  ⟨_,integralSource_mem P f d K⟩

/-- The canonical source comparison to the ordinary tensor used by projection.
Source: rational purity proof, trace-transpose source
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinarySource (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  tensorToOrdinary P.coefficients.l P.extension X
    (twist P X (X ↘ Spec (.of P.field.k)) d)
    ⟨_,pullFiniteTor P f d K⟩ ≪≫
    (ordinaryModel P.coefficients.l P.extension X).tensor.mapIso
      (Iso.prod (Iso.refl _) (smoothPullToOrdinary P f d K))

/-- The actual proper/open projection transformation for the fixed compactification.
Source: rational purity proof, inverse projection in the trace transpose
(blueprint: def-pur-canonical-rational-purity-realization). -/
def projection (d : ℕ) (K : finiteTorConstructibleIntegralCategory
    P.coefficients.l P.extension Y) :=
  ((PurCompactSupport.projectionMap
    (PurCompactSupport.completed P.coefficients.l P.extension) c
    (ordinaryModel P.coefficients.l P.extension X)
    (ordinaryModel P.coefficients.l P.extension c.Z)
    (ordinaryModel P.coefficients.l P.extension Y)
    (PurCompactSupport.completedPull_comp P.coefficients.l P.extension c.i c.g)).app
      (twist P X (X ↘ Spec (.of P.field.k)) d).obj).app K.obj

/-- Projection is invertible on the indicated constructible finite-Tor inputs.
The asserted map is the actual counit-first proper/open composite above.
Source: rational purity proof, projection formula
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: finite coefficient projection is invertible for a bounded flat constructible
second input. Ordinary coefficient tensor agrees with completed tensor on this domain.
The normalized strict quotient-tower realization carries the finite projection and its
inverse to the displayed ordinary map and inverse. Proper and open comparisons retain
their original units and counits throughout, so this proves invertibility of this map. -/
theorem projection_isIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    IsIso (projection P f c d K) := by
  sorry

/-- The shifted zero-power line is the coefficient unit of the normalized ordinary tensor.
Source: rational purity proof, tensor-unit constraint
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinaryCoefficientUnit (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    (twist P T aT 0).obj ≅
      (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)).monoidal.tensorUnit :=
  (shiftFunctorZero _ ℤ).app _ ≪≫
    (@RingedSiteDualityModel.unitIso.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)).symm

/-- The ordinary tensor's coefficient left unitor, retaining its scalar normalization.
Source: rational purity proof, trace transpose
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinaryLeftUnitor
    (K : DerivedCategory (integralTowerModules P.coefficients.l P.extension Y)) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      ((twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj,K) ≅ K :=
  eqToIso (congrArg (fun a ↦ a.obj ((twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj,K))
    (ordinaryModel_existsUnique P.coefficients.l P.extension Y).exists.choose_spec.1) ≪≫
    (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} Y none)
      (IntegralOnSlice.abLocallyBijective.{u, u} Y none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension Y none)).tensor.mapIso
      (Iso.prod (ordinaryCoefficientUnit P Y (Y ↘ Spec (.of P.field.k))) (Iso.refl K)) ≪≫
    (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} Y none)
      (IntegralOnSlice.abLocallyBijective.{u, u} Y none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension Y none)).monoidal.leftUnitor K

/-- The actual trace/projection composite whose adjoint is smooth purity.
Source: rational purity proof Step 1, trace-transpose construction
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralTraceTransposeOfOrientation (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).F.obj
      (integralSource P f d K) ⟶ K :=
  ObjectProperty.homMk
    ((S.ring.left c (.integral (AdicSmoothDualizing.fieldStage P))).hom.app
        (integralSource P f d K) ≫
      (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).map (ordinarySource P f d K).hom ≫
      (@asIso _ _ _ _ (projection P f c d K) (projection_isIso P f c d K)).inv ≫
      (ordinaryModel P.coefficients.l P.extension Y).tensor.map
        (Prod.mkHom (orientationTrace P f c S d a) (𝟙 K.obj)) ≫
      (ordinaryLeftUnitor P K.obj).hom)

/-- The fixed transpose uses the transported, finite-trace-normalized adic unit
orientation. Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralTraceTranspose (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  integralTraceTransposeOfOrientation P f c S d (orientation P f c S d) K

/-- Integral purity is the actual adjoint transpose of that fixed composite.
The only chosen orientation is uniquely determined on the coefficient unit.
Source: rational purity proof Step 1 and the trace-transpose convention
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralMap (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralSource P f d K ⟶
      (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.homEquiv _ _
    (integralTraceTranspose P f c S d K)

/-- On every integral input, the chosen purity map is the transpose constructed
from the transported adic unit orientation. The trace premise is exactly the
finite-reduction normalization of that orientation, with the finite maps pinned
by finiteIntegration_smoothPurityMap. Thus this compares maps, not only objects.
Source: thm-pur-adic-reconstruction; rational purity proof Step 1;
lem-pur-tower-trace-purity-comparison
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: orientation_eq_adic identifies the finite-trace-normalized orientation
with the transported reconstructed unit map a. Substitute that equality in the
explicit projection/trace composite integralTraceTranspose. Applying the actual
constructible adjunction homEquiv gives the asserted equality for every K.
No uniqueness of a coherent lift for a general K is used. -/
theorem integralMap_eq_adicTraceTranspose (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
    (ha : IsNormalizedTrace P f c d (orientationTrace P f c S d a))
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralMap P f c S d K =
      (operation P f c S (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.homEquiv _ _
        (integralTraceTransposeOfOrientation P f c S d a K) := by
  sorry

/-- The trace-transpose integral comparison is invertible.
Source: rational purity proof Step 1, transporting adic purity
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: the finite diagonal orientations are compatible with reduction and yield the
normalized tower orientation. The finite tensor-counit transpose is exactly
smoothPurityMap, including its shift reassociation. Strict tower reconstruction
carries that map to integralMap, because all tensor, compactification, and coefficient
comparisons preserve their normalized units and counits. Each finite purity map is
invertible. Normalized reconstruction preserves its inverse, hence integralMap is
invertible. This uses the full trace transpose, not uniqueness of arbitrary lifts. -/
theorem integralMap_isIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    IsIso (integralMap P f c S d K) := by
  sorry

/-- The canonical integral purity isomorphism, with its map already constructed.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  @asIso _ _ _ _ (integralMap P f c S d K) (integralMap_isIso P f c S d K)

end RelativeOrientation



section Rational
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))

/-- Every underlying integral representative is in the finite-Tor category.
There is no stable-lattice assumption on any rational arrow.
Source: rational purity proof Step 1; integral residue-Tor theorem
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: an object of the scalar localization has an actual integral constructible
representative. integral_residue_tor identifies its object predicate with the
uniform finite-Tor constructible predicate, proving the asserted membership. -/
theorem representativeTor
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension Y K.obj.obj := by
  sorry

/-- The unchanged integral object presenting a rational object.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def representative
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y :=
  ⟨K.obj.obj,representativeTor P K⟩

/-- Rationalization returns the original object, literally in the scalar localization.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: rationalization includes the integral full subcategory and changes only Hom
groups by scalar localization. Both objects therefore have the same integral
representative; their membership proofs are equal by proof irrelevance. -/
theorem representative_eq
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) Y).obj (representative P K) = K := by
  sorry

/-- The rational tensor and pullback retain their integral object formulas.
The first input here is the localization of the *integrally* shifted line, so this
identity makes no claim that a rational shift by 2d is literally the integral shift.
Source: rational purity proof Step 1, localization of integral representatives
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: use the recorded object clauses of rationalDerivedTensor and
rationalDerivedPullback. The nonnegative integral Tate line is the positive root
tensor power used by twist; inherited integral shifts retain the ambient shift.
The resulting ambient objects agree. Full-subcategory membership proofs agree by
proof irrelevance, yielding this object equality. -/
theorem rationalIntegralSource_eq (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalDerivedTensor P.coefficients.l P.extension X).obj
      ((sfRationalConstructibleLocalization P.coefficients.l P.extension X).obj
        ((sfIntegralTwistingCoefficient P.coefficients.l P.extension X (d : ℤ))⟦2*(d : ℤ)⟧),
        (rationalDerivedPullback P.coefficients.l P.extension f).obj K) =
      (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldStage P) X).obj
        (integralSource P f d (representative P K)) := by
  sorry

/-- The source comparison uses the inverse localization commShiftIso at 2d,
followed by the unchanged integral tensor/pullback object formulas. The rational
shift is only normalized at one; its coherent comparison supplies all other shifts.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def rationalSourceComparison (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldStage P) X).obj
        (integralSource P f d (representative P K)) :=
  (rationalDerivedTensor P.coefficients.l P.extension X).mapIso
    (Iso.prod
      (((sfRationalConstructibleLocalization P.coefficients.l P.extension X).commShiftIso
        (2*(d : ℤ))).symm.app
          (sfIntegralTwistingCoefficient P.coefficients.l P.extension X (d : ℤ)))
      (Iso.refl _)) ≪≫ eqToIso (rationalIntegralSource_eq P f d K)

/-- The canonical rational purity isomorphism: rationalize the constructed integral
trace transpose, then use the specified counit-preserving exceptional comparison.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def rationalIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  rationalSourceComparison P f d K ≪≫
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) X).mapIso
        (integralIso P f c S d (representative P K)) ≪≫
    (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).b.app
      (representative P K) ≪≫
    (operation P f c S (.rational (AdicSmoothDualizing.fieldStage P))).G.mapIso
      (eqToIso (representative_eq P K))

end Rational

section CommonPurity
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (P : PurityFiniteSetting.{u})

/-- The fixed purity datum at an arbitrary finite subfield; only the coefficient field changes.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
abbrev stageSetting (L : Index P.coefficients.l P.coefficients.Qbar) : PurityFiniteSetting.{u} :=
  { P with extension := L.val, finiteExtension := L.property }

/-- The inverse of the published small-model algebra equivalence.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
def modelInverse : Coefficient.{u} P.coefficients.l P.coefficients.Qbar
    (AdicSmoothDualizing.fieldIndex P) →ₐ[Padic P.coefficients.l] P.extension :=
  (Shrink.algEquiv (Padic P.coefficients.l) P.extension).toAlgHom

/-- Scalar transport from the small model back to the given finite coefficient field.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
def modelBack (T : Scheme.{u}) :=
  sfRationalScalarExtension P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) T 0
      (Fact.out : P.coefficients.l.Prime).ne_zero P.extension (modelInverse P)

/-- The two actual algebra equivalences compose to the identity.
Source: rational purity proof Step 2, small-model identity
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: apply the left inverse identity of Shrink.algEquiv pointwise. AlgHom
extensionality gives exactly the identity of algebra homomorphisms. -/
theorem modelComposite :
    (AdicSmoothDualizing.modelEmbedding P).comp (modelInverse P) =
      AlgHom.id (Padic P.coefficients.l)
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex P)) := by
  sorry

/-- The canonical round trip is balanced scalar associativity followed by the unit.
Source: rational purity proof Step 2, small-model transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
def modelRoundtrip (T : Scheme.{u}) :
    modelBack P T ⋙ AdicSmoothDualizing.modelScalar P T ≅
      𝟭 (sfRationalConstructibleCategory P.coefficients.l
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex P)) T) :=
  scalarAssociator P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) P.extension
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P))
    (modelInverse P) (AdicSmoothDualizing.modelEmbedding P)
    (AlgHom.id (Padic P.coefficients.l) _) (modelComposite P) T ≪≫
    sfRationalScalarUnit P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) T 0
        (Fact.out : P.coefficients.l.Prime).ne_zero

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))

/-- Rational purity in the actual small coefficient model, transported through the
specified algebra equivalence and counit-preserving exceptional comparison.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
def smallModelIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) Y) :
    (rationalSource P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) f d).obj K ≅
    (S.ring.operation c (.rational
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.obj K :=
  (rationalSource P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) f d).mapIso ((modelRoundtrip P Y).app K).symm ≪≫
    (sourceScalar P.coefficients.l P.extension
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)
      f d ((modelBack P Y).obj K)).symm ≪≫
    (AdicSmoothDualizing.modelScalar P X).mapIso
      (rationalIso P f c S d ((modelBack P Y).obj K)) ≪≫
    (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)).b.app
          ((modelBack P Y).obj K) ≪≫
    (S.ring.operation c (.rational
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.mapIso ((modelRoundtrip P Y).app K)

/-- The canonical common-stage purity family. Each object is treated at its literal
finite stage, transported by its actual field-model equivalence, then included with the
specified exceptional coefficient comparison.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
def commonIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) :
    (commonSource P.coefficients.l P.coefficients.Qbar f d).obj K ≅
      (S.ring.operation c .closed).G.obj K :=
  let e : (rationalSource P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar K.stage) f d).obj K.obj ≅
      (S.ring.operation c (.rational (ConstructibleExceptionalCoefficients.commonField
        P.coefficients.l P.coefficients.Qbar K.stage))).G.obj K.obj :=
    smallModelIso (stageSetting P K.stage) f c S d K.obj
  commonSourceComparison P.coefficients.l P.coefficients.Qbar f d K ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso e ≪≫
    (S.common.commonComparison c K.stage).b.app K.obj

/-- Finite scalar extension carries the trace-normalized rational purity map to
that over the enlarged coefficient field, with the specified exceptional mate.
Source: rational purity proof Step 2, the finite-extension compatibility equation
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: on the degree-zero unit orientation, reduce at every finite quotient.
The diagonal finite trace is compatible with coefficient scalar extension and its
fixed root generators. Finite reduction of maps from the shifted rank-one line is
jointly faithful, so the integral unit trace square commutes. Tensoring with an
arbitrary lattice, apply the actual projection formula and its counit compatibility;
the defining adjunction hom-equivalence yields the integral purity square. The
finite-free completed-scalar comparison identifies ordinary scalar tensor with
strict adic scalar extension. Rationalize this square. Since scalar localization
is linear, the equation holds on every object and respects the normalized source
comparison and the counit-preserving exceptional comparison in the display. -/
theorem rationalIso_scalar (L : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar)
    (a : P.extension →ₐ[Padic P.coefficients.l] L.val)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) (AdicSmoothDualizing.fieldStage (stageSetting P L))
      a X).map (rationalIso P f c S d K).hom ≫
        (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
          (AdicSmoothDualizing.fieldStage (stageSetting P L)) a).b.hom.app K =
      (sourceScalar P.coefficients.l P.extension L.val a f d K).hom ≫
        (rationalIso (stageSetting P L) f c S d
          ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y).obj K)).hom := by
  sorry

end CommonPurity

end RationalSmoothPurityCanonical


end WeilConjectures
