/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionTowers
public import WeilConjectures.AlgebraicGeometry.IntegralSmoothAdjunctionPresentation
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Normalized integral and condensed counit realization data

Source: latest blueprint, sk-thm-purity-transport, Steps 2--4.
(blueprint: def-pur-integral-counit-realization-data).

## Main definitions

`Stage` specifies the realized Hom adjunction and its fixed counit.
`CondensedStage` specifies its normalized transport to condensed modules.
`Condensed`, its inclusion and restriction reuse the existing full subcategory.
`condensedSource` and `towerSource` are the actual twisted inverse images.
No inhabitance of these data types is asserted here.

Positive tower exponent n+1 is indexed by n. All gamma components below are
realizations of entire strict-tower morphisms, not lifts of separate finite arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.integralDerivedPullback

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.TransportIntegralCounit

/-- The existing condensed finite-Tor category, kept opaque during elaboration.
Source: purity-transport Step 2, condensed integral Dctf.
(blueprint: def-pur-integral-counit-realization-data). -/
@[irreducible]
def Condensed (P : PurityFiniteSetting.{u}) (E : FieldShriekSystem.Index P)
    (T : Scheme.{u}) : Type (u + 2) :=
  ConstantModelConstructibleFiniteTor (spIntegralCondensed P.coefficients.l E.val) T

/-- The inherited category structure has the original condensed Hom universe u+1.
Source: purity-transport Step 2, ambient derived morphisms.
(blueprint: def-pur-integral-counit-realization-data). -/
instance condensedCategory (P : PurityFiniteSetting.{u}) (E : FieldShriekSystem.Index P)
    (T : Scheme.{u}) : Category.{u + 1} (Condensed P E T) := by
  unfold Condensed
  infer_instance

/-- The actual full-subcategory inclusion of condensed Dctf in integral derived modules.
Source: purity-transport Step 2, comparison with condensed modules.
(blueprint: def-pur-integral-counit-realization-data). -/
@[irreducible]
def condensedInclusion (P : PurityFiniteSetting.{u}) (E : FieldShriekSystem.Index P)
    (T : Scheme.{u}) : Condensed P E T ⥤
      IntegralDirectImageTower.Integral P.coefficients.l E.val T := by
  unfold Condensed
  exact ObjectProperty.ι _

/-- Restrict the given literal ambient functor using its preservation certificate.
Source: purity-transport Step 2, restriction to the same condensed Dctf categories.
(blueprint: def-pur-integral-counit-realization-data). -/
@[irreducible]
def condensedRestriction (P : PurityFiniteSetting.{u}) (E : FieldShriekSystem.Index P)
    {T W : Scheme.{u}}
    (F : IntegralDirectImageTower.Integral P.coefficients.l E.val T ⥤
      IntegralDirectImageTower.Integral P.coefficients.l E.val W)
    (h : ∀ M : Condensed P E T,
      (constantModelBoundedConstructible (spIntegralCondensed P.coefficients.l E.val) W ⊓
        fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)
          (F.obj ((condensedInclusion P E T).obj M))) :
    Condensed P E T ⥤ Condensed P E W := by
  unfold Condensed condensedInclusion condensedCategory at *
  exact ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ F) h

section IntegralStage

variable (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- The explicit adjunction at one integral stage, retaining the actual realization
and both directions of its Hom bijection. The gamma normalization determines the
natural isomorphism completely; no unspecified purity morphism is admitted.
Source: purity-transport Step 2, integral Hom display and Step 3, fixed counit.
(blueprint: def-pur-integral-counit-realization-data). -/
structure Stage (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d) where
  gammaH : FieldExtensionTowers.puritySource P D j p d m ≅
    FieldExtensionTowers.exceptional P D j p d m
  gammaH_eq : ∀ K : FieldExtensionTowers.Integral P E Y,
    gammaH.hom.app K = FieldExtensionTowers.gamma P D j p d m K
  adjunction : FieldExtensionTowers.support P D j p d m ⊣
    FieldExtensionTowers.puritySource P D j p d m
  transported : adjunction = m.realization.adjunction.ofNatIsoRight gammaH.symm
  hom : ∀ (M : FieldExtensionTowers.Integral P E X)
    (K : FieldExtensionTowers.Integral P E Y)
    (h : (FieldExtensionTowers.support P D j p d m).obj M ⟶ K),
    adjunction.homEquiv M K h = m.realization.adjunction.homEquiv M K h ≫ gammaH.inv.app K
  inverse : ∀ (M : FieldExtensionTowers.Integral P E X)
    (K : FieldExtensionTowers.Integral P E Y)
    (a : M ⟶ (FieldExtensionTowers.puritySource P D j p d m).obj K),
    (adjunction.homEquiv M K).symm a =
      (FieldExtensionTowers.support P D j p d m).map (a ≫ gammaH.hom.app K) ≫
        m.realization.adjunction.counit.app K
  unit : ∀ M : FieldExtensionTowers.Integral P E X,
    adjunction.unit.app M = m.realization.adjunction.unit.app M ≫
      gammaH.inv.app ((FieldExtensionTowers.support P D j p d m).obj M)
  counit : ∀ K : FieldExtensionTowers.Integral P E Y,
    adjunction.counit.app K =
      (FieldExtensionTowers.support P D j p d m).map (gammaH.hom.app K) ≫
        m.realization.adjunction.counit.app K
  fixed_counit : ∀ (G : FieldExtensionTowers.Integral P E Y ⥤
      FieldExtensionTowers.Integral P E X)
    (a : FieldExtensionTowers.support P D j p d m ⊣ G)
    (K : FieldExtensionTowers.Integral P E Y),
    adjunction.counit.app K =
      (FieldExtensionTowers.support P D j p d m).map
        (gammaH.hom.app K ≫ (m.realization.adjunction.rightAdjointUniq a).hom.app K) ≫
          a.counit.app K
  unit_reduction : ∀ M : FieldExtensionTowers.Integral P E X,
    (FieldExtensionTowers.reduceX P D j p d m).map (adjunction.unit.app M) =
      m.adjunction.unit.app ((FieldExtensionTowers.reduceX P D j p d m).obj M) ≫
        m.exceptional.map (m.realization.leftComparison.inv.app M) ≫
        m.realization.rightComparison.inv.app _ ≫
        (FieldExtensionTowers.reduceX P D j p d m).map
          (gammaH.inv.app ((FieldExtensionTowers.support P D j p d m).obj M))
  counit_reduction : ∀ K : FieldExtensionTowers.Integral P E Y,
    (FieldExtensionTowers.reduceY P D j p d m).map (adjunction.counit.app K) =
      (FieldExtensionTowers.reduceY P D j p d m).map
          ((FieldExtensionTowers.support P D j p d m).map (gammaH.hom.app K)) ≫
        m.realization.leftComparison.hom.app _ ≫
        (SpTowerGluing.support P.coefficients.l E.val (D.base E) (D.operations E)
          (D.coordinates E) (SpTowerGamma.factorization j p) m.supportClosed).map
          (m.realization.rightComparison.hom.app K) ≫
        m.adjunction.counit.app ((FieldExtensionTowers.reduceY P D j p d m).obj K)

/-- Literal condensed pullback, tensor with the specified integral Tate line and
shift. The line is transported by the normalized coefficient-ring isomorphism,
using the existing internalization equivalence, not chosen from its reductions.
Source: purity-transport Step 2 and coefficient-twists-detailed, integral paragraph.
(blueprint: def-pur-integral-counit-realization-data). -/
@[irreducible]
def condensedSource (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d) :
    IntegralDirectImageTower.Integral P.coefficients.l E.val Y ⥤
      IntegralDirectImageTower.Integral P.coefficients.l E.val X :=
  IntegralDirectImageTower.pull P.coefficients.l E.val (j ≫ p) ⋙
    (IntegralDirectImageTower.tensor P.coefficients.l E.val X).flip.obj
      ((RationalizedSmoothAdjunction.internalization P.coefficients.l E.val X
        ((D.coordinates E).abelian X) m.reductionX).functor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (integralTwistLine P.coefficients.l E.val X (d : ℤ)))) ⋙
      shiftFunctor _ (2 * (d : ℤ))

/-- Realization on the actual condensed Dctf categories. The inclusion comparisons
fix the coefficient encodings; support and source are the literal ambient functors
restricted by membership proofs. The adjunction comparison fixes the Hom bijection,
unit and counit to those of the whole-tower construction.
Source: purity-transport Steps 2--3, integral realization and same ambient left adjoint.
(blueprint: def-pur-integral-counit-realization-data). -/
structure CondensedStage (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d)
    (A : Stage P D j p d E m) where
  encodingX : FieldExtensionTowers.Integral P E X ≌
    Condensed P E X
  encodingY : FieldExtensionTowers.Integral P E Y ≌
    Condensed P E Y
  encodingX_normalized : encodingX.functor ⋙ condensedInclusion P E X ≅
    (sfIntegralConstructible P.coefficients.l E.val X).ι ⋙
      (RationalizedSmoothAdjunction.internalization P.coefficients.l E.val X
        ((D.coordinates E).abelian X) m.reductionX).functor
  encodingY_normalized : encodingY.functor ⋙ condensedInclusion P E Y ≅
    (sfIntegralConstructible P.coefficients.l E.val Y).ι ⋙
      (RationalizedSmoothAdjunction.internalization P.coefficients.l E.val Y
        ((D.coordinates E).abelian Y) m.reductionY).functor
  supportClosed : ∀ M :
      Condensed P E X,
    (constantModelBoundedConstructible (spIntegralCondensed P.coefficients.l E.val) Y ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)
      ((IntegralDirectImageTower.shriek P.coefficients.l E.val
        (SpTowerGamma.factorization j p)).obj ((condensedInclusion P E X).obj M))
  sourceClosed : ∀ K :
      Condensed P E Y,
    (constantModelBoundedConstructible (spIntegralCondensed P.coefficients.l E.val) X ⊓
      fun L ↦ _root_.DerivedCategory.finiteTorAmplitude _ L)
      ((condensedSource P D j p d E m).obj ((condensedInclusion P E Y).obj K))
  F : Condensed P E X ⥤
    Condensed P E Y
  F_eq : F = condensedRestriction P E
    (IntegralDirectImageTower.shriek P.coefficients.l E.val
      (SpTowerGamma.factorization j p)) supportClosed
  J : Condensed P E Y ⥤
    Condensed P E X
  J_eq : J = condensedRestriction P E (condensedSource P D j p d E m) sourceClosed
  adjunction : F ⊣ J
  supportComparison : FieldExtensionTowers.support P D j p d m ⋙ encodingY.functor ≅
    encodingX.functor ⋙ F
  sourceComparison : FieldExtensionTowers.puritySource P D j p d m ⋙ encodingX.functor ≅
    encodingY.functor ⋙ J
  unitComparison : ∀ M : FieldExtensionTowers.Integral P E X,
    encodingX.functor.map (A.adjunction.unit.app M) ≫
        sourceComparison.hom.app ((FieldExtensionTowers.support P D j p d m).obj M) ≫
        J.map (supportComparison.hom.app M) = adjunction.unit.app (encodingX.functor.obj M)
  counitComparison : ∀ K : FieldExtensionTowers.Integral P E Y,
    F.map (sourceComparison.hom.app K) ≫ adjunction.counit.app (encodingY.functor.obj K) =
      supportComparison.inv.app ((FieldExtensionTowers.puritySource P D j p d m).obj K) ≫
        encodingY.functor.map (A.adjunction.counit.app K)
  fixed_counit : ∀
    (G : Condensed P E Y ⥤
      Condensed P E X)
    (a : F ⊣ G)
    (K : Condensed P E Y),
    adjunction.counit.app K =
      F.map ((adjunction.rightAdjointUniq a).hom.app K) ≫ a.counit.app K

end IntegralStage

variable (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [QuasiSeparatedSpace Y]

/-- The actual tower twisted inverse image restricted to uniform constructible
finite-Tor towers. Membership is the recorded purity domain, not an extra hypothesis.
Source: purity-transport Step 2, local normalization paragraph.
(blueprint: def-pur-integral-counit-realization-data). -/
def towerSource (E : FieldShriekSystem.Index P)
    (m : FieldExtensionTowers.IntegralModel P D E j p d)
    [IsNoetherian X] [IsNoetherian Y] :
    SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) Y ⥤
      SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) X :=
  ObjectProperty.lift _
    (SpTowerGamma.source P.coefficients.l E.val (D.base E) (D.operations E)
      (D.coordinates E) (j ≫ p) m.twists d ⋙
        (SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
          ((D.coordinates E).abelian X)).inverse)
    m.realization.purity.source_mem


end AlgebraicGeometry.ProEtale.TransportIntegralCounit
