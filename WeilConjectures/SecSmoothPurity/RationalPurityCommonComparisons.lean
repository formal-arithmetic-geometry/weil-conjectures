/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.RationalPurityLineComparisons
import WeilConjectures.AlgebraicGeometry.CanonicalTateComparisons

/-! # Rational purity: CommonComparisons

Source: current blueprint, rational purity trace and coherence construction.
Existing declarations are retained in this compilation subdivision.
(blueprint: def-pur-rational-purity-common-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open WeilConjectures

attribute [-instance] integralOperationsSiteSmall
  integralReductionSiteEssentiallySmall
attribute [local irreducible] IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit IntegralAmbient.tensorTowerIso
  IntegralOnSlice.tower IntegralOnSlice.augmentation
  integralOperationsTensorTowerFunctor IntegralSystemRealization.tensorShifts

attribute [local irreducible] sfIntegralConstructible finiteTorConstructibleIntegral
  completedIntegralCoefficientSheafUnrestricted
  AlgebraicGeometry.Scheme.residueField
  PurCompactSupport.image sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  IntegralOnSlice.duality integralDerivedPullback integralCompletedTensor
  sfRationalScalarExtension HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Iso.trans Iso.prod Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.leftAdjoint
attribute [local instance 5000] integralTowerHasDerivedCategory scalarReductionTargetDerived
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom

namespace WeilConjectures.RationalPurityCoherence
open FrobeniusCoefficientTwists RationalSmoothPurityCanonical

attribute [local irreducible] integralSource integralTraceTranspose rationalSourceComparison
  smallModelIso rationalIso commonIso

attribute [local irreducible] rationalSource commonSource commonSourceComparison
  commonStageDerivedTensor completedIntegralCommRingSheafUnrestricted

section Composition
open ConstructibleExceptionalCoefficients
variable (P : PurityFiniteSetting.{u})
  {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
  (Sf : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (Sg : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := g))
  (Sfg : System P.coefficients.l P.coefficients.Qbar P.field
    P.coefficients.different (f := f ≫ g))

/-- Compact-support composition in the same adjunction coordinates as purity.
Source: proof Step 4, canonical c_g,f
(blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def rationalSupportComposition (s : FieldStage.{u} P.coefficients.l) :
    (Sf.ring.operation cf (.rational s)).F ⋙ (Sg.ring.operation cg (.rational s)).F ≅
      (Sfg.ring.operation cfg (.rational s)).F :=
  Functor.isoWhiskerRight (Sf.ring.rationalLeft cf s) _ ≪≫
    Functor.isoWhiskerLeft _ (Sg.ring.rationalLeft cg s) ≪≫
    sfFieldShriekCompositionRational P.field P.coefficients.l P.coefficients.different
      cf cg cfg s.carrier ≪≫ (Sfg.ring.rationalLeft cfg s).symm

/-- The canonical exceptional compositor c_g,f, namely the counit mate of the actual
proper/open compact-support compositor. It is defined independently of gamma.
Source: proof Step 4 (blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def rationalExceptionalComposition (s : FieldStage.{u} P.coefficients.l) :
    (Sfg.ring.operation cfg (.rational s)).G ≅
      (Sg.ring.operation cg (.rational s)).G ⋙ (Sf.ring.operation cf (.rational s)).G :=
  conjugateIsoEquiv (Sfg.ring.operation cfg (.rational s)).adjunction
    ((Sf.ring.operation cf (.rational s)).adjunction.comp
      (Sg.ring.operation cg (.rational s)).adjunction)
    (rationalSupportComposition P f g cf cg cfg Sf Sg Sfg s)

end Composition

section CommonSources
attribute [local irreducible] commonStageDerivedPullback
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Pullback at a literal finite stage, from its published object formula.
Source: proof Step 6 (blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def commonPullInclusion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (i : Index l Ω) (K : Stage l Ω Y i) :
    (commonStageDerivedPullback l Ω f).obj ⟨i,K⟩ ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion i).obj
        ((rationalDerivedPullback l (Coefficient.{u} l Ω i) f).obj K) :=
  by
    unfold commonStageDerivedPullback
    exact eqToIso
      ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 ⟨i, K⟩)

/-- The geometric source compositor at Qbar, represented by the rational compositor
at the input's own finite field and the prescribed source comparisons.
Source: proof Step 6 (blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def commonSourceComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (d e : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    (commonSource l Ω (f ≫ g) (d + e)).obj K ≅
      (commonSource l Ω f d).obj ((commonSource l Ω g e).obj K) :=
  commonSourceComparison l Ω (f ≫ g) (d + e) K ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      (rationalSourceComposition l (Coefficient.{u} l Ω K.stage) f g d e K.obj) ≪≫
    (commonSourceComparison l Ω f d
      ⟨K.stage,(rationalSource l (Coefficient.{u} l Ω K.stage) g e).obj K.obj⟩).symm ≪≫
    (commonSource l Ω f d).mapIso (commonSourceComparison l Ω g e K).symm

/-- The source comparison around an arbitrary Cartesian square at Qbar, represented
by the rational root/tensor/pullback comparison and the actual stage inclusions.
Source: proof Step 6 (blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def commonSourceBaseChange {X' X Y' Y : Scheme.{u}}
    (a : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (b : Y' ⟶ Y)
    [∀ x : X', Invertible (l : X'.residueField x)]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y', Invertible (l : Y'.residueField y)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (sq : IsPullback a f' f b) (d : ℕ)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω a).obj ((commonSource l Ω f d).obj K) ≅
      (commonSource l Ω f' d).obj ((commonStageDerivedPullback l Ω b).obj K) :=
  (commonStageDerivedPullback l Ω a).mapIso (commonSourceComparison l Ω f d K) ≪≫
    commonPullInclusion l Ω a K.stage _ ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      (rationalSourceBaseChange l (Coefficient.{u} l Ω K.stage) a f' f b sq d K.obj) ≪≫
    (commonSourceComparison l Ω f' d
      ⟨K.stage,(rationalDerivedPullback l (Coefficient.{u} l Ω K.stage) b).obj K.obj⟩).symm ≪≫
    (commonSource l Ω f' d).mapIso (commonPullInclusion l Ω b K.stage K.obj).symm

end CommonSources

attribute [local irreducible] commonStageDerivedPullback

section GeometricComposition
attribute [local irreducible] ScalarLocalization.category
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
open ConstructibleExceptionalCoefficients
open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [Z.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
  [QuasiCompact (Z ↘ Spec (.of P.field.k))]
  [IsSeparated (Z ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  [∀ z : Z, Invertible (P.coefficients.l : Z.residueField z)]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
  (Sf : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := f))
  (Sg : System P.coefficients.l P.coefficients.Qbar P.field P.coefficients.different (f := g))
  (Sfg : System P.coefficients.l P.coefficients.Qbar P.field
    P.coefficients.different (f := f ≫ g))

/-- Existence of the finite-stage common compact-support compositor.
Source: proof Steps 4--6 (blueprint: lem-pur-rational-common-support-composition-existence).
The construction conjugates the rational support compositor by the three counit-normalized
finite-stage comparisons and descends the resulting natural isomorphism. -/
theorem commonSupportComposition_exists :
    ∃ c : (Sf.ring.operation cf .closed).F ⋙ (Sg.ring.operation cg .closed).F ≅
        (Sfg.ring.operation cfg .closed).F,
      ∀ (i : Index P.coefficients.l P.coefficients.Qbar)
        (K : Stage P.coefficients.l P.coefficients.Qbar X i),
        (c.hom.app ⟨i,K⟩) =
          (Sg.ring.operation cg .closed).F.map ((Sf.common.commonComparison cf i).q.inv.app K) ≫
          (Sg.common.commonComparison cg i).q.inv.app
            ((Sf.ring.operation cf (.rational
              (commonField P.coefficients.l P.coefficients.Qbar i))).F.obj K) ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Z) i).map
            (by
              have e := rationalSupportComposition P f g cf cg cfg Sf Sg Sfg
                (commonField P.coefficients.l P.coefficients.Qbar i)
              have t := e.hom.app K
              exact (commonCategory_eq P Z i) ▸ t) ≫
          (Sfg.common.commonComparison cfg i).q.hom.app K := by
  sorry


/-- The common-stage support compositor is uniquely fixed by the rational compositor
and the counit-normalized inclusion comparisons. This does not use purity.
Source: proof Steps 4--6 (blueprint: def-pur-rational-purity-common-comparisons).
Proof: at (i,K), conjugate the inclusion of the rational support compositor by
q_f, q_g and q_gf. Their scalar cocycles and the proper/open coefficient comparison
identify these maps after every enlargement. Every common-stage arrow has a finite
representative, so rational naturality gives naturality. Descend the inverse formula
as well. Every object is a literal pair, so the component formula gives uniqueness. -/
theorem commonSupportComposition_existsUnique :
    ∃! c : (Sf.ring.operation cf .closed).F ⋙ (Sg.ring.operation cg .closed).F ≅
        (Sfg.ring.operation cfg .closed).F,
      ∀ (i : Index P.coefficients.l P.coefficients.Qbar)
        (K : Stage P.coefficients.l P.coefficients.Qbar X i),
        (c.hom.app ⟨i,K⟩) =
          (Sg.ring.operation cg .closed).F.map ((Sf.common.commonComparison cf i).q.inv.app K) ≫
          (Sg.common.commonComparison cg i).q.inv.app
            ((Sf.ring.operation cf (.rational
              (commonField P.coefficients.l P.coefficients.Qbar i))).F.obj K) ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Z) i).map
            (by
              have e := rationalSupportComposition P f g cf cg cfg Sf Sg Sfg
                (commonField P.coefficients.l P.coefficients.Qbar i)
              have t := e.hom.app K
              exact (commonCategory_eq P Z i) ▸ t) ≫
          (Sfg.common.commonComparison cfg i).q.hom.app K := by
  obtain ⟨c, hc⟩ := commonSupportComposition_exists P f g cf cg cfg Sf Sg Sfg
  refine ⟨c, hc, ?_⟩
  intro d hd
  apply Iso.ext
  apply NatTrans.ext
  funext j
  rcases j with ⟨i, K⟩
  exact (hd i K).trans (hc i K).symm

/-- The specified common-stage compact-support compositor.
Source: proof Step 6 (blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def commonSupportComposition :=
  (commonSupportComposition_existsUnique P f g cf cg cfg Sf Sg Sfg).exists.choose

/-- The Qbar exceptional compositor is the adjunction mate of support composition.
Source: proof Steps 4--6 (blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def commonExceptionalComposition :
    (Sfg.ring.operation cfg .closed).G ≅
      (Sg.ring.operation cg .closed).G ⋙ (Sf.ring.operation cf .closed).G :=
  conjugateIsoEquiv (Sfg.ring.operation cfg .closed).adjunction
    ((Sf.ring.operation cf .closed).adjunction.comp
      (Sg.ring.operation cg .closed).adjunction)
    (commonSupportComposition P f g cf cg cfg Sf Sg Sfg)

/-- The two geometric composition paths for the canonical rational purity maps.
Source: thm-pur-composition-coherence, rationalization
(blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def RationalCompositionClause (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension (d + e) (f ≫ g)] : Prop :=
  ∀ K : sfRationalConstructibleCategory P.coefficients.l P.extension Z,
    (rationalIso P (f ≫ g) cfg Sfg (d + e) K).hom =
      (rationalSourceComposition P.coefficients.l P.extension f g d e K).hom ≫
      (rationalSource P.coefficients.l P.extension f d).map
        (rationalIso P g cg Sg e K).hom ≫
      (rationalIso P f cf Sf d
        ((Sg.ring.operation cg (.rational (AdicSmoothDualizing.fieldStage P))).G.obj K)).hom ≫
      (rationalExceptionalComposition P f g cf cg cfg Sf Sg Sfg
        (AdicSmoothDualizing.fieldStage P)).inv.app K

/-- Both composition paths in the actual common-stage category, with the counit mate
c_g,f and the root-normalized source compositor.
Source: thm-pur-composition-coherence, common-stage descent
(blueprint: def-pur-rational-purity-common-comparisons). -/
@[irreducible]
def CommonCompositionClause (d e : ℕ)
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension (d + e) (f ≫ g)] : Prop :=
  ∀ K : generalAlgebraicallyClosedConstructibleCategory
      P.coefficients.l P.coefficients.Qbar Z,
    (commonIso P (f ≫ g) cfg Sfg (d + e) K).hom =
      (commonSourceComposition P.coefficients.l P.coefficients.Qbar f g d e K).hom ≫
      (commonSource P.coefficients.l P.coefficients.Qbar f d).map
        (commonIso P g cg Sg e K).hom ≫
      (commonIso P f cf Sf d ((Sg.ring.operation cg .closed).G.obj K)).hom ≫
      (commonExceptionalComposition P f g cf cg cfg Sf Sg Sfg).inv.app K

end GeometricComposition

end WeilConjectures.RationalPurityCoherence
