/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.IntegralAdjunctionBijection
public import Sheaf.Paper.FieldShriekSystemComparison
public import Sheaf.Paper.FieldExtensionSourceNormalization
public import Sheaf.Paper.SfScalarExtensionComposition
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison

/-! # FieldExtensionIntegralModels

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-integral-models).

## Main definitions and statements

The declarations below package the named functors, comparisons and equations of
the indicated clauses, using the published coefficient and geometric models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers

/-- The source's integral category, with its completed ring and uniform reduction bound.
Source: clause (1) (blueprint: def-sp-field-extension-integral-models). -/
abbrev Integral (P : PurityFiniteSetting.{u}) (E : FieldShriekSystem.Index P)
    (T : Scheme.{u}) := sfIntegralConstructibleCategory P.coefficients.l E.val T

/-- The raw rational category; no idempotents or objects are adjoined.
Source: clause (3) (blueprint: def-sp-field-extension-integral-models). -/
abbrev Rational (P : PurityFiniteSetting.{u}) (E : FieldShriekSystem.Index P)
    (T : Scheme.{u}) := sfRationalConstructibleCategory P.coefficients.l E.val T

/-- The specified completed integral scalar extension on constructible objects.
Source: clause (1) (blueprint: def-sp-field-extension-integral-models). -/
abbrev scalar (P : PurityFiniteSetting.{u}) {E F : FieldShriekSystem.Index P}
    (h : E ≤ F) (T : Scheme.{u}) :=
  sfConstructibleIntegralScalarExtension P.field.p P.coefficients.l P.coefficients.different
    E.val F.val (IntermediateField.inclusion h) T

/-- Rational scalar extension on integral representatives and tensor Hom groups.
Source: clause (3) (blueprint: def-sp-field-extension-integral-models). -/
abbrev rationalScalar (P : PurityFiniteSetting.{u}) {E F : FieldShriekSystem.Index P}
    (h : E ≤ F) (T : Scheme.{u}) :=
  sfRationalScalarExtension P.coefficients.l E.val T P.field.p P.coefficients.different
    F.val (IntermediateField.inclusion h)

/-- One recorded integral realization, including its tower adjunction, finite adjunctions,
reconstruction, and purity map. These are presentation data for the functors in the node.
Source: clause (2), det-sp-integral-adjunction-bijection
(blueprint: def-sp-field-extension-integral-models). -/
structure IntegralModel (P : PurityFiniteSetting.{u}) (D : FieldShriekSystem.Models P)
    (E : FieldShriekSystem.Index P) {X Z Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ) where
  sourceNormalization : SourceNormalization P E.val (j ≫ p) d
  twists : SpChartAdmissibility.Twists P.coefficients.l E.val X
  reductionX : SpReductionTower P.coefficients.l E.val X ((D.coordinates E).abelian X)
  normalizationX : SpNormalizedEquivalence P.coefficients.l E.val X
    ((D.coordinates E).abelian X) reductionX
  reductionY : SpReductionTower P.coefficients.l E.val Y ((D.coordinates E).abelian Y)
  normalizationY : SpNormalizedEquivalence P.coefficients.l E.val Y
    ((D.coordinates E).abelian Y) reductionY
  supportClosed : ∀ M : SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) X,
    spConstructibleTorTowers P.coefficients.l E.val Y ((D.coordinates E).abelian Y)
      ((SpTowerCalculus.F P.coefficients.l E.val (D.base E) (D.operations E)
        (D.coordinates E) (SpTowerGamma.factorization j p)).obj M.obj)
  exceptional : SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) Y ⥤
    SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) X
  adjunction : SpTowerGluing.support P.coefficients.l E.val (D.base E) (D.operations E)
    (D.coordinates E) (SpTowerGamma.factorization j p) supportClosed ⊣ exceptional
  levels : SpTowerGluing.Levels P.coefficients.l E.val (D.base E) (D.operations E)
    (D.coordinates E) (SpTowerGamma.factorization j p) supportClosed exceptional adjunction
  realization : SpIntegralAdjunction.realizationResult P.coefficients.l E.val P.field j p d
    (D.base E) (D.operations E) (D.coordinates E) twists reductionX normalizationX
    reductionY normalizationY supportClosed exceptional adjunction levels

/-- Finite type over the fixed field makes X compact.
Source: standing finite-type setting (blueprint: def-sp-field-extension-integral-models). -/
abbrev compactSpace (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    [X.Over (Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k))

/-- A separated scheme over the fixed field is quasi-separated.
Source: standing separated setting (blueprint: def-sp-field-extension-integral-models). -/
abbrev quasiSeparatedSpace (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))] : QuasiSeparatedSpace Y :=
  quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of P.field.k))

/-- The specified open/proper factorization is a compactification.
Source: clause (2), fixed compactification (blueprint: def-sp-field-extension-integral-models). -/
instance hasCompactification {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p] :
    HasCompactification (j ≫ p) := (SpTowerGamma.factorization j p).hasCompactification

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

/-- Compact support is the recorded separately derived completed compactification image.
Source: clause (2) (blueprint: def-sp-field-extension-integral-models). -/
abbrev support {E : FieldShriekSystem.Index P} (m : IntegralModel P D E j p d) :=
  SpIntegralAdjunction.support P.coefficients.l E.val (SpTowerGamma.factorization j p)
    m.realization.support_closed

/-- The exceptional functor is exactly L_X G_bullet red_Y of the recorded realization.
Source: clause (2) (blueprint: def-sp-field-extension-integral-models). -/
abbrev exceptional {E : FieldShriekSystem.Index P} (m : IntegralModel P D E j p d) :=
  SpIntegralAdjunction.right P.coefficients.l E.val (D.base E) (D.coordinates E)
    m.reductionX m.normalizationX m.reductionY m.realization.reductionY m.exceptional
    m.realization.closed

/-- Reduction of integral objects, in the original strict-system derived category.
Source: clause (2) (blueprint: def-sp-field-extension-integral-models). -/
abbrev reduceX {E : FieldShriekSystem.Index P} (m : IntegralModel P D E j p d) :=
  SpIntegralAdjunction.reduce P.coefficients.l E.val X ((D.coordinates E).abelian X)
    m.reductionX m.realization.reductionX

/-- Reduction of integral objects on Y, including all quotient transitions.
Source: clause (2) (blueprint: def-sp-field-extension-integral-models). -/
abbrev reduceY {E : FieldShriekSystem.Index P} (m : IntegralModel P D E j p d) :=
  SpIntegralAdjunction.reduce P.coefficients.l E.val Y ((D.coordinates E).abelian Y)
    m.reductionY m.realization.reductionY

/-- Integral reduction in the recorded section-preserving sequence-site coordinates.
Source: clause (2) (blueprint: def-sp-field-extension-integral-models). -/
abbrev sectionX {E : FieldShriekSystem.Index P} (m : IntegralModel P D E j p d) :=
  reduceX P D j p d m ⋙
    (spConstructibleTorTowers P.coefficients.l E.val X ((D.coordinates E).abelian X)).ι ⋙
      (SpTowerCalculus.realization P.coefficients.l E.val (D.base E)
        X ((D.coordinates E).abelian X)).functor

/-- Integral reduction on Y in the same sequence-site coordinates.
Source: clause (2) (blueprint: def-sp-field-extension-integral-models). -/
abbrev sectionY {E : FieldShriekSystem.Index P} (m : IntegralModel P D E j p d) :=
  reduceY P D j p d m ⋙
    (spConstructibleTorTowers P.coefficients.l E.val Y ((D.coordinates E).abelian Y)).ι ⋙
      (SpTowerCalculus.realization P.coefficients.l E.val (D.base E)
        Y ((D.coordinates E).abelian Y)).functor

/-- The smooth purity source is the published completed pullback, twist and shift.
Its membership proof is provided by the recorded integral adjunction realization.
Source: clauses (2)--(3) (blueprint: def-sp-field-extension-integral-models). -/
def puritySource {E : FieldShriekSystem.Index P} (m : IntegralModel P D E j p d) :=
  ObjectProperty.lift (sfIntegralConstructible P.coefficients.l E.val X)
    (SpTwistedPullback.source P.coefficients.l E.val (j ≫ p) (d : ℤ) (2 * (d : ℤ)))
    m.realization.source_complete

/-- The actual integral purity component: reconstruction unit followed by total limit
of the source comparison and the tower gamma, with the section equivalence unit inserted.
Source: clause (2), det-sp-integral-adjunction-bijection, Purity
(blueprint: def-sp-field-extension-integral-models). -/
def gamma {E : FieldShriekSystem.Index P} (m : IntegralModel P D E j p d)
    (K : Integral P E Y) :
    (puritySource P D j p d m).obj K ⟶ (exceptional P D j p d m).obj K :=
  letI := m.realization.noetherianX
  letI := m.realization.noetherianY
  ObjectProperty.homMk
    (m.normalizationX.adjunction.unit.app
        ((SpTwistedPullback.source P.coefficients.l E.val (j ≫ p)
          (d : ℤ) (2 * (d : ℤ))).obj K) ≫
      (SpIntegralAdjunction.limit P.coefficients.l E.val X
        ((D.coordinates E).abelian X) m.reductionX m.normalizationX).map
        ((SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
          ((D.coordinates E).abelian X)).unitIso.hom.app _ ≫
          (SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
            ((D.coordinates E).abelian X)).inverse.map
              (m.realization.sourceComparison.hom.app K ≫
                SpTowerGamma.gamma P.coefficients.l E.val (D.base E) (D.operations E)
                  (D.coordinates E) (SpTowerGamma.factorization j p) m.twists d
                  m.realization.purity.tensorX m.realization.purity.tensorY m.supportClosed
                  m.exceptional m.adjunction m.realization.purity.unit_mem
                  m.realization.purity.orientation ((reduceY P D j p d m).obj K)
                  (m.realization.purity.tensor_mem _) (m.realization.purity.projection_iso _)) ≫
          (SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
            ((D.coordinates E).abelian X)).unitIso.inv.app _))

/-- The original strict-tower scalar functor, conjugated by section equivalences.
Source: clause (2) (blueprint: def-sp-field-extension-integral-models). -/
abbrev towerScalar {E F : FieldShriekSystem.Index P} (h : E ≤ F) (T : Scheme.{u}) :=
  (SpTowerCalculus.realization P.coefficients.l E.val (D.base E) T
    ((D.coordinates E).abelian T)).functor ⋙ (D.scalars E F h T).T ⋙
      (SpTowerCalculus.realization P.coefficients.l F.val (D.base F) T
        ((D.coordinates F).abelian T)).inverse

/-- The scalar associator is the published balanced tensor associator.
Source: clause (2), E subset F subset L (blueprint: def-sp-field-extension-integral-models). -/
abbrev scalarAssoc {E F L : FieldShriekSystem.Index P} (h : E ≤ F) (k : F ≤ L)
    (T : Scheme.{u}) :=
  sfIntegralScalarComp P.coefficients.l E.val F.val (IntermediateField.inclusion h) T
    P.field.p P.coefficients.different L.val (IntermediateField.inclusion k)

/-- The rational associator is the localization of that same integral associator.
Source: clause (3) (blueprint: def-sp-field-extension-integral-models). -/
abbrev rationalScalarAssoc {E F L : FieldShriekSystem.Index P} (h : E ≤ F) (k : F ≤ L)
    (T : Scheme.{u}) :=
  sfRationalScalarComp P.coefficients.l E.val F.val (IntermediateField.inclusion h) T
    P.field.p P.coefficients.different L.val (IntermediateField.inclusion k)

end AlgebraicGeometry.ProEtale.FieldExtensionTowers

namespace CategoryTheory

/-- Explicit unit and counit compatibility for a scalar comparison of adjunctions.
Source: clause (2) (blueprint: def-sp-field-extension-integral-models). -/
structure FieldScalarAdjunctionComparison
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (SX : A ⥤ C) (SY : B ⥤ D) where
  left : F ⋙ SY ≅ SX ⋙ F'
  right : G ⋙ SX ≅ SY ⋙ G'
  unit : ∀ M : A,
    SX.map (adj.unit.app M) ≫ right.hom.app (F.obj M) ≫
      G'.map (left.hom.app M) = adj'.unit.app (SX.obj M)
  counit : ∀ K : B,
    F'.map (right.hom.app K) ≫ adj'.counit.app (SY.obj K) =
      left.inv.app (G.obj K) ≫ SY.map (adj.counit.app K)

end CategoryTheory

