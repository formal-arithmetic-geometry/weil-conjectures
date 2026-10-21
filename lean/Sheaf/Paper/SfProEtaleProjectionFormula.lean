/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteRingCompactSupportProjectionMap
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.IntegralResidueTor
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.SfRationalizationKaroubi
import WeilConjectures.Compactification.Noetherian
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-! # The pro-etale projection formula at the four coefficient stages

Source: Weil blueprint main-20261015, sec-six-functors/sk-thm-sf-pf-proetale,
statement and proof (blueprint: sk-thm-sf-pf-proetale).

## Main definitions

* `SfProEtaleProjection.Origin`: the recorded fixed-scalar etale-origin witness,
  transported to intrinsic finite coefficients by the existing equivalence.
* `SfProEtaleProjection.integralMap`: the completed projection, characterized by
  the completion-unit equation, in the actual integral constructible category.

## Main statements

* `SfProEtaleProjection.integralDomains`: the typing and completion-unit facts
  needed to write this map, including for every integral representative of a raw
  rational object.
* `sf_proetale_projection_formula`: invertibility at finite, integral, raw rational,
  and common finite-field stages, for every chosen compactification.

The ordinary projection used below is the existing proper-counit/open-extension
composite, with its representative-normalized tensor and pullback comparisons.
Completed tensor is completion of ordinary tensor. Its unit identity determines
its projection; completion of the pullback factor is absorbed by completed tensor.
The field maps are its actual localization and common-stage inclusion, respectively.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace SfProEtaleProjection

/-- A retained bounded constructible etale origin in the recorded fixed-scalar
presentation, together with the canonical intrinsic realization of its target.
This packages the existing witness; it does not choose a new inverse image.
Source: blueprint finite-coefficient clause and def-weil-pbc-etale-origin-witness
(blueprint: sk-thm-sf-pf-proetale). -/
structure Origin (W : Scheme.{u}) (R : Type u) [CommRing R] [Finite R]
    (K : proEtaleDerivedCategory W R) where
  object : DerivedCategory.Plus
    (Sheaf (ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))
  witness : FixedEtaleOriginWitness W (ULift.{u + 1, u} R) object
  constructible : Etale.DerivedCategory.isBoundedConstructible
    (ULift.{u + 1, u} R) W witness.complex.obj
  realization : (sfIntrinsicModuleEquivalence W R).functor.mapDerivedCategory.obj
    object.obj ≅ K

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing signed K-flat tensor model over the completed coefficient sheaf.
Source: blueprint integral coefficient clause; Stacks 07A4
(blueprint: sk-thm-sf-pf-proetale). -/
abbrev TensorModel (W : Scheme.{u}) :=
  ProEtaleTensorModel W ((PurCompactSupport.completed l E).ring W)

/-- Ordinary presentation of the completed projection's source before its unit.
Source: blueprint projection display (blueprint: sk-thm-sf-pf-proetale). -/
def ordinarySource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aY : TensorModel l E Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :=
  aY.tensor.obj ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K, L)

/-- Ordinary tensor inside the compact-support projection's target.
Its completion also computes completed tensor with completed pullback: inserting
that factor's completion unit becomes invertible after tensor completion.
Source: blueprint projection display; Stacks 099N
(blueprint: sk-thm-sf-pf-proetale). -/
def ordinaryInner {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : TensorModel l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :=
  aX.tensor.obj (K, (PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj L)

/-- The completed tensor on the source of the projection.
The completion and unit are the actual positive-quotient Roos construction.
Source: blueprint integral clause; Bhatt--Scholze Definition 3.4.10
(blueprint: sk-thm-sf-pf-proetale). -/
def completedSource {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aY : TensorModel l E Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :=
  (IntegralOnSlice.completion l E Y none).obj (ordinarySource l E c aY K L)

/-- Compact support of the completed tensor on the target of the projection.
Source: blueprint integral clause; Bhatt--Scholze Definition 3.4.10
(blueprint: sk-thm-sf-pf-proetale). -/
def completedTarget {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : TensorModel l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :=
  (PurCompactSupport.image (PurCompactSupport.completed l E) c).obj
    ((IntegralOnSlice.completion l E X none).obj (ordinaryInner l E f aX K L))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

include D hl in
/-- Typing facts for the canonical completed projection, without structural
separatedness assumptions on X or Y. They hold for every integral constructible
representative; thus raw rationalization has no additional lattice restriction.
Source: blueprint proof steps 1, 3, 4; Bhatt--Scholze Sections 6.5 and 6.7
(blueprint: sk-thm-sf-pf-proetale).

Proof (postponed): finite type over k gives Noetherianness, and l differs from
its characteristic, hence is invertible in all residue fields. The integral
residue-Tor theorem gives a uniform finite-Tor interval for every constructible
integral input. At every positive quotient choose its bounded constructible etale
origin. Open extension by zero and proper direct image give bounded constructible
compact support, with uniform bounds from the finite cohomological dimension.
Use the strict quotient transitions and their Roos triangle to reconstruct the
complete integral object. The same argument for finite tensor and pullback gives
the completed target. For the ordinary source, a finite stratification and bounded
flat perfect models of the second input identify its tensor-completion unit with
the unit of the first input tensored with those models; it is invertible. This is
the ordinary-to-completed normalization, not faithfulness of finite reductions.
The completed source and target consequently have complete constructible
reductions and a common cohomological bound, exactly the recorded predicate. -/
theorem integralDomains
    (aX : TensorModel l E X) (aY : TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) :
    IsIso ((IntegralOnSlice.completionUnit l E Y none).app
      (ordinarySource l E c aY K.obj L.obj)) ∧
    sfIntegralConstructible l E Y (completedSource l E c aY K.obj L.obj) ∧
    sfIntegralConstructible l E Y (completedTarget l E c aX K.obj L.obj) := by
  sorry

/-- The actual completed projection in the intrinsic completed category.
It is the unique extension of the ordinary proper-counit/open projection across
its source completion unit. The target unit is applied before compact support.
Thus eta_source followed by this map equals ordinary PF followed by Rf! eta_inner.
This is precisely the completed-adjunction normalization of def-exchange-projection;
no projection arrow or arbitrary isomorphism is supplied as an input.
Source: blueprint projection display; Stacks 099N; completed projection unit equation
(blueprint: sk-thm-sf-pf-proetale). -/
def integralMap
    (aX : TensorModel l E X) (aZ : TensorModel l E c.Z) (aY : TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) :
    (⟨completedSource l E c aY K.obj L.obj,
      (integralDomains l E D hl f c aX aY K L).2.1⟩ :
        sfIntegralConstructibleCategory l E Y) ⟶
    (⟨completedTarget l E c aX K.obj L.obj,
      (integralDomains l E D hl f c aX aY K L).2.2⟩ :
        sfIntegralConstructibleCategory l E Y) :=
  letI := (integralDomains l E D hl f c aX aY K L).1
  ObjectProperty.homMk
    (inv ((IntegralOnSlice.completionUnit l E Y none).app
        (ordinarySource l E c aY K.obj L.obj)) ≫
      (((PurCompactSupport.projectionMap (PurCompactSupport.completed l E) c aX aZ aY
        (PurCompactSupport.completedPull_comp l E c.i c.g)).app K.obj).app L.obj) ≫
      (PurCompactSupport.image (PurCompactSupport.completed l E) c).map
        ((IntegralOnSlice.completionUnit l E X none).app
          (ordinaryInner l E f aX K.obj L.obj)))

end SfProEtaleProjection

/-- Projection formula on the pro-etale realization at all four coefficient stages.
The first clause retains bounded constructible etale origins and the intrinsic
finite-Tor predicates. Positive exponent n+1 ranges over all allowed finite levels.
The second uses complete integral finite-Tor inputs, including their witnessed
finite reductions. Its map is the completed-unit extension of the specified
proper-counit/open-extension composite, in the actual integral full subcategory.
The third localizes that map on every integral representative of the raw rational
category (which has exactly those objects). The fourth takes its class under each
common-stage inclusion into the literal-pair algebraically closed category.
Any two pairs admit such a common finite stage, so this clause includes inputs
initially represented at different fields. No idempotents or lattices are added.

Source: Weil blueprint main-20261015, sec-six-functors/sk-thm-sf-pf-proetale,
statement and five-step proof (blueprint: sk-thm-sf-pf-proetale).

Proof (postponed):
1. The finite-type finite-field geometry is Noetherian. Nagata gives the chosen
compactification; for any supplied compactification its open immersion is qc.
2. At finite coefficients use the retained etale origins. Comparison reflects
finite Tor amplitude and identifies the proper counit and inverse open projection
with the etale compact-support projection map. The etale projection formula and
full faithfulness of D+ comparison prove that this very map is invertible.
The intrinsic equivalence preserves and reflects invertibility. Finite Tor bounds
and left t-exact direct image give bounded-below endpoints, so the map lifts to D+.
3. On the completed integral domain apply thm-sf-pf-adic at this compactification,
using the uniform Tor intervals in finiteTorConstructibleIntegral and the supplied
finite origins. Its completed projection is characterized by the same unit equation
as integralMap, hence is that map, and is invertible.
4. The residue-Tor theorem supplies the integral condition for every integral
constructible representative. Raw scalar localization sends the completed map
and its inverse to inverse morphisms. Its objects are unchanged; this proves
the rational clause without a separate existence-of-lattice hypothesis.
5. Represent both algebraically closed objects over their finite coefficient
compositum, apply step 4 there, and include its map and inverse. Their composites
are identities already at that stage, hence in the directed-colimit Hom groups.
The argument works for every common stage and every compactification. -/
theorem sf_proetale_projection_formula
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
      (n : ℕ)
      (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)))
      (L : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)))
      (_hK : finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X K)
      (_hL : finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y L)
      (_wK : SfProEtaleProjection.Origin X (Padic.coefficientExtensionRing l E (n + 1)) K)
      (_wL : SfProEtaleProjection.Origin Y (Padic.coefficientExtensionRing l E (n + 1)) L),
      let P := Arrow.mk (((finiteRingCompactSupportProjection
        (Padic.coefficientExtensionRing l E (n + 1)) c).app K).app L)
      ∃ (hS : (DerivedCategory.TStructure.t (C := proEtaleRingModules Y
          (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))).plus P.left)
        (hT : (DerivedCategory.TStructure.t (C := proEtaleRingModules Y
          (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))).plus P.right),
        IsIso (ObjectProperty.homMk P.hom :
          (⟨P.left, hS⟩ : DerivedCategory.Plus (proEtaleRingModules Y
            (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))) ⟶
          (⟨P.right, hT⟩ : DerivedCategory.Plus (proEtaleRingModules Y
            (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1))))))) ∧
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
      (aX : SfProEtaleProjection.TensorModel l E X)
      (aZ : SfProEtaleProjection.TensorModel l E c.Z)
      (aY : SfProEtaleProjection.TensorModel l E Y)
      (K : sfIntegralConstructibleCategory l E X)
      (L : sfIntegralConstructibleCategory l E Y)
      (_hK : finiteTorConstructibleIntegral l E X K.obj)
      (_hL : finiteTorConstructibleIntegral l E Y L.obj)
      (_wK : ∀ n : ℕ, SfProEtaleProjection.Origin X
        (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E X n).obj K.obj))
      (_wL : ∀ n : ℕ, SfProEtaleProjection.Origin Y
        (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E Y n).obj L.obj)),
      IsIso (SfProEtaleProjection.integralMap l E D hl f c aX aZ aY K L)) ∧
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
      (aX : SfProEtaleProjection.TensorModel l E X)
      (aZ : SfProEtaleProjection.TensorModel l E c.Z)
      (aY : SfProEtaleProjection.TensorModel l E Y)
      (K : sfIntegralConstructibleCategory l E X)
      (L : sfIntegralConstructibleCategory l E Y),
      IsIso ((sfRationalConstructibleLocalization l E Y).map
        (SfProEtaleProjection.integralMap l E D hl f c aX aZ aY K L))) ∧
    (∀ (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
      (F : Padic.FiniteCoefficientFields l Ω)
      (aX : SfProEtaleProjection.TensorModel l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X)
      (aZ : SfProEtaleProjection.TensorModel l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) c.Z)
      (aY : SfProEtaleProjection.TensorModel l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Y)
      (K : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X)
      (L : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Y),
      IsIso ((GeneralAlgebraicallyClosedCoefficients.inclusion (Y := Y) F).map
        ((sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) Y).map
            (SfProEtaleProjection.integralMap l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
                D hl f c aX aZ aY K L)))) := by
  sorry

end WeilConjectures
