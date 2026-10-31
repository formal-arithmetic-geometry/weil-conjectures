/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenCounitComparisons

/-! # Completed open comparison support data

Source: purity transport, Steps 2--3; support constructions for the specified
open-counit normalization (blueprint: def-pur-condensed-open-counit-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures
open CondensedERealization CompactSupportCondensedRealization
namespace WeilConjectures.CondensedOpenCounitRealization

variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

open CondensedExceptionalReconstruction

/-- The coefficient-realization and strict-system models used to spell out the maps.
The reduction equality chooses the existing canonical geometric calculus; the bridge
and realization model retain its ordinary section and K-flat normalizations.
Source: blueprint purity transport, Steps 2--3
(blueprint: def-pur-condensed-open-counit-comparisons). -/
structure Models where
  coefficient : CoefficientData l (Field.{u} l) k
  operations : IntegralSystemRealization.Operations l (Field.{u} l)
  model : IntegralSystemRealization.RealizationModel l (Field.{u} l) operations
  bridge : IntegralSystemRealization.CanonicalBridge l (Field.{u} l) operations
  reduction_eq : coefficient.reduction = IntegralSystemRealization.calculus l (Field.{u} l)

/-- The supplied parent comparison, transported only along equality of its reduction.
Source: blueprint purity transport, trivial compactification
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def supportAt (C : Models l k) (U Y : Base k) (j : U.scheme ⟶ Y.scheme)
    [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    RealizationAt l (Field.{u} l) k C.coefficient.realization
      (IntegralSystemRealization.calculus l (Field.{u} l)) U Y j
      (trivialCompactification k j) :=
  C.reduction_eq ▸ C.coefficient.atCompactification U Y j (trivialCompactification k j)

/-- The specified reconstructed compact support for (j,id).
Source: blueprint purity transport, trivial compactification
(blueprint: def-pur-condensed-open-counit-comparisons). -/
abbrev support (C : Models l k) (U Y : Base k) (j : U.scheme ⟶ Y.scheme)
    [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :=
  integralSupport l (Field.{u} l) (trivialCompactification k j)
    (IntegralSystemRealization.calculus l (Field.{u} l)) (supportAt l k C U Y j).integral

/-- The actual formula d L(alpha) u, before forgetting the coefficient coordinates.
Here the last two factors are d = L(r inverse) u inverse; the system identity
unitor removes only the proper identity factor of alpha. No evaluated morphisms
are used to choose a lift.
Source: blueprint purity transport, specified b normalization
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def integralIdentificationEncoded (C : Models l k) (U Y : Base k)
    (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (M : Integral l (Field.{u} l) U.scheme) :=
  (IntegralSystemRealization.calculus l (Field.{u} l) Y.scheme).adjunction.unit.app
      ((purCoefficientModel l (Field.{u} l) Y.scheme).functor.obj
        ((support l k C U Y j).obj M).obj) ≫
    (coefficientSequenceLimit l (Field.{u} l) Y.scheme).map
      ((alpha l (Field.{u} l) (trivialCompactification k j)
        (IntegralSystemRealization.calculus l (Field.{u} l))
        (supportAt l k C U Y j).integral).app M) ≫
    (coefficientSequenceLimit l (Field.{u} l) Y.scheme).map
      ((SemilinearProperOpen.sId (quotientRings l (Field.{u} l))
        (quotientMaps l (Field.{u} l)) Y.scheme).hom.app _) ≫
    (coefficientSequenceLimit l (Field.{u} l) Y.scheme).map
      ((C.bridge.shriek l (Field.{u} l) j).inv.app _) ≫
    (coefficientSequenceLimit l (Field.{u} l) Y.scheme).map
      ((C.model.openReduction l (Field.{u} l) j).app
        ((purCoefficientModel l (Field.{u} l) U.scheme).functor.obj M.obj)) ≫
    GeneratorReduction.inverseOrZero
      ((IntegralSystemRealization.calculus l (Field.{u} l) Y.scheme).adjunction.unit.app
        ((IntegralSystemRealization.ringedOpen l (Field.{u} l) j).obj
          ((purCoefficientModel l (Field.{u} l) U.scheme).functor.obj M.obj)))

/-- The same integral identification in the constructible full subcategory.
Source: blueprint purity transport, specified b normalization
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def integralIdentification (C : Models l k) (U Y : Base k)
    (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (h : Preserves l k U Y j) (M : Integral l (Field.{u} l) U.scheme) :
    (support l k C U Y j).obj M ⟶ (extension l k h).obj M :=
  ObjectProperty.homMk
    ((purCoefficientModel l (Field.{u} l) Y.scheme).unitIso.hom.app _ ≫
      (purCoefficientModel l (Field.{u} l) Y.scheme).inverse.map
        (integralIdentificationEncoded l k C U Y j M))

/-- The specified b: V(t inverse), then extension of the parent's a, then the
original coefficient projection and the canonical proper identity unitor.
Source: blueprint purity transport, specified b normalization
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def extensionComparison (C : Models l k) (U Y : Base k)
    (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (h : Preserves l k U Y j) (M : Integral l (Field.{u} l) U.scheme) :=
  ((realization l k C.coefficient.realization Y).map
      (GeneratorReduction.inverseOrZero (integralIdentification l k C U Y j h M))).hom ≫
    (omegaScalar l (Field.{u} l) (embedding l) Y.scheme).map
      ((supportAt l k C U Y j).realization.hom.app (ScalarLocalization.mk M)) ≫
    (condensedProjection (omegaMap l (Field.{u} l) (embedding l))
      (trivialCompactification k j)).app
        ((C.coefficient.realization.atObject U).realization.functor.obj
          (ScalarLocalization.mk M)).obj ≫
    (removeIdentity (Profinite.padicAlgClRingObj l) Y.scheme).hom.app _

/-- The parent's a is the specific proper/open factorization, with its actual
unit-normalized open factor, rather than an arbitrary natural isomorphism.
Source: blueprint purity transport, proof Step 3; compact-support factor normalization
(blueprint: def-pur-condensed-open-counit-comparisons). -/
def FactorNormalized (C : Models l k) : Prop :=
  ∀ (U Y : Base k) (j : U.scheme ⟶ Y.scheme) [IsOpenImmersion j]
    [j.IsOver (Spec (.of k))] (M : Integral l (Field.{u} l) U.scheme),
    (supportAt l k C U Y j).realization.hom.app (ScalarLocalization.mk M) =
      CompactSupportFactorNormalization.parentFactorization l (Field.{u} l)
        C.operations C.model C.bridge (trivialCompactification k j)
        (supportAt l k C U Y j).integral
        (C.coefficient.realization.atObject U) (C.coefficient.realization.atObject Y)
        (C.coefficient.realization.atObject Y) M


end WeilConjectures.CondensedOpenCounitRealization
