/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.SmoothPurity.Sf.SfRationalLocalizationOrthogonality
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.SmoothPurity.Sf.SfQbarLocalizationExactDescent
import WeilConjectures.SmoothPurity.Sf.SfQbarLocalizationFiniteCoherence
import all WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage

/-! # Localization on the raw common-stage coefficient categories

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, algebraically closed stage
(blueprint: lem-sf-qbar-localization-common-stage).

The records package the asserted descent and its Hom comparison. They introduce
neither another coefficient category nor a Karoubi envelope. The open compactification
is (j,id_X). Closed direct image uses the normalized ordinary direct-image functor
and the adjunction mate of the pullback comparison.

## Main definitions and statement

* `SfQbarLocalizationExactAction`: exactness and shift/unit coherence.
* `SfQbarLocalizationHomComparison`: the explicitly transported cross-stage Hom system.
* `SfQbarLocalizationDescent`: the descended functors, adjunction maps and triangles.
* `sfQbarLocalizationCommonStage`: their existence for complementary immersions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
namespace WeilConjectures
attribute [local irreducible] sfIntegralConstructible FrobeniusExchange.models
  sfRationalTriangulationDatum
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient)

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

set_option linter.flexible false in
section HomComparison
variable {X U Z : Scheme.{u}}
  (J : (stageSystem l Ω U).Morphism (stageSystem l Ω X))
  (I : (stageSystem l Ω Z).Morphism (stageSystem l Ω X))
  (N : Pair l Ω U) (M : Pair l Ω Z) (m : ℤ)

set_option backward.isDefEq.respectTransparency false in
end HomComparison

section Descent
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Z U : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
  (i : Z ⟶ X) (j : U ⟶ X) [i.IsOver (Spec (.of D.k))] [j.IsOver (Spec (.of D.k))]
  [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ z : Z, Invertible (l : Z.residueField z)]
  [∀ t : U, Invertible (l : U.residueField t)]

end Descent

/-- Residue-field invertibility obtained from the given characteristic hypothesis,
without adding geometric invertibility hypotheses to the localization statement.
Source: the global finite-field datum and the algebraically closed-stage paragraph
(blueprint: lem-sf-qbar-localization-common-stage). -/
@[instance_reducible] def sfQbarLocalizationResidueInvertible
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u}) (t : W ⟶ Spec (.of D.k)) (x : W) :
    Invertible (l : W.residueField x) :=
  let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ t.appTop ≫ W.Γevaluation x).hom
  (Eq.mp (congrArg IsUnit (map_natCast φ l))
    ((PurCompactSupport.coefficientPrimeUnit l D hl).map φ)).invertible

end WeilConjectures
