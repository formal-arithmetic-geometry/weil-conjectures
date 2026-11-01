/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Projection--evaluation pairing and its three Weil transposes

Source: blueprint, prop-weil-operations, evaluation/adjunction construction of the formal
Verdier exchange (blueprint: lem-pod-verdier-pairing-three-transposes).

The supplied-domain interfaces below retain the underlying tensor--Hom adjunctions,
the evaluation normalization, and the underlying units of the lifted adjunctions.
They assert no existence of exceptional adjoints on an ambient derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w vX vY vC vB
open CategoryTheory CategoryTheory.Endofunctor Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.VerdierPairing

/-- The rational or common-stage category, with precisely the coefficient categories of the
recorded dependencies. `none` means algebraically closed coefficients.
Source: prop-weil-operations, supplied domains
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
abbrev CategoryAt (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (T : Scheme.{u})
    (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l)) :=
  ConstructibleExceptionalCoefficients.C l Ω T
    (match E with | some E' => .rational E' | none => .closed)

/-- The actual geometric-Frobenius pullback in either coefficient category.
Source: prop-weil-operations, Weil-pair convention
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
def frobenius (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l)) :
    CategoryAt l Ω (D.geometricFiber T₀).left E ⥤
      CategoryAt l Ω (D.geometricFiber T₀).left E :=
  match E with
  | some E' => sfWeilFrobeniusPullback D l hl T₀ E'.carrier
  | none => sfCommonStageWeilFrobeniusPullback D l hl T₀ Ω

section Calculus
variable {X : Type v} {Y : Type w} [Category.{vX} X] [Category.{vY} Y]
  (ΦX : X ⥤ X) (ΦY : Y ⥤ Y)

/-- The supplied tensor and partial Hom, restricted to their closed domain, with their
canonical Frobenius comparisons. No tensor--Hom adjunction on X is presumed globally.
Source: prop-weil-operations, supplied canonical operations
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
structure TensorHomData {C : Type v} [Category.{vC} C] (Φ : C ⥤ C) where
  tensor : C ⥤ C ⥤ C
  hom : Cᵒᵖ ⥤ C ⥤ C
  tensorComparison : Functor.uncurry.obj tensor ⋙ Φ ≅
    Φ.prod Φ ⋙ Functor.uncurry.obj tensor
  homComparison : Functor.uncurry.obj hom ⋙ Φ ≅
    Φ.op.prod Φ ⋙ Functor.uncurry.obj hom

/-- A supplied adjunction and its canonical Weil lifts, with the prescribed underlying
units and counits. It is only asserted on the supplied domains.
Source: prop-weil-operations, lifted adjunctions
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
structure LiftedAdjunction (L : X ⥤ Y) (R : Y ⥤ X) where
  adj : L ⊣ R
  leftComparison : L ⋙ ΦY ≅ ΦX ⋙ L
  rightComparison : R ⋙ ΦX ≅ ΦY ⋙ R
  weilAdj : IsoAlgebra.mapOfNatIso leftComparison ⊣
    IsoAlgebra.mapOfNatIso rightComparison
  unit_eq : ∀ K : IsoAlgebra ΦX, (weilAdj.unit.app K).hom.f = adj.unit.app K.carrier
  counit_eq : ∀ K : IsoAlgebra ΦY,
    (weilAdj.counit.app K).hom.f = adj.counit.app K.carrier

end Calculus

/-- A full, Frobenius-stable domain in the recorded rational/common-stage category.
Source: prop-weil-operations, supplied-domain proviso
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
structure Domain (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
    (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l)) where
  objects : ObjectProperty (CategoryAt l Ω (D.geometricFiber T₀).left E)
  stable : ∀ K : objects.FullSubcategory,
    objects ((frobenius D l hl Ω T₀ E).obj K.obj)

namespace Domain
variable {D : FiniteFieldDatum.{u}} {l : ℕ} [Fact l.Prime] {hl : l ≠ D.p}
  {Ω : Type u} [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {T₀ : Over (Spec (.of D.k₀))} [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
  {E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l)}

/-- The supplied full subcategory, with the original underlying Hom sets.
Source: prop-weil-operations, supplied-domain proviso
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
abbrev C (S : Domain D l hl Ω T₀ E) := S.objects.FullSubcategory

/-- The inherited category structure on the supplied full domain.
Source: prop-weil-operations, supplied-domain proviso
(blueprint: lem-pod-verdier-pairing-three-transposes). -/
instance category (S : Domain D l hl Ω T₀ E) : Category.{u + 2} S.C := inferInstance

end Domain

section Realization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom]
  (E : Option (ConstructibleExceptionalCoefficients.FieldStage.{u} l))

end Realization

end WeilConjectures.VerdierPairing
