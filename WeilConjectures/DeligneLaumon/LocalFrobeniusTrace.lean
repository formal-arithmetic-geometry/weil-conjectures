/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.CoefficientCohomologyModules
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.ZetaSeries
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod

import WeilConjectures.PointCount
public import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField

/-!
# Local Frobenius on the derived point fibre and its alternating trace

Source: Weil blueprint, sec-poincare-duality/sk-lem-finite,
Local Frobenius and local alternating trace; Deligne, Weil II, (1.1.7)--(1.1.10)
(blueprint: def-weil-local-frobenius-trace).

The rational composition comparison below is the localization of the specified integral
comparison. Object equalities only identify the unchanged objects of raw rationalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Identify the prescribed rational pullback object with its integral model.
Source: blueprint rational pullback convention (blueprint: def-weil-local-frobenius-trace). -/
def localPullbackObjectIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E f).obj K ≅
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj K.obj) :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K)

/-- The specified composition comparison, localized from the integral comparison.
Source: blueprint composition convention (blueprint: def-weil-local-frobenius-trace). -/
def localPullbackComposition {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E Z) :
    (rationalDerivedPullback l E (h ≫ k)).obj K ≅
      (rationalDerivedPullback l E h).obj ((rationalDerivedPullback l E k).obj K) :=
  localPullbackObjectIso l E (h ≫ k) K ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (((integralPullbackComposition l E).choose h k).app K.obj) ≪≫
    (localPullbackObjectIso l E h
      ((sfRationalConstructibleLocalization l E Y).obj
        ((constructibleIntegralPullback l E k).obj K.obj))).symm ≪≫
    (rationalDerivedPullback l E h).mapIso (localPullbackObjectIso l E k K).symm

/-- Positive powers, with exponent n+1; this avoids any choice of a pullback unit.
Source: blueprint theta iteration (blueprint: def-weil-local-frobenius-trace). -/
def localPositivePower {X : Scheme.{u}} (g : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => g
  | n + 1 => localPositivePower g n ≫ g

/-- Contravariant Spec sends the positive power to the corresponding field power.
Source: geometric-Frobenius construction (blueprint: def-weil-local-frobenius-trace). -/
private theorem localPointPower_eq (n : ℕ) :
    localPositivePower (frobeniusPointIso D).hom n =
      let := Fintype.ofFinite D.k₀
      Spec.map (CommRingCat.ofHom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ (n + 1)).toRingHom) := by
  let := Fintype.ofFinite D.k₀
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [localPositivePower, ih]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1

/-- Iterating the two Galois-map projections preserves the model projection and
iterates the coefficient projection.
Source: geometric-Frobenius construction (blueprint: def-weil-local-frobenius-trace). -/
private theorem localFrobeniusPower_projections (n : ℕ) :
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        localPositivePower (frobeniusPointIso D).hom n := by
  let := Fintype.ofFinite D.k₀
  have h := D.galoisMap_projections Y₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
  change (D.geometricFrobenius Y₀).hom ≫ _ = _ ∧
    (D.geometricFrobenius Y₀).hom ≫ _ =
      _ ≫ (frobeniusPointIso D).hom at h
  induction n with
  | zero => exact h
  | succ n ih =>
    constructor
    · rw [localPositivePower, Category.assoc, h.1]
      exact ih.1
    · rw [localPositivePower, Category.assoc, h.2, ← Category.assoc, ih.2,
        Category.assoc]
      rfl

/-- A model map fixed by the point power has the stated semilinear return lift.
Source: pullback uniqueness in the return construction
(blueprint: def-weil-local-frobenius-trace). -/
private theorem localLift_return (n : ℕ) (a : Spec (.of D.k) ⟶ Y₀.left)
    (c : a ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (ha : localPositivePower (frobeniusPointIso D).hom n ≫ a = a) :
    pullback.lift a (𝟙 _) c ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ pullback.lift a (𝟙 _) c := by
  apply pullback.hom_ext
  · rw [Category.assoc, (localFrobeniusPower_projections D Y₀ n).1,
      pullback.lift_fst, Category.assoc, pullback.lift_fst, ha]
  · rw [Category.assoc, (localFrobeniusPower_projections D Y₀ n).2,
      ← Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
      Category.id_comp, Category.comp_id]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
/-- Derived pullback of the underlying Weil complex at an arbitrary geometric point.
Source: blueprint K_xbar (blueprint: def-weil-local-frobenius-trace). -/
def localDerivedStalk (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    sfRationalConstructibleCategory l E (Spec (.of D.k)) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (rationalDerivedPullback l E x).obj K.carrier

/-- The bounded finite-dimensional rational point complex C_xbar.
Source: blueprint point-fibre clause (blueprint: def-weil-local-frobenius-trace). -/
def localPointComplex (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    (DerivedCategory.pointFiniteDimensional E).FullSubcategory :=
  (pointRationalFibre D l hl E).obj (localDerivedStalk l E D hl Y₀ K x)

/-- Point transport to the actual one-step rational pullback object.
Source: blueprint iota_N (blueprint: def-weil-local-frobenius-trace). -/
def localPointTransport (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl E).obj N ⟶
      (pointRationalFibre D l hl E).obj
        ((@rationalDerivedPullback l _ E _ _ _ _ _ (frobeniusPointIso D).hom
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N) :=
  frobeniusPointTransportRational D l hl E N ≫
    (pointRationalFibre D l hl E).map
      ((@localPullbackObjectIso l _ E _ _ _ _ _ (frobeniusPointIso D).hom
        (frobeniusPointPrimeInvertible D l hl)
        (frobeniusPointPrimeInvertible D l hl) N).inv)

/-- The finite-field inclusion and a point over k₀ have matching base maps.
Source: blueprint finite-field-point clause (blueprint: def-weil-local-frobenius-trace).
Proof: the composite of extensionEmbedding with the subfield inclusion is algebraMap.
Contravariant functoriality of Spec and the equation Over.w x give the equality. -/
theorem localExtensionPoint_compatible (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) :
    (Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left) ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  have hbase :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k n hn).choose_spec.2.2.2.2.2.2.choose_spec
  rw [Category.assoc, Over.w x, Category.id_comp]
  change Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding n hn)) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hbase

/-- The geometric point obtained from F_(q^n) ⊂ k by the universal fibre-product lift.
Source: blueprint xbar (blueprint: def-weil-local-frobenius-trace). -/
def localExtensionPoint (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left)
    (𝟙 _) (localExtensionPoint_compatible D Y₀ n hn x)

/-- The degree of a closed point uses its actual residue field with its structure map.
Source: blueprint r=[κ(y):k₀] (blueprint: def-weil-local-frobenius-trace). -/
def localClosedPointDegree (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) : ℕ :=
  letI := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  Module.finrank D.k₀ (Y₀.left.residueField y.val)

/-- A closed point of a finite-type model has finite positive residue degree.
Source: blueprint closed-point clause; lem-kun-closed-point-field(a)
(blueprint: def-weil-local-frobenius-trace).
Proof: closedPoint_iff_residueField_trdeg_zero_and_finite gives finiteness over k₀.
A field is nonzero, so its finite vector-space dimension is positive. -/
theorem localClosedPointDegree_pos
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) :
    1 ≤ localClosedPointDegree D Y₀ y := by
  let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  have := (closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y.val).2.1.mp y.prop
  exact Module.finrank_pos

/-- A k₀-embedding of κ(y) gives a model point compatible with the base field.
Source: blueprint chosen residue-field embedding (blueprint: def-weil-local-frobenius-trace).
Proof: the structural composite of fromSpecResidueField is Spec of the residue-field
algebra map. Compose with Spec ι and use the displayed k₀-compatibility equation. -/
theorem localClosedPoint_compatible
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    (Spec.map (CommRingCat.ofHom ι) ≫ Y₀.left.fromSpecResidueField y.val) ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  rw [Category.assoc, ← Y₀.hom.specMap_residueFieldAlgebraMap,
    Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hι]

/-- The geometric point over a closed point for the chosen k₀-embedding of its residue field.
Source: blueprint ybar (blueprint: def-weil-local-frobenius-trace). -/
def localClosedPoint (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom ι) ≫ Y₀.left.fromSpecResidueField y.val) (𝟙 _)
    (localClosedPoint_compatible D Y₀ y ι hι)

/-- Geometric Frobenius to the residue degree returns the chosen closed-point lift.
Source: blueprint closed-point return (blueprint: def-weil-local-frobenius-trace).
Proof: the residue field is finite over k₀ by lem-kun-closed-point-field(a), with
q^r elements. Its embedded image is the unique subfield of that size by
lem-weil-unique-subfield-of-closure, hence is fixed by gamma^r. Compare both
projections of the pullback exactly as for localExtensionPoint_return. Positivity
of the degree identifies the positive-power index r-1 with exponent r. -/
theorem localClosedPoint_return
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    localClosedPoint D Y₀ y ι hι ≫
        localPositivePower (D.geometricFrobenius Y₀).hom
          (localClosedPointDegree D Y₀ y - 1) =
      localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D Y₀ y - 1) ≫
        localClosedPoint D Y₀ y ι hι := by
  let := Fintype.ofFinite D.k₀
  let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  have := (closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y.val).2.1.mp y.prop
  have : Finite (Y₀.left.residueField y.val) := Module.finite_of_finite D.k₀
  have hc : Nat.card (Y₀.left.residueField y.val) =
      Fintype.card D.k₀ ^ localClosedPointDegree D Y₀ y := by
    simpa only [Nat.card_eq_fintype_card, localClosedPointDegree] using
      (Module.natCard_eq_pow_finrank (K := D.k₀) (V := Y₀.left.residueField y.val))
  apply localLift_return D Y₀ (localClosedPointDegree D Y₀ y - 1)
  rw [← Category.assoc]
  suffices h :
      localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D Y₀ y - 1) ≫
        Spec.map (CommRingCat.ofHom ι) = Spec.map (CommRingCat.ofHom ι) by rw [h]
  rw [localPointPower_eq, Nat.sub_add_cancel (localClosedPointDegree_pos D Y₀ y),
    ← Spec.map_comp]
  congr 1
  ext a
  exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq
    D.k₀ D.k (localClosedPointDegree D Y₀ y) hc ι a

set_option linter.unusedSectionVars false in
end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

end WeilConjectures
