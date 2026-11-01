/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusCohomologyRealization
import WeilConjectures.SixFunctors.FrobeniusCohomologyRealization
import WeilConjectures.SixFunctors.CohomologyRealization.FrobeniusCohomologyComparisonFactors

/-!
# Invertibility of Frobenius cohomology transport

Source: Deligne, *La conjecture de Weil II*, (1.1.7), (1.1.10)--(1.1.14),
and the Weil blueprint (blueprint: lem-weil-frobenius-cohomology-transport-iso).

The statement records invertibility of the canonical point transports, the two
Frobenius exchange components, and their induced maps in every cohomological
degree, for each of the four coefficient realizations.
The realization helpers expose the canonical functors on arbitrary common-stage
morphisms used by the naturality statement, retaining the recorded transport values.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

open FrobeniusExchange

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard

section QuotientDescent
universe w a b c d

end QuotientDescent

section CommonStageFunctors
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (stageSystem)
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

set_option linter.defProp false in
set_option linter.defProp false in
end CommonStageFunctors

section Exchanges

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The ordinary finite exchange at the actual structure map to Spec k, in the
intrinsic inverse-image coordinates used by the cohomology transport.
Source: Deligne, Weil II (1.1.14); the exchange factor in the transport definition
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyFiniteDirectExchange (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  finiteExchange (Padic.coefficientExtensionRing l E (n + 1))
    (D.geometricFiber Y₀).hom (D.geometricFiber Y₀).hom
    (galois D Y₀) (frobeniusPointIso D).hom
    (D.frobenius_square_cartesian Y₀ (sfWeilCohomologyPoint D)
      (frobeniusCohomologyModelMap D Y₀)).2.2.2.2.2.2.2.w

/-- The compact finite exchange to Spec k, retaining exactly the compactification
and the middle Frobenius used by the compact cohomology transport.
Source: Deligne, Weil II (1.1.14); the compact exchange in the transport definition
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyFiniteCompactExchange (c₀ : Compactification Y₀.hom) (n : ℕ) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let F := sfIntrinsicCompactSupport (frobeniusCohomologyCompactification D Y₀ c₀)
    (Padic.coefficientExtensionRing l E (n + 1))
  let e := finiteCompact l E (n + 1) (Nat.succ_pos n)
    (frobeniusCohomologyCompactification D Y₀ c₀) (galois D Y₀)
    (galois D (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀))
    (frobeniusPointIso D).hom
    (D.frobenius_square_cartesian
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
      (sfWeilCohomologyPoint D)
      (zlCompactificationProper D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.2.2.w
    (D.frobenius_square_cartesian Y₀
      (zlCompactificationMiddle D (frobeniusCohomologyModelMap D Y₀) c₀)
      (zlCompactificationOpen D (frobeniusCohomologyModelMap D Y₀) c₀)).2.2.2.2.2.1
  Functor.whiskerLeft F (openSquareDerivedPullbackModel
      (Padic.coefficientExtensionRing l E (n + 1)) (frobeniusPointIso D).hom).inv ≫
    e ≫ Functor.whiskerRight (openSquareDerivedPullbackModel
      (Padic.coefficientExtensionRing l E (n + 1)) (galois D Y₀)).hom F

/-- The actual integral ordinary or compact exchange at a_Y, with target Spec k.
Only the inherited proof instances are installed; no exchange morphism is selected.
Source: Deligne, Weil II (1.1.14); the recorded support recipe
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyIntegralExchange (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelExchange l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The actual rational ordinary or compact exchange at a_Y, with target Spec k.
Only the inherited proof instances are installed; no exchange morphism is selected.
Source: Deligne, Weil II (1.1.14); the recorded support recipe
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalExchange (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelRationalExchange l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The common-stage exchange at a_Y, with the same actual Spec k as target.
Its components are the recorded rational exchanges at their own coefficient stage.
Source: Deligne, Weil II (1.1.14); the common-stage exchange construction
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyQbarExchange (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  commonStageExchange l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) Ω

end Exchanges

section Naturality

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

end Naturality

end WeilConjectures
