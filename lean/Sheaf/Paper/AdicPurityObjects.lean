/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.AdicPurityTwistReduction
public import Sheaf.Paper.ExceptionalFiniteSupportRealization
public import Sheaf.Paper.IntegralOperationsPreserveConstructible
public import Sheaf.Paper.NormalizedDVREffectivity
/-! # Adic reconstruction of the specified finite smooth-purity comparisons
Source: blueprint thm-pur-adic-reconstruction, current main-20261015 snapshot.
The source is integral pullback followed by the actual coefficient twist and shift.
The target is the total inverse limit of the actual exceptional coefficient system.
All finite coefficients are those of PurityFiniteSetting.{u}, without a universe lift
of the geometric datum or a divisibility restriction on the coefficient exponent.
(blueprint: def-pur-adic-purity-objects).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures

section Pullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical finite reduction of integral pullback. This is the actual coherent
reduction/limit counit, transported by the specified Roos model and evaluation maps.
Source: blueprint thm-pur-adic-reconstruction, source normalization
(blueprint: def-pur-adic-purity-objects). -/
@[no_expose] def purAdicPullbackReduction
    (K : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj ((integralDerivedPullback l E f).obj K) ⟶
      (finiteDerivedPullback l E n f).obj
        ((scalarReductionDerivedExtension l E Y n).obj K) :=
  (scalarReductionDerivedExtension l E X n).map
      ((pullbackTensorIntegralPullbackModel l E f).hom.app K) ≫
    ((pullbackTensorCalculus l E X).reductionEvaluation n).inv.app _ ≫
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorCalculus l E X).adjunction.counit.app
        ((pullbackTensorSequenceDerived l E f).obj
          ((pullbackTensorCalculus l E Y).reduction.obj K))) ≫
    (pullbackTensorDerivedEvaluation l E f n).hom.app _ ≫
    (finiteDerivedPullback l E n f).map
      (((pullbackTensorCalculus l E Y).reductionEvaluation n).hom.app K)

/-- Exact finite pullback in the fixed-scalar presentation, with the canonical
localization composition comparisons retained.
Source: blueprint finite pullback normalization (blueprint: def-pur-adic-purity-objects). -/
@[no_expose] def purAdicFinitePullbackPresentation (n : ℕ) :
    finiteDerivedPullback l E n f ≅
      (Scheme.sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).inverse
        ⋙
        ProEtale.sfFixedDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f ⋙
          (Scheme.sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n +
            1))).functor :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso _ _)
end Pullback

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]

/-- The finite setting at every positive exponent, literally in the universe used by
isIso_smoothPurityMap. The natural number n denotes exponent n+1.
Source: blueprint finite coefficient conventions (blueprint: def-pur-adic-purity-objects). -/
abbrev purAdicFiniteSetting (n : ℕ) : PurityFiniteSetting.{u} where
  field := D
  coefficients := C
  extension := E
  level := n + 1
  level_pos := Nat.succ_le_succ (Nat.zero_le n)

/-- The coefficient prime is a unit on global sections of every k-scheme.
Source: blueprint purity conventions (blueprint: def-pur-adic-purity-objects).
Proof: l is nonzero in characteristic p because the two primes differ. It is a unit
in the field k. The structure map on global sections preserves units, including on
the empty scheme. -/
theorem purAdicCoefficientUnit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    IsUnit (C.l : Γ(W, ⊤)) := by
  have hchar0 : ringChar D.k₀ = D.p := by
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    exact ringChar.eq D.k₀ D.p
  have hchar : ringChar D.k = D.p :=
    (Algebra.ringChar_eq D.k₀ D.k).symm.trans hchar0
  have hl : (C.l : D.k) ≠ 0 := by
    intro hz
    exact C.different
      ((CharP.ringChar_of_prime_eq_zero (Fact.out : C.l.Prime) hz).symm.trans hchar)
  have hspec : IsUnit (C.l : Γ(Spec (.of D.k), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hl).map (Scheme.ΓSpecIso (.of D.k)).inv.hom
  simpa only [map_natCast] using hspec.map (W ↘ Spec (.of D.k)).appTop.hom

/-- The same coefficient prime is a unit in every residue field.
Source: blueprint purity conventions (blueprint: def-pur-adic-purity-objects).
Proof: map its unit in k first to the stalk at x, and then to the residue field.
The structure map and residue quotient are unital ring maps and preserve units. -/
theorem purAdicResidueUnit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (x : W) :
    IsUnit (C.l : W.residueField x) := by
  simpa only [map_natCast] using
    (purAdicCoefficientUnit D C W).map (W.Γevaluation x).hom

/-- The inverse of the coefficient prime, uniquely determined in each residue field.
Source: blueprint purity conventions (blueprint: def-pur-adic-purity-objects). -/
instance purAdicResidueInvertible (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (x : W) :
    Invertible (C.l : W.residueField x) := (purAdicResidueUnit D C W x).invertible

/-- Each actual derived finite reduction has bounded constructible cohomology and
finite Tor amplitude, using the two uniform intervals in the integral hypothesis.
Source: blueprint thm-pur-adic-reconstruction, K_n clause
(blueprint: def-pur-adic-purity-objects).
Proof: the integral constructibility predicate gives constructibility of every
positive reduction with a common cohomological interval. The second component of
finiteTorConstructibleIntegral supplies a single Tor interval [a,b] valid for all n.
At the chosen n, retain that interval as the finite Tor witness. No hypothesis on
an arbitrary source or target object is introduced. -/
theorem purAdicReductionFiniteTor (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource C.l E W))
    (hK : finiteTorConstructibleIntegral C.l E W K) (n : ℕ) :
    finiteTorConstructible C.l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) W
      ((scalarReductionDerivedExtension C.l E W n).obj K) := by
  rcases hK with ⟨⟨_, a, b, hab, hc⟩, c, d, hcd, ht⟩
  exact ⟨(hc n).1, c, d, ht n⟩

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The actual integral source Lf* K(d)[2d], using the recorded flat completed
coefficient line. No auxiliary source object is quantified.
Source: blueprint thm-pur-adic-reconstruction, displayed source
(blueprint: def-pur-adic-purity-objects). -/
def purAdicSource (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  ((integralComplexTwist D C.l C.different E X (d : ℤ)).obj
    ((integralDerivedPullback C.l E f).obj K))⟦2 * (d : ℤ)⟧

/-- The actual integral target Rlim nu_X* G_f Rnu_Y,* R_Y K, using the ordinary
etale system right adjoint and all actual quotient transitions.
Source: blueprint thm-pur-adic-reconstruction, displayed target
(blueprint: def-pur-adic-purity-objects). -/
def purAdicTarget (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  (integralExceptionalInverseImage C.l E D C.different f).obj K

/-- The specified finite smooth-purity arrow at exponent n+1, applied to the actual
finite reduction K_n. The source and target are the endpoints of that very arrow.
Source: blueprint thm-pur-adic-reconstruction, gamma_(f,K_n)
(blueprint: def-pur-adic-purity-objects). -/
def purAdicFiniteArrow
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ) :=
  Arrow.mk ((purAdicFiniteSetting D C E n).smoothPurityMap f d
    ((scalarReductionDerivedExtension C.l E Y n).obj K)
    (purAdicReductionFiniteTor D C E Y K hK n))

end WeilConjectures
