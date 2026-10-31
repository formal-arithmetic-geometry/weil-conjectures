/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralExceptionalMappingSystem
import WeilConjectures.AlgebraicGeometry.ExceptionalFiniteIntrinsicBounds
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.AlgebraicGeometry.FiniteCtfTriangulated
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated

/-! # Constructibility of the exceptional system limit

Source: the accepted integral exceptional mapping-adjunction interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralExceptionalMapping
open FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

variable {l E D hl}
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {c : Compactification f}
  {SX : CoefficientDerivedSystemCalculus l E X}
  {SZ : CoefficientDerivedSystemCalculus l E c.Z}
  {SY : CoefficientDerivedSystemCalculus l E Y}
  (r : Realization l E D hl f c SX SZ SY)


private def finiteExceptionalComparison (n : ℕ) :
    ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c ≅
      sfFiniteOperationsIntrinsicRight l
        ({ carrier := E } : ConstructibleExceptionalCoefficients.FieldStage.{u} l)
        ⟨n + 1, Nat.succ_pos n⟩ c := by
  let : (AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u+1} (ULift.{u+1, u}
        (Padic.coefficientExtensionRing l E (n + 1)))) c).IsLeftAdjoint :=
    AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c
  let e : ProEtale.sfFiniteExceptionalFixed
      (Padic.coefficientExtensionRing l E (n + 1)) c ≅
      ProEtale.sfFiniteExceptionalAt
        (ULift.{u+1, u} (Padic.coefficientExtensionRing l E (n + 1))) c :=
    letI := c.hasCompactification
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _
        ((AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunctionOfCompactification
            (ULift.{u+1, u} (Padic.coefficientExtensionRing l E (n + 1))) c).rightAdjointUniq
          (Adjunction.ofIsLeftAdjoint
            (AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u+1} (ULift.{u+1, u}
                (Padic.coefficientExtensionRing l E (n + 1)))) c)))) _
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft
      (sfIntrinsicDerivedEquivalence Y
        (Padic.coefficientExtensionRing l E (n + 1))).inverse e)
    (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor

private theorem interval_of_iso (W : Scheme.{u}) (n : ℕ) (a b : ℤ)
    {P Q : proEtaleDerivedCategory W (Padic.coefficientExtensionRing l E (n + 1))}
    (e : P ≅ Q) (hQ : constructibleInterval l E (n + 1) (Nat.succ_pos n) W a b Q) :
    constructibleInterval l E (n + 1) (Nat.succ_pos n) W a b P := by
  have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W) :=
    (proEtale_bounded_constructible_isTriangulated W
      (Padic.coefficientExtensionRing l E (n + 1))).1
  refine ⟨ObjectProperty.prop_of_iso _ e.symm hQ.1, ?_⟩
  intro i hi
  apply hQ.2
  intro hz
  exact hi (((DerivedCategory.homologyFunctor
    (scalarReductionTarget.{u, u} l E W n) i).mapIso e).isZero_iff.mpr hz)

/-- The exceptional system limit of an integral constructible input is constructible.
Source: prop-coef-integral-exceptional-adjoint, proof paragraph 1, and the accepted
specified-adjunction interface
(blueprint: lem-coef-integral-exceptional-limit-constructible).

Proof: apply the existing uniform intrinsic exceptional bounds once to f and c.
The resulting two integer shifts are independent of E and the positive level.
Use the common interval of the input reductions, whose finite-Tor membership is
supplied by reduction_domain and reductionEvaluation. Uniqueness of the etale
right adjoint compares the fixed finite exceptional functor with the one used
by the uniform bounds, in the same intrinsic coordinates. The output system
is normalized, so actual reconstruction makes its limit complete and its counit
invertible. Compose inverse reductionEvaluation, the evaluated actual counit,
exceptionalEvaluation, finite exceptional image of input reductionEvaluation,
and the right-adjoint comparison. Transfer constructibility and support through
these actual isomorphisms. Enlarge the output interval to its min/max endpoints
to obtain ordered bounds, including zero objects and empty schemes. There is
no common bound imposed on all objects of the normalized system category. -/
theorem exceptional_limit_constructible
    (L : sfIntegralConstructibleCategory l E Y) :
    sfIntegralConstructible l E X ((J r).obj L) := by
  classical
  obtain ⟨cm, cp, hb⟩ := sfFiniteOperations_intrinsicExceptionalBounds D l hl f c
  let E' : ConstructibleExceptionalCoefficients.FieldStage.{u} l := { carrier := E }
  obtain ⟨_, a, b, hab, hred⟩ := L.property
  have he (n : ℕ) :
      (scalarReductionDerivedExtension l E X n).obj ((J r).obj L) ≅
        (sfFiniteOperationsIntrinsicRight l E' ⟨n + 1, Nat.succ_pos n⟩ c).obj
          ((scalarReductionDerivedExtension l E Y n).obj L.obj) :=
    ((SX.reductionEvaluation n).app ((J r).obj L)).symm ≪≫
      (coefficientSequenceDerivedEvaluation l E X n).mapIso
        ((exceptionalIso r).app L) ≪≫
      (FiniteExceptional.domain l E X n).ι.mapIso
        ((r.exceptionalEvaluation n).app ((R l E D hl Y SY).obj L)) ≪≫
      (ProEtale.sfFiniteExceptional (Padic.coefficientExtensionRing l E (n + 1)) c).mapIso
        ((SY.reductionEvaluation n).app L.obj) ≪≫
      (finiteExceptionalComparison (l := l) (E := E) (c := c) n).app _
  have hc : IsSfDerivedComplete l E X ((J r).obj L) := by
    obtain ⟨D', hl', h⟩ :=
      ((purNormalizedReconstructionOfScheme l E X SX).1 _
        (r.G.obj ((R l E D hl Y SY).obj L)).property.1).1
    exact (sfDerivedComplete_iff_legacy l E X D' hl' _).mpr h
  have intervals (n : ℕ) :
      constructibleInterval l E (n + 1) (Nat.succ_pos n) X (a + cm) (b + cp)
        ((scalarReductionDerivedExtension l E X n).obj ((J r).obj L)) := by
    have hN : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) Y
        ((scalarReductionDerivedExtension l E Y n).obj L.obj) := by
      have ht := (reduction_domain l E D hl Y SY L).2 n
      have : (FiniteExceptional.domain l E Y n).IsClosedUnderIsomorphisms :=
        (finite_ctf_isTriangulated l E (n + 1) (Nat.succ_pos n) Y).1
      exact ObjectProperty.prop_of_iso _ ((SY.reductionEvaluation n).app L.obj) ht
    exact interval_of_iso (l := l) (E := E) X n _ _ (he n)
      ((hb E' ⟨n + 1, Nat.succ_pos n⟩).2.1 ⟨_, hN⟩ a b (hred n))
  refine ⟨hc, min (a + cm) (b + cp), max (a + cm) (b + cp), min_le_max, ?_⟩
  intro n
  refine ⟨(intervals n).1, ?_⟩
  intro i hi
  exact ⟨(min_le_left _ _).trans ((intervals n).2 hi).1,
    ((intervals n).2 hi).2.trans (le_max_right _ _)⟩

end WeilConjectures.IntegralExceptionalMapping
