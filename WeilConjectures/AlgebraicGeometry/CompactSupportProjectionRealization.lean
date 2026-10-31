/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarLimitFoundations
import WeilConjectures.AlgebraicGeometry.CompactSupportScalarLimitReduction
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionRealizationLift
import all WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
import all WeilConjectures.AlgebraicGeometry.IntegralReductionJointFaithfulness
import WeilConjectures.AlgebraicGeometry.IntegralReductionShiftedHomFiniteQcqs
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Milnor

/-! # Constructible compact-support realization

The normalized lift is invertible and unique on the specified constructible domain.
Source: Stacks Tags 0941 and 0A07; the constructible Milnor injection.
(blueprint: lem-pur-compact-support-projection-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurScalarProjection
open PurCompactSupport

attribute [local irreducible] HasDerivedCategory.standard
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  completedCoefficientMap PurCompactSupport.comparison

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

include hl in
private theorem constructible_reduction_ext
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))]
    [QuasiCompact (W ↘ Spec (.of D.k))]
    {A B : DerivedCategory (scalarReductionSource l E W)}
    (hA : sfIntegralConstructible l E W A) (hB : sfIntegralConstructible l E W B)
    (a b : A ⟶ B)
    (hab : ∀ n : ℕ, (scalarReductionDerivedExtension l E W n).map a =
      (scalarReductionDerivedExtension l E W n).map b) : a = b := by
  obtain ⟨hp, δ, hδ⟩ := hB.1
  let := hp
  have hc : IsHomotopyLimit (sfIntegralReductionCone l E W B) := by
    apply reduction_roos_isHomotopyLimit (δ := δ)
    change IsDerivedLimitTriangle
      (K := fun n ↦ (sfDerivedReductionRestricted l E W n).obj B)
      (fun n ↦ (sfIntegralReductionTower l E W B).map (homOfLE n.le_succ).op)
      B (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E W n).app B)) δ
    simpa only [sfIntegralReductionTower,
      Functor.ofOpSequence_map_homOfLE_succ] using hδ
  let W' : SixFunctorSpace D :=
    ⟨Over.mk (W ↘ Spec (.of D.k)),
      (by change LocallyOfFiniteType (W ↘ Spec (.of D.k)); infer_instance),
      (by change QuasiCompact (W ↘ Spec (.of D.k)); infer_instance)⟩
  have (n : ℕ) : Finite
      (A⟦(1 : ℤ)⟧ ⟶ (sfIntegralReductionTower l E W B).obj (Opposite.op n)) :=
    integralReduction_shiftedHom_finite_qcqs D l hl E W' ⟨A, hA⟩ ⟨B, hB⟩ n
  apply (hc.bijective_milnorMap A).injective
  apply Subtype.ext
  funext n
  change a ≫ (sfDerivedReductionUnit l E W n).app B =
    b ≫ (sfDerivedReductionUnit l E W n).app B
  have ha := (sfDerivedReductionUnit l E W n).naturality a
  have hb := (sfDerivedReductionUnit l E W n).naturality b
  dsimp only [Functor.id_map, Functor.comp_map] at ha hb
  rw [ha, hb, hab n]

include hl in
omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
private theorem image_constructible
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : sfIntegralConstructible l E X M) :
    sfIntegralConstructible l E Y ((image (completed l E) c).obj M) := by
  let τ := sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) c
  exact ObjectProperty.prop_of_iso (sfIntegralConstructible l E Y)
    (τ.app ⟨M, hM⟩).symm
    ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) c E).obj
      ⟨M, hM⟩).property

include D hl in
/-- Canonical direct-image/total-limit and quasi-compact-open/total-limit
realization, retaining the actual finite scalar-adjunction counits.
Source: Stacks 0A07, 0GL1, 0941;
(blueprint: lem-pur-compact-support-projection-realization), Steps 5--6.
Proof: the normalized strict-system lift supplies a morphism with the required
finite counit equations. The qcqs finite comparison and invertible scalar-support
counits make each reduction of that morphism invertible. The qcqs recorded
realization makes its source constructible; the scalar-limit theorem makes its
target complete. Complete reduction detection makes the target constructible,
and constructible reduction detection makes the morphism invertible. For
uniqueness use the derived Hom inverse-limit sequence on these constructible
objects. Finite shifted Hom groups make its lim-one term vanish. Cancellation
of the invertible finite counits gives equality of the reductions, and the
Milnor injection then gives equality of integral maps. This proves uniqueness
on this domain without positing faithfulness for arbitrary derived reductions. -/
theorem realization_existsUnique
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    ∃! ρ : (image (completed l E) c).obj M ≅
        (PurStrictScalar.scalarSupport l E c S).obj M,
      ∀ n : ℕ,
        (pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) Y)).map
            ρ.hom ≫ PurStrictScalar.scalarSupportCounit l E c S n M =
          (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app M := by
  obtain ⟨ρ, hρ⟩ := compactSupportProjectionRealization_lift l E D hl f c S M
  let A := (image (completed l E) c).obj M
  let B := (PurStrictScalar.scalarSupport l E c S).obj M
  have hA : sfIntegralConstructible l E Y A :=
    image_constructible l E D hl f c M _hM.1
  have hram : Ramification l E E (AlgHom.id ℚ_[l] E) 1 := by
    have hi : integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E) =
        RingHom.id _ := by
      ext x
      rfl
    change Ideal.map _ _ = _
    rw [hi, Ideal.map_id]
  obtain ⟨γ, _, hγ⟩ := PurStrictScalar.compactSupportScalarLimitReduction
    l E E (AlgHom.id ℚ_[l] E) D hl f c S S 1 hram (by omega)
  have hBcomplete : IsSfDerivedComplete l E Y B := (hγ ⟨M, _hM⟩).2.1
  have hfinite := sfQcqsCompactSupport_finiteComparison l E D.k
    (coefficientPrimeUnit l D hl) c ⟨M, _hM.1⟩
  have hred (n : ℕ) : IsIso ((scalarReductionDerivedExtension l E Y n).map ρ) := by
    let R := pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) Y)
    have := ((hγ ⟨M, _hM⟩).2.2.2.2.2.2.1 n).1
    have := hfinite.2 n
    have : IsIso (R.map ρ ≫ PurStrictScalar.scalarSupportCounit l E c S n M) := by
      rw [hρ n]
      infer_instance
    have : IsIso (R.map ρ) := IsIso.of_isIso_comp_right
      (R.map ρ) (PurStrictScalar.scalarSupportCounit l E c S n M)
    have he := (finiteReductionIso l E Y n).hom.naturality ρ
    have : IsIso ((finiteReductionIso l E Y n).hom.app A ≫
        (scalarReductionDerivedExtension l E Y n).map ρ) := by
      rw [← he]
      infer_instance
    exact IsIso.of_isIso_comp_left ((finiteReductionIso l E Y n).hom.app A) _
  let (n : ℕ) : IsIso ((scalarReductionDerivedExtension l E Y n).map ρ) := hred n
  have hB : sfIntegralConstructible l E Y B :=
    constructible_of_complete_reduction_isos l E Y hBcomplete hA
      (fun n ↦ (asIso ((scalarReductionDerivedExtension l E Y n).map ρ)).symm)
  have : IsIso ρ := constructible_isIso_of_reductions l E Y ρ hA hB hred
  refine ⟨asIso ρ, hρ, ?_⟩
  intro σ hσ
  apply Iso.ext
  apply constructible_reduction_ext l E D hl Y hA hB
  intro n
  have := ((hγ ⟨M, _hM⟩).2.2.2.2.2.2.1 n).1
  have heq : (pbcDerivedExtend
      (projection l E (n + 1) (Nat.le_add_left 1 n) Y)).map σ.hom =
      (pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) Y)).map ρ := by
    apply (cancel_mono (PurStrictScalar.scalarSupportCounit l E c S n M)).1
    exact (hσ n).trans (hρ n).symm
  have hs := (finiteReductionIso l E Y n).hom.naturality σ.hom
  have hr := (finiteReductionIso l E Y n).hom.naturality ρ
  apply (cancel_epi ((finiteReductionIso l E Y n).hom.app A)).1
  exact hs.symm.trans ((congrArg
    (fun q ↦ q ≫ (finiteReductionIso l E Y n).hom.app B) heq).trans hr)

/-- The support realization fixed by all its specified finite counits.
Source: Stacks 0A07, 0GL1, 0941;
(blueprint: lem-pur-compact-support-projection-realization), Steps 5--6. -/
def realization
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :=
  (realization_existsUnique l E D hl f c S M hM).exists.choose

end WeilConjectures.PurScalarProjection
