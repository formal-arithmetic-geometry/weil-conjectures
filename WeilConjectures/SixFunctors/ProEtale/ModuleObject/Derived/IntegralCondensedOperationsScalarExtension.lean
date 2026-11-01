/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions

import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedTensorNormalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.FiniteFreeScalarCoordinates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarSectionRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeTensor
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeHom
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower

/-! # Integral condensed scalar compatibility for ordinary derived operations

Source: latest blueprint, under `literature/blueprint/latest/blueprint/`:
* part-six-operations/sec-proetale-coefficients/sec-pe-localization-completion/
  sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md, final paragraph;
* part-six-operations/sec-six-functors/sec-n-change/sk-prop-scalar-six/
  det-prop-scalar-six-pullback.proof.md (1),(3);
* part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/
  sec-towers-and-integral-coefficients/sk-lem-sp-tower/
  lem-coef-integral-finite-extension.proof.md, finite-free Hom and scalar-associator paragraphs
(blueprint: lem-pur-integral-operations-scalar-extension).

All functors and comparison arrows below are the published ordinary internal-module
constructions. `scalarSixPull` is the termwise exact inverse image, identified with
`Lf^*` by `leftDerivedUpperStarIsoMapDerivedCategory`. No completion is applied.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 2000000 in
-- Elaborating all native coefficient, tensor and adjunction instances exceeds the default budget.
/-- The complete scalar compatibility assertion, including the prescribed arrows.
The fields are finite subfields of the fixed algebraic closure; the coefficient map
is the continuous integral inclusion, bundled as a commutative ring-object map.
`tensor` is the native derived relative tensor and `ihom` the native `derivedHom`.
The Hom equation fixes the evaluation transpose, and the last two clauses retain
inverse transport in its contravariant variable. The tensor tower and identity
clauses are the tensor equations for the balanced associator and multiplication unitor.

Source: latest blueprint, under `literature/blueprint/latest/blueprint/`:
* part-six-operations/sec-proetale-coefficients/sec-pe-localization-completion/
  sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md, final paragraph;
* part-six-operations/sec-six-functors/sec-n-change/sk-prop-scalar-six/
  det-prop-scalar-six-pullback.proof.md (1),(3);
* part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/
  sec-towers-and-integral-coefficients/sk-lem-sp-tower/
  lem-coef-integral-finite-extension.proof.md, finite-free Hom and scalar-associator paragraphs
(blueprint: lem-pur-integral-operations-scalar-extension). -/
def IntegralCondensedOperationsScalarCompatibility (ell : ℕ) [Fact ell.Prime] : Prop :=
  ∀ (E L : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ L)
    (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
      ⟨Profinite.padicIntegersRingObj ell L.1⟩)
    (_ha : a.hom.hom = finiteCoefficientIntegersPointMap ell h),
    (∀ (X Y : Scheme.{u}) [∀ x : X, Invertible (ell : X.residueField x)]
      [∀ y : Y, Invertible (ell : Y.residueField y)] (f : X ⟶ Y),
      IsIso (scalarSixPullHom a f)) ∧
    (∀ (W : Scheme.{u}) [∀ w : W, Invertible (ell : W.residueField w)],
      ∃ t : tensor (DerivedCategory
          (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) W))
          ⋙ scalarSixChange a W ≅
        (scalarSixChange a W).prod (scalarSixChange a W) ⋙
          tensor (DerivedCategory
            (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell L.1) W)),
        ∀ M N : DerivedCategory
          (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) W),
          t.hom.app (M, N) = (scalarSixTensorIso a W M N).hom) ∧
    (∀ (W : Scheme.{u}) [∀ w : W, Invertible (ell : W.residueField w)]
      (M N : DerivedCategory
        (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) W)),
      IsIso ((@Functor.LaxMonoidal.ihomComparison _ _ _ _ _ _ _ _
        (scalarSixChange a W) (scalarSixChangeMonoidal a W).toLaxMonoidal M).natTrans.app N) ∧
      (@Functor.LaxMonoidal.ihomComparison _ _ _ _ _ _ _ _
        (scalarSixChange a W) (scalarSixChangeMonoidal a W).toLaxMonoidal M).natTrans.app N =
        MonoidalClosed.curry
          ((scalarSixTensorIso a W M ((ihom M).obj N)).inv ≫
          (scalarSixChange a W).map ((ihom.ev M).app N))) ∧
    (∀ (P : PadicAlgCl.FiniteIntermediateField ell) (hL : L ≤ P)
      (b : (⟨Profinite.padicIntegersRingObj ell L.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicIntegersRingObj ell P.1⟩)
      (_hb : b.hom.hom = finiteCoefficientIntegersPointMap ell hL)
      (W : Scheme.{u}) [∀ w : W, Invertible (ell : W.residueField w)],
      (∀ M N : DerivedCategory
        (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) W),
        (scalarSixChange b W).map ((scalarSixTensorIso a W M N).hom) ≫
            (scalarSixTensorIso b W ((scalarSixChange a W).obj M)
              ((scalarSixChange a W).obj N)).hom ≫
            ((scalarSixTower a b W).hom.app M ⊗ₘ (scalarSixTower a b W).hom.app N) =
          (scalarSixTower a b W).hom.app (M ⊗ N) ≫
            (scalarSixTensorIso (a ≫ b) W M N).hom) ∧
      (∀ M N : DerivedCategory
        (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) W),
        (scalarSixTower a b W).hom.app ((ihom M).obj N) ≫
            (@Functor.LaxMonoidal.ihomComparison _ _ _ _ _ _ _ _
              (scalarSixChange (a ≫ b) W)
              (scalarSixChangeMonoidal (a ≫ b) W).toLaxMonoidal M).natTrans.app N =
          (scalarSixChange b W).map
            ((@Functor.LaxMonoidal.ihomComparison _ _ _ _ _ _ _ _
              (scalarSixChange a W) (scalarSixChangeMonoidal a W).toLaxMonoidal M).natTrans.app N) ≫
            (@Functor.LaxMonoidal.ihomComparison _ _ _ _ _ _ _ _
              (scalarSixChange b W) (scalarSixChangeMonoidal b W).toLaxMonoidal
              ((scalarSixChange a W).obj M)).natTrans.app ((scalarSixChange a W).obj N) ≫
            (ihom ((scalarSixChange b W).obj ((scalarSixChange a W).obj M))).map
              ((scalarSixTower a b W).hom.app N) ≫
            (MonoidalClosed.pre ((scalarSixTower a b W).inv.app M)).app
              ((scalarSixChange (a ≫ b) W).obj N)) ∧
      (∀ (Y : Scheme.{u}) [∀ y : Y, Invertible (ell : Y.residueField y)]
        (f : W ⟶ Y) (K : DerivedCategory
          (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) Y)),
        (scalarSixTower a b W).hom.app ((scalarSixPull _ f).obj K) ≫
            (scalarSixPullHom (a ≫ b) f).app K =
          (scalarSixChange b W).map ((scalarSixPullHom a f).app K) ≫
            (scalarSixPullHom b f).app ((scalarSixChange a Y).obj K) ≫
            (scalarSixPull _ f).map ((scalarSixTower a b Y).hom.app K))) ∧
    (∃ e : ∀ W : Scheme.{u},
      scalarSixChange (𝟙 (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u})) W ≅
        𝟭 (DerivedCategory
          (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) W)),
      (∀ W, e W =
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap (Λ := Profinite.padicIntegersRingObj ell E.1)
            (Λ' := Profinite.padicIntegersRingObj ell E.1) (𝟙 _) W)).leftAdjointUniq
          (Adjunction.id.ofNatIsoRight
            (Functor.mapDerivedCategoryNatIso
                (Mod.comapCongr
                  (coefficientMap_id (Λ := Profinite.padicIntegersRingObj ell E.1) W)) ≪≫
              Functor.mapDerivedCategoryNatIso
                (Mod.comapId (condensedRingObj (Profinite.padicIntegersRingObj ell E.1) W)) ≪≫
              Functor.mapDerivedCategoryIdIso _).symm)) ∧
      ∀ (W : Scheme.{u}) [∀ w : W, Invertible (ell : W.residueField w)],
        (∀ M N : DerivedCategory
          (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) W),
          (scalarSixTensorIso
              (𝟙 (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u})) W M N).hom ≫
              ((e W).hom.app M ⊗ₘ (e W).hom.app N) =
            (e W).hom.app (M ⊗ N)) ∧
        (∀ M N : DerivedCategory
          (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) W),
          (@Functor.LaxMonoidal.ihomComparison _ _ _ _ _ _ _ _
            (scalarSixChange
              (𝟙 (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u})) W)
            (scalarSixChangeMonoidal
              (𝟙 (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u})) W).toLaxMonoidal
            M).natTrans.app N ≫
              (ihom ((scalarSixChange
                (𝟙 (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u})) W).obj M)).map
                ((e W).hom.app N) ≫
              (MonoidalClosed.pre ((e W).inv.app M)).app N =
            (e W).hom.app ((ihom M).obj N)) ∧
        (∀ (Y : Scheme.{u}) [∀ y : Y, Invertible (ell : Y.residueField y)]
          (f : W ⟶ Y) (K : DerivedCategory
            (ModuleRingedComparison.internalModules (Profinite.padicIntegersRingObj ell E.1) Y)),
          (scalarSixPullHom
            (𝟙 (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u})) f).app K ≫
              (scalarSixPull _ f).map ((e Y).hom.app K) =
            (e W).hom.app ((scalarSixPull _ f).obj K)))

/-- Integral finite coefficient extension commutes with ordinary unbounded derived
pullback, relative tensor, and internal Hom, with evaluation and scalar coherence.

Source: latest blueprint, under `literature/blueprint/latest/blueprint/`:
* part-six-operations/sec-proetale-coefficients/sec-pe-localization-completion/
  sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md, final paragraph;
* part-six-operations/sec-six-functors/sec-n-change/sk-prop-scalar-six/
  det-prop-scalar-six-pullback.proof.md (1),(3);
* part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/
  sec-towers-and-integral-coefficients/sk-lem-sp-tower/
  lem-coef-integral-finite-extension.proof.md, finite-free Hom and scalar-associator paragraphs
(blueprint: lem-pur-integral-operations-scalar-extension).

Proof:
1. Use lem-sfb-internal-section-scalar-adjunction and
   lem-pd-section-derived-tensor-normalization to identify internal operations with
   section-ring operations, including their adjunctions, tensors and evaluation.
2. By det-prop-sfb-cartesian-coefficients-finite-free the extended coefficient ring
   is finite free. The scalar coordinates of lem-sfb-finite-free-scalar-coordinates
   give exact scalar extension. The K-flat tensorator is identified by
   lem-sfb-coefficient-scalar-section-realization.
3. Apply det-prop-scalar-six-pullback (1),(3) to obtain the canonical pullback
   isomorphism and its coefficient-composition square on all unbounded objects.
4. Apply lem-sfb-ringed-derived-monoidal-comparisons to the identity geometric
   morphism with this coefficient map. Its tensor comparison is the specified
   K-flat balancing map, natural in both arguments.
5. Apply lem-sf-ringed-finite-free-hom-base-change. After restriction of scalars
   and a finite free basis, both Hom objects identify with the same finite sum
   of RHom(M,N), and the evaluation transpose is the identity on each summand.
   Restriction is conservative, so the prescribed map is invertible, without
   perfectness, boundedness or completeness assumptions on either input.
6. The tensor-tower and identity equations of lem-sfb-scalar-hom-tensor-coherence
   and the transpose uniqueness in lem-pur-scalar-hom-comparison-tower give the
   Hom equations. The pullback tower is step 3; its identity equation follows
   from the ringed identity comparison. Thus all equalities concern the actual
   normalized arrows. Bounded constructible inputs are particular unbounded inputs. -/
theorem integralCondensedOperationsScalarExtension (ell : ℕ) [Fact ell.Prime] :
    IntegralCondensedOperationsScalarCompatibility.{u} ell := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
