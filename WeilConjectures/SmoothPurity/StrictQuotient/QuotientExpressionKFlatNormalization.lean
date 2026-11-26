/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.StrictQuotient.StrictQuotientExpressions
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionKFlatModels
import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionKFlatOperations

/-! # Simultaneous K-flat normalization of strict quotient expressions

Given finitely many K-flat complexes with flat terms over the completed integral coefficient
ring, we construct strict towers of K-flat models whose levels are their ordinary reductions,
and show that every expression generated from them by tensor products, pullbacks and the
degree-zero units is a normalized coefficient sequence with compatible derived adjoints.

## Implementation details

All transitions belong to strict sequence complexes before localization. The ordinary and
derived adjoints are adjoints of those actual maps. No assertion that inverse image commutes
with the completed coefficient limit is made.

## References

* Stacks Project, Tags 0G7E, 07A2, 07A4 and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
namespace WeilConjectures.StrictQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Simultaneous strict quotient normalization: for a finite family `P` of K-flat complexes
with flat terms, there are strict towers `N i` with isomorphisms `κ` identifying their levels
with the ordinary reductions of `P i`, compatibly with all quotient transitions, such that every
expression generated from the `N i` by tensor products, pullbacks along `h` and `f`, and the
degree-zero units is levelwise K-flat, is a normalized coefficient sequence, and has derived
adjoints computed by the ordinary adjoints of its transitions. -/
theorem quotientExpressionKFlatNormalization
    {Z X Y : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (_hlZ : ∀ x : Z, IsUnit (l : Z.residueField x))
    (_hlX : ∀ x : X, IsUnit (l : X.residueField x))
    (_hlY : ∀ x : Y, IsUnit (l : Y.residueField x))
    (r : ℕ) (P : Fin r → CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : ∀ i : Fin r, CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E Y) (P i))
    (_hflat : ∀ (i : Fin r) (k : ℤ), SheafOfModules.IsFlatOnSite
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted l E Y) ((P i).X k)) :
    ∃ (N : Fin r → Complex l E Y)
      (κ : ∀ (i : Fin r) (n : ℕ), level l E (N i) n ≅
        ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj (P i)),
      (∀ (i : Fin r) {m n : ℕ} (hmn : n ≤ m),
        transition l E (N i) hmn ≫
            ((normalizedDVRModuleRes l E Y hmn).mapHomologicalComplex (.up ℤ)).map
              (κ i n).hom =
          (κ i m).hom ≫
            (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E Y hmn)
              (.up ℤ)).app (P i)) ∧
      (∀ (i : Fin r) (n : ℕ),
        ∃ e : (coefficientFiniteDerivedExtension l E Y n).obj
            (DerivedCategory.Q.obj (P i)) ≅ DerivedCategory.Q.obj (level l E (N i) n),
          e.hom = (coefficientFiniteReductionModel l E Y (P i) (hP i) n).hom ≫
            DerivedCategory.Q.map (κ i n).inv) ∧
      (∀ (W : Scheme.{t}) (K : Complex l E W), Generated l E h f N W K →
        (∀ n : ℕ, Good l E K n) ∧
        IsNormalizedCoefficientSequence l E W (DerivedCategory.Q.obj K) ∧
        (∀ (S : CoefficientDerivedSystemTensors l E W)
          (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m),
          ∃ hK : CochainComplex.IsKFlatIndependentCoefficients
            (R := integralCoefficientCommRingSheaf l E W m) (level l E K m),
            AdjointModel l E K S D hmn hK)) ∧
      (∀ (W : Scheme.{t}) (U V : Complex l E W),
        Generated l E h f N W U → Generated l E h f N W V →
        TensorTransitions l E U V ∧
        (∀ (n : ℕ) (S : CoefficientDerivedSystemTensors l E W),
          ∃ (hU : Good l E U n) (hV : Good l E V n)
            (e : DerivedCategory.Q.obj (level l E (total l E U V) n) ≅
              (S.finiteClosed n).tensor.obj
                (DerivedCategory.Q.obj (level l E U n), DerivedCategory.Q.obj (level l E V n))),
            e.hom = DerivedCategory.Q.map (coefficientEvaluationTensorIso l E W n U V).hom ≫
              ((S.finiteTensorModel n).iso (Scheme.ProEt.topology W)
                (integralCoefficientCommRingSheaf l E W n) (S.finiteClosed n)
                (level l E U n) (level l E V n) hU.1 hV.1).hom) ∧
        (∀ (S : CoefficientDerivedSystemTensors l E W)
          (D : CoefficientFiniteQuotientCalculus l E W S) {m n : ℕ} (hmn : n ≤ m)
          (hUm : Good l E U m) (hVm : Good l E V m)
          (hUn : Good l E U n) (hVn : Good l E V n),
          TensorAdjointEquation l E U V S D hmn hUm hVm hUn hVn)) ∧
      (∀ {V W : Scheme.{t}} (g : V ⟶ W), AllowedArrow h f g →
        ∀ K : Complex l E W, Generated l E h f N W K →
          PullbackTransitions l E g K ∧
          (∀ n : ℕ, PullbackModel l E g K n ∧ PullbackComputes l E g K n) ∧
          (∀ (SW : CoefficientDerivedSystemTensors l E W)
            (DW : CoefficientFiniteQuotientCalculus l E W SW)
            (SV : CoefficientDerivedSystemTensors l E V)
            (DV : CoefficientFiniteQuotientCalculus l E V SV) {m n : ℕ} (hmn : n ≤ m),
            PullbackAdjointEquation l E g K SW DW SV DV hmn)) := by
  obtain ⟨N, κ, hκ, he, hgood⟩ :=
    quotientExpressionKFlatModels l E h f _hlZ _hlX _hlY r P hP _hflat
  obtain ⟨hnorm, htensor, hpull⟩ :=
    quotientExpressionKFlatOperations l E h f r N P κ hκ
      (fun W K hK ↦ hgood W K hK)
  refine ⟨N, κ, hκ, he, ?_, htensor, hpull⟩
  intro W K hK
  exact ⟨hgood W K hK, (hnorm W K hK).1, (hnorm W K hK).2⟩

end WeilConjectures.StrictQuotient
