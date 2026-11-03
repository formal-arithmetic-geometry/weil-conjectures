/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTensorReduction.CondensedPointTensorReduction
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FlatCondensedScalarRealization
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatExtendScalars
public import WeilConjectures.SixFunctors.Etale.Derived.PointFiber
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.Analysis.Normed.Group.Ultra
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTensorReduction.NativeIntegralPointTensor
import WeilConjectures.SixFunctors.PointFibreDerivedTensorBasic
import WeilConjectures.CategoryTheory.DerivedCategory.Picard.DerivedTensorSecondFactorFunctor
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.BraidedCochainNormalization
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Integral point-fibre scalar coherence

Source: latest blueprint,
`part-duality-trace-formula/sec-lefschetz-verdier/`
`sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/`
`sk-thm-sf-kunneth-relative/thm-sf-kunneth-relative.md`,
"compatible with finite reduction, scalar extension"; the normalized point-fibre
coefficient-comparison sub-step (blueprint: lem-sf-point-fibre-integral-scalar-coherence).

The map from integral coefficients to a positive finite quotient is written with the
actual quotient by the chosen uniformizer ideal.  The theorem below records the
simultaneous comparison data and its finite-level transition coherence; it postpones
its construction to the proof stage.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

attribute [local instance 20000]
  CategoryTheory.InternalAbelianSheafModule.comparison_essentiallySmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction

/-- The integral condensed coefficient ring attached to a finite coefficient field.

This is the native condensed ring `p_s^* O_E` used by the point-fibre statement.
Source: `def-weil-finite-coefficient-point`
(blueprint: lem-sf-point-fibre-integral-scalar-coherence). -/
noncomputable def integralCoefficient (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) : ScalarSixRing.{u} :=
  ⟨Profinite.padicIntegersRingObj.{u} ell E⟩

/-- The canonical condensed quotient map, given the continuity of the quotient.

The quotient is by the chosen uniformizer ideal and has the discrete topology; this
helper only packages the canonical sheaf map after its continuity proof is supplied.
Source: `def-weil-finite-coefficient-point`
(blueprint: lem-sf-point-fibre-integral-scalar-coherence). -/
noncomputable def nativeMapOf (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (π : PadicAlgCl.integers ell E)
    (qcont : ∀ n : ℕ,
      @Continuous (PadicAlgCl.integers ell E)
        (PadicAlgCl.integers ell E ⧸
          (Ideal.span ({π} : Set (PadicAlgCl.integers ell E))) ^ (n + 1))
        (inferInstance : TopologicalSpace (PadicAlgCl.integers ell E)) ⊥
        (Ideal.Quotient.mk _))
    (n : ℕ) :
    integralCoefficient.{u} ell E ⟶ finiteCoefficient.{u} ell E π n :=
  let A := PadicAlgCl.integers ell E ⧸
    (Ideal.span ({π} : Set (PadicAlgCl.integers ell E))) ^ (n + 1)
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  CommMon.homMk (Mon.Hom.mk
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Ideal.Quotient.mk _) (qcont n))))

set_option maxHeartbeats 2000000 in
-- The site tensor comparison has large derived-category instance arguments.
set_option synthInstance.maxHeartbeats 100000 in
-- Elaborating the native point tensor and its localization involves large site instances.
/-- The point tensor is the localized inverse of the native section cup on every
flat-term K-flat model. The inverse of the chain isomorphism sends each homogeneous
pure tensor to the actual sheaf section tensor in that total summand. The final
square pins the given `PointData.tensorIso`, rather than choosing another tensorator.
Source: `lem-sf-point-ringed-evaluation-model`, chain isomorphism b and its localization;
latest blueprint, `part-duality-trace-formula/sec-lefschetz-verdier/`
`sec-trace-classes-and-the-lefschetz-verdier-formula/sk-p-proper/`
`sk-thm-sf-kunneth-relative/thm-sf-kunneth-relative.md`, proof step 5
(blueprint: lem-sf-point-fibre-integral-scalar-coherence). -/
def NativePointTensor (Λ : ScalarSixRing.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    (d : PointData Λ k) : Prop :=
  ∀ (P Q : CochainComplex (ModuleRingedComparison.internalModules Λ.X (Spec (.of k))) ℤ)
    (_hP : ∀ i : ℤ, ObjectProperty.flat (P.X i))
    (_hQ : ∀ i : ℤ, ObjectProperty.flat (Q.X i))
    (_hkP : (HomologicalComplex.quasiIso
      (ModuleRingedComparison.internalModules Λ.X (Spec (.of k))) (.up ℤ)).kFlat P)
    (_hkQ : (HomologicalComplex.quasiIso
      (ModuleRingedComparison.internalModules Λ.X (Spec (.of k))) (.up ℤ)).kFlat Q),
    let G := CohomologyTransport.sections Λ.X (Spec (.of k))
    ∃ b : (G.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
        (G.mapHomologicalComplex (.up ℤ)).obj P ⊗
          (G.mapHomologicalComplex (.up ℤ)).obj Q,
      (∀ (i j t : ℤ) (h : i + j = t) (x : G.obj (P.X i)) (y : G.obj (Q.X j)),
        (b.inv.f t)
          ((HomologicalComplex.ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj P)
            ((G.mapHomologicalComplex (.up ℤ)).obj Q) i j t h)
              (x ⊗ₜ[condensedScalarRing Λ.X] y)) =
          (G.map (HomologicalComplex.ιTensorObj P Q i j t h))
            (InternalAbelianSheafModule.comparison_internalTmul
              (Scheme.ProEt.topology (Spec (.of k))) (condensedRingObj Λ.X (Spec (.of k)))
              (P.X i) (Q.X j) (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) x y)) ∧
      ∀ (hP : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) (DerivedCategory.Q.obj P))
        (hQ : condensedConstructibleFiniteTor Λ.X (Spec (.of k)) (DerivedCategory.Q.obj Q)),
        (fiber Λ k).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
            G.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
            DerivedCategory.Q.{u + 1, u + 1, u + 2}.map b.hom =
          (d.tensorIso (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) hP hQ).hom ≫
            (G.mapDerivedCategoryFactors.hom.app P ⊗ₘ
              G.mapDerivedCategoryFactors.hom.app Q) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q.{u + 1, u + 1, u + 2}
              ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q)

set_option maxHeartbeats 2000000 in
-- The site tensor comparison has large derived-category instance arguments.
set_option synthInstance.maxHeartbeats 100000 in
-- Elaborating the native point tensor and its localization involves large site instances.
end AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction

namespace AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction

private theorem native_map_comp (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
    (qcont : ∀ n : ℕ,
      @Continuous (PadicAlgCl.integers ell E)
        (PadicAlgCl.integers ell E ⧸ (Ideal.span ({π} : Set _)) ^ (n + 1))
        inferInstance ⊥ (Ideal.Quotient.mk _))
    (m n : ℕ) (h : n ≤ m) :
    nativeMapOf.{u} ell E π qcont m ≫ finiteCoefficientMap ell E π h =
      nativeMapOf ell E π qcont n := by
  rfl

private theorem finite_map_id (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
    (n : ℕ) : finiteCoefficientMap.{u} ell E π (m := n) (n := n) (le_refl n) = 𝟙 _ := by
  let A := PadicAlgCl.integers ell E ⧸ (Ideal.span ({π} : Set _)) ^ (n + 1)
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have hq : Ideal.Quotient.factorPow (Ideal.span ({π} : Set _))
      (Nat.add_le_add_right (le_refl n) 1) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  apply CommMon.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.ext
  intro x
  apply ULift.ext
  change (⟨_, _⟩ : C(S.unop, _)) = x.down
  apply ContinuousMap.ext
  intro y
  exact congrArg (fun f ↦ f (x.down y)) hq

private theorem scalar_map_comp {A B C : ScalarSixRing.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    (scalarMap b).comp (scalarMap a) = scalarMap (a ≫ b) := by
  rfl

private theorem scalar_map_id (A : ScalarSixRing.{u}) : scalarMap (𝟙 A) = RingHom.id _ := by
  rfl

private theorem quotient_mk_continuous (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set (PadicAlgCl.integers ell E)) =
      IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E)) (n : ℕ) :
    @Continuous (PadicAlgCl.integers ell E)
      (PadicAlgCl.integers ell E ⧸ (Ideal.span ({π} : Set _)) ^ (n + 1))
      inferInstance ⊥ (Ideal.Quotient.mk _) := by
  let := PadicAlgCl.normedFieldOfAlgebra ell E
  let := PadicAlgCl.isUltrametricDist_ofAlgebra ell E
  have hπ0 : π ≠ 0 := by
    intro h
    apply PadicAlgCl.maximalIdeal_integers_ne_bot ell E
    rw [← hπ, h]
    simp
  let A := PadicAlgCl.integers ell E ⧸ (Ideal.span ({π} : Set _)) ^ (n + 1)
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have hπE : (π : E) ≠ 0 := fun h ↦ hπ0 (Subtype.ext h)
  have hr : 0 < ‖(π : E)‖ ^ (n + 1) := pow_pos (norm_pos_iff.mpr hπE) _
  have heq (x y : PadicAlgCl.integers ell E) :
      Ideal.Quotient.mk ((Ideal.span ({π} : Set _)) ^ (n + 1)) x =
        Ideal.Quotient.mk ((Ideal.span ({π} : Set _)) ^ (n + 1)) y ↔
      ‖(x : E) - y‖ ≤ ‖(π : E)‖ ^ (n + 1) := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, ha⟩
      have hval := congrArg Subtype.val ha
      change (a : E) * (π : E) ^ (n + 1) = (x : E) - y at hval
      rw [← hval, norm_mul, norm_pow]
      exact mul_le_of_le_one_left (by positivity) a.property
    · intro h
      refine ⟨⟨((x : E) - y) / (π : E) ^ (n + 1), ?_⟩, Subtype.ext ?_⟩
      · change ‖((x : E) - y) / (π : E) ^ (n + 1)‖₊ ≤ 1
        rw [← NNReal.coe_le_coe, coe_nnnorm, norm_div, norm_pow, NNReal.coe_one]
        exact div_le_one_of_le₀ h hr.le
      · change ((x : E) - y) / (π : E) ^ (n + 1) * (π : E) ^ (n + 1) =
          (x : E) - y
        exact div_mul_cancel₀ _ (pow_ne_zero _ hπE)
  refine continuous_discrete_rng.mpr fun q ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hf : (Ideal.Quotient.mk ((Ideal.span ({π} : Set _)) ^ (n + 1))) ⁻¹'
        {Ideal.Quotient.mk _ x} =
      Subtype.val ⁻¹' Metric.closedBall (x : E) (‖(π : E)‖ ^ (n + 1)) := by
    ext y
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall,
      dist_eq_norm] using heq y x
  rw [hf]
  exact (IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage continuous_subtype_val

end AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction
