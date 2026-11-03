/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import Mathlib.CategoryTheory.Monoidal.Internal.Limits
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Ring.Compact

/-! # Integral sections computed through finite residue coefficients

Source: current blueprint prop-cohomological-finiteness, final paragraph of step 4.
(blueprint: lem-weil-connected-integral-coefficient-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace WeilConjectures.CohomologicalFiniteness

private instance (X : Scheme.{u}) : (upperStarFromPoint X).Additive := by
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint X) :=
    (upperStarFromPointAdjunction X).leftAdjoint_preservesColimits
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (upperStarFromPoint X)
  exact Functor.additive_of_preservesBinaryBiproducts _

set_option maxHeartbeats 800000 in
-- The point adjunction expands the two inverse-image functors.
private theorem continuous_constants_pullback (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] (t : T) :
    (condensedRingScalarSections (Profinite.continuousMapRingObj T) X
        (Profinite.continuousMapConstRingHom T t)).hom ≫ continuousMapComparison X T =
      (continuousMapSectionRingHom X T (ContinuousMap.const X t)).hom := by
  change (Γ.mapFunctor (upperStarFromPoint X)
    (Profinite.continuousMapConstRingHom T t)).hom ≫ _ = _
  rw [Γ.mapFunctor_hom, Category.assoc]
  refine (upperStarFromPointAdjunction X).ε_comp_map_comp_homEquiv_symm_eq _ _ _ ?_
  refine Sheaf.unitHomEval_injective (J := coherentTopology Profinite.{u})
    Profinite.isTerminalPUnit _ ?_
  have hs : Sheaf.unitHomEval (J := coherentTopology Profinite.{u})
      (Profinite.of PUnit.{u + 1}) (Profinite.continuousMapConstRingHom T t).hom =
        ULift.up (ContinuousMap.const (Profinite.of PUnit.{u + 1}) t) :=
    Sheaf.unitHomEval_ringHomΓSheafCompose (J := coherentTopology Profinite.{u})
      (Profinite.of PUnit.{u + 1}) (Profinite.continuousMapRingSheaf.{u} T)
      (Profinite.continuousMapConstSectionRingHom.{u} T) (fun _ _ ↦ rfl) t
  rw [Sheaf.unitHomEval_comp (J := coherentTopology Profinite.{u}), hs]
  rw [Functor.LaxMonoidal.comp_ε, Functor.comp_map, Category.assoc, ← Functor.map_comp]
  erw [Sheaf.unitHomEval_ε_comp_sheafPushforwardContinuous_map
    (J := coherentTopology Profinite.{u}) (K := Scheme.ProEt.topology specZ.{u})
    (T := Profinite.of PUnit.{u + 1}) profiniteToProEt.{u}
    (Scheme.ProEt.isTerminalMkId specZ.{u})]
  rw [unitHomEval_ε_comp_lowerStar_map (toSpecZ X),
    unitHomEval_continuousMapSectionRingHom]
  rfl


private def coefficientFunction (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (s : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶
      condensedRingObj (Profinite.continuousMapRingObj T) X) : C(X, T) :=
  (Sheaf.unitHomEval (J := Scheme.ProEt.topology X) (Scheme.ProEt.mk (𝟙 X))
    (s ≫ continuousMapComparison X T)).down

private theorem coefficientFunction_naturality (X : Scheme.{u})
    {T S : Type} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (φ : T →+* S) (hφ : Continuous φ)
    (s : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶
      condensedRingObj (Profinite.continuousMapRingObj T) X) :
    coefficientFunction X S
        (s ≫ (completedCoefficientMap X
          (Profinite.continuousMapRingSheafMap φ hφ)).hom) =
      (⟨φ, hφ⟩ : C(T, S)).comp (coefficientFunction X T s) := by
  unfold coefficientFunction
  rw [Category.assoc]
  rw [show (completedCoefficientMap X (Profinite.continuousMapRingSheafMap φ hφ)).hom ≫
      continuousMapComparison X S = continuousMapComparison X T ≫
        (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (continuousMapRingSheafMap X φ hφ) from continuousMapComparison_naturality X φ hφ]
  rw [← Category.assoc]
  rfl

private theorem coefficientFunction_constant (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] (t : T) :
    coefficientFunction X T
        (condensedRingScalarSections (Profinite.continuousMapRingObj T) X
          (Profinite.continuousMapConstRingHom T t)).hom = ContinuousMap.const X t := by
  unfold coefficientFunction
  rw [continuous_constants_pullback, unitHomEval_continuousMapSectionRingHom]
  rfl

private theorem coefficientFunction_injective (X : Scheme.{u}) (T : Type)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [T2Space T] [TotallyDisconnectedSpace T] : Function.Injective (coefficientFunction X T) := by
  intro s t h
  apply (cancel_mono (continuousMapComparison X T)).1
  apply Sheaf.unitHomEval_injective.{u + 1} (J := Scheme.ProEt.topology X)
    (Scheme.ProEt.isTerminalMkId X)
  exact ULift.ext _ _ h

set_option maxHeartbeats 1000000 in
-- The limit cone and its finite quotient normalizations expand several ring-object instances.
/-- Global integral sections are constant, by their finite residue projections.

Source: current blueprint prop-cohomological-finiteness, final paragraph of step 4;
coefficient comparison sk-prop-sfb-qlbar-colimit-x.
(blueprint: lem-weil-connected-integral-coefficient-sections).

Proof: choose a uniformizer and the coefficient limit cone. Evaluate an integral
section at any point of the nonempty connected scheme to obtain an integer r.
Every finite residue projection is a section of the finite constant residue sheaf,
hence a continuous map to a finite discrete ring, and is constant with value the
reduction of r. Naturality of the coefficient comparison identifies these projections
with the reductions of the scalar r. The universal property of the integral limit
makes the original section equal to that scalar. Evaluation proves injectivity.
Only the finite residue coefficient comparisons are required to be invertible.
-/
theorem connected_integralScalarSections_bijective (X : Scheme.{u}) [ConnectedSpace X]
    (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell) :
    Function.Bijective
      (condensedRingScalarSections (Profinite.padicIntegersRingObj ell E) X) := by
  classical
  let := PadicAlgCl.normedFieldOfAlgebra ell E.1
  let : NormedAlgebra ℚ_[ell] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ell) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ell) x‖
        erw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let : ProperSpace E.1 := FiniteDimensional.proper ℚ_[ell] E.1
  let R := PadicAlgCl.integers ell E
  have hball : (R : Set E.1) = Metric.closedBall 0 1 := by
    ext x
    change ‖x‖₊ ≤ 1 ↔ dist x 0 ≤ 1
    simp only [dist_zero_right, ← NNReal.coe_le_coe, NNReal.coe_one]
    rfl
  let : CompactSpace R := isCompact_iff_compactSpace.mp
    (hball ▸ isCompact_closedBall (0 : E.1) 1)
  obtain ⟨π, hπ⟩ := PadicAlgCl.isPrincipal_maximalIdeal_integers ell E.1
  have hπ' : Ideal.span {π} = IsLocalRing.maximalIdeal R := by
    simpa only [Ideal.submodule_span_eq] using hπ.symm
  obtain ⟨⟨c, e, he, ⟨hc⟩⟩, hfin, _⟩ := completedCondensedIntegral X ell E π hπ'
  let Q := completedResidue ell E π
  let : ∀ n, Finite (Q n) := hfin
  let : ∀ n, DiscreteTopology (Q n) := fun n ↦ by
    apply QuotientAddGroup.discreteTopology
    change IsOpen (X := R) ↑(Ideal.span {π} ^ (n + 1))
    erw [hπ']
    exact IsLocalRing.isOpen_maximalIdeal_pow R (n + 1)
  let x : X := Classical.choice inferInstance
  have hnorm (r : R) : coefficientFunction X R
      (condensedRingScalarSections (Profinite.padicIntegersRingObj ell E) X
        (Profinite.continuousMapConstRingHom R r)).hom = ContinuousMap.const X r :=
    coefficientFunction_constant X R r
  constructor
  · intro a b hab
    obtain ⟨r, rfl⟩ := Profinite.continuousMapConstRingHom_surjective R a
    obtain ⟨s, rfl⟩ := Profinite.continuousMapConstRingHom_surjective R b
    have h := congrArg (fun z ↦ coefficientFunction X R z.hom x) hab
    rw [hnorm, hnorm] at h
    exact congrArg _ h
  · intro s
    let r : R := coefficientFunction X R s.hom x
    refine ⟨Profinite.continuousMapConstRingHom R r, ?_⟩
    apply Γ.ext
    apply (cancel_mono e.hom.hom).1
    apply (isLimitOfPreserves (Mon.forget _) hc).hom_ext
    intro n
    change _ ≫ (c.π.app n).hom = _ ≫ (c.π.app n).hom
    have he' : e.hom.hom ≫ (c.π.app n).hom =
        (completedCoefficientMap X (completedReduction ell E π n.unop)).hom :=
      congrArg Mon.Hom.hom (he n.unop)
    simp only [Category.assoc, he']
    let : T2Space (Q n.unop) := DiscreteTopology.toT2Space
    let : TotallySeparatedSpace (Q n.unop) := TotallySeparatedSpace.of_discrete _
    let : TotallyDisconnectedSpace (Q n.unop) :=
      TotallySeparatedSpace.totallyDisconnectedSpace _
    let q : R →+* Q n.unop := Ideal.Quotient.mk _
    let t := (condensedRingScalarSections (Profinite.padicIntegersRingObj ell E) X
      (Profinite.continuousMapConstRingHom R r)).hom
    have hf : (⟨q, continuous_quot_mk⟩ : C(R, Q n.unop)).comp
        (coefficientFunction X R t) =
      (⟨q, continuous_quot_mk⟩ : C(R, Q n.unop)).comp
        (coefficientFunction X R s.hom) := by
      rw [show coefficientFunction X R t = ContinuousMap.const X r from hnorm r]
      apply ContinuousMap.ext
      intro y
      have hlocal : IsLocallyConstant (fun y : X ↦ q (coefficientFunction X R s.hom y)) :=
        (IsLocallyConstant.iff_continuous _).mpr
          ((show Continuous q from continuous_quot_mk).comp
            (coefficientFunction X R s.hom).continuous)
      exact hlocal.apply_eq_of_preconnectedSpace x y
    apply coefficientFunction_injective X (Q n.unop)
    exact (coefficientFunction_naturality X q continuous_quot_mk t).trans
      (hf.trans (coefficientFunction_naturality X q continuous_quot_mk s.hom).symm)

end WeilConjectures.CohomologicalFiniteness
