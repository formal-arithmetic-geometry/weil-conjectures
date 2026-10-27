/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.Paper.TorsionCdTopologicalSerreTransfer
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.AlgebraicGeometry.Sites.AffineCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.AffineSepclosedEtaleAcyclic

/-! # An affine cohomology bound over a profinite geometric base

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph, affine-local input
(blueprint: lem-sfb-affine-profinite-family-serre-cd).

The affine torsion argument is motivated by Stacks Tag 0F0V. The final transfer to
ordinary continuous topological coefficients is a separate, still open source obligation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme

private theorem field_strictLocalization_of_zeroDimensional
    (C : Scheme.{u}) [IsAffine C] [IsReduced C]
    (hCdim : ∀ p : PrimeSpectrum Γ(C, ⊤), p.asIdeal.IsMaximal)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ C) :
    IsField (strictHenselization s) := by
  have hdimC : topologicalKrullDim C ≤ 0 := by
    rw [C.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
    change topologicalKrullDim (PrimeSpectrum Γ(C, ⊤)) ≤ 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (Ring.krullDimLE_zero_iff.mpr (fun p hp ↦ hCdim ⟨p, hp⟩)).1
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro a ha
  have ha' : strictHenselizationEval s a = 0 :=
    (mem_maximalIdeal_strictHenselization_iff a).mp ha
  obtain ⟨N, hN⟩ := exists_specPointedEtaleNeighborhood_forall_mem_range 1 (fun _ ↦ a)
  obtain ⟨c, rfl⟩ := hN 0
  rw [SpecPointedEtaleNeighborhood.strictHenselizationEval_ι] at ha'
  let : AlgebraicGeometry.Etale N.hom := N.etale
  have : IsReduced (Spec N.R) := isReduced_of_etale N.hom
  have : _root_.IsReduced N.R := by
    exact (affine_isReduced_iff N.R).mp inferInstance
  have : Ring.KrullDimLE 0 N.R := by
    constructor
    change ringKrullDim N.R ≤ 0
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact N.hom.topologicalKrullDim_le_of_etale.trans hdimC
  let q : Ideal N.R := RingHom.ker N.pt.hom
  let : q.IsPrime := RingHom.ker_isPrime _
  have : Ring.KrullDimLE 0 (Localization.AtPrime q) :=
    Ring.KrullDimLE.of_isLocalization q (Ideal.mem_minimalPrimes_iff_isPrime.mpr
      (inferInstance : q.IsPrime)) _
  have hf := Ring.KrullDimLE.isField_of_isReduced (R := Localization.AtPrime q)
  have hz : algebraMap N.R (Localization.AtPrime q) c = 0 := by
    have hc : algebraMap N.R (Localization.AtPrime q) c ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q c).mpr ha'
    rwa [(IsLocalRing.isField_iff_maximalIdeal_eq.mp hf), Ideal.mem_bot] at hc
  obtain ⟨⟨t, ht⟩, htc⟩ :=
    (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) c).mp hz
  have hu : IsUnit (N.ι t) := isUnit_of_strictHenselizationEval_ne_zero (by
    rw [SpecPointedEtaleNeighborhood.strictHenselizationEval_ι]
    exact ht)
  exact hu.mul_right_eq_zero.mp (by rw [← map_mul, htc, map_zero])

private theorem torsionCd_of_affine_zeroDimensional
    {C V : Scheme.{u}} [IsAffine C] [IsReduced C] [IsAffine V]
    (hCdim : ∀ p : PrimeSpectrum Γ(C, ⊤), p.asIdeal.IsMaximal)
    (hCres : ∀ c : C, IsSepClosed (C.residueField c))
    (f : V ⟶ C) [LocallyOfFiniteType f] (e : ℕ)
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (c : Spec (.of K) ⟶ C),
      topologicalKrullDim (pullback f c : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    V.HasTorsionEtaleCohomologicalDimensionLE e := by
  have hclosed : ∀ c : C, IsClosed ({c} : Set C) := by
    intro c
    let E := C.isoSpec.hom.homeomorph
    have hc := (PrimeSpectrum.isClosed_singleton_iff_isMaximal (E c)).mpr (hCdim (E c))
    simpa only [Set.image_singleton, E.symm_apply_apply] using E.symm.isClosedMap _ hc
  intro F hF n hn
  obtain ⟨E⟩ := nonempty_sheafH_extDerivedIso V n
  have hH : Subsingleton (Sheaf.H F n) := by
    apply Etale.subsingleton_H_of_rightDerived_lowerStar f F (c := 0) (e := e) ?_
      (fun p q hp ↦ subsingleton_H_of_affine_closed_isSepClosed C hclosed hCres _ p hp)
      n (by simpa using hn)
    intro q hq
    let G := (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)
    have hstalk (c : C) :
        IsZero ((pointSmallEtale (C.algClosurePoint c)).sheafFiber.obj G) := by
      let s := C.algClosurePoint c
      let H := ↑(strictHenselization s)
      let : Field H := (field_strictLocalization_of_zeroDimensional C hCdim s).toField
      have : IsSepClosed H := IsSepClosed.of_ringEquiv
        (RingEquiv.ofBijective (IsLocalRing.residue H)
          ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩).symm
      let t := strictLocalizationToBase s
      let a := pullback.snd f t
      let k := AlgebraicClosure H
      let b := Spec.map (CommRingCat.ofHom (algebraMap H k))
      have hd : topologicalKrullDim (pullback f t : Scheme.{u}) ≤ (e : WithBot ℕ∞) := by
        rw [← topologicalKrullDim_pullback_eq_of_field a b]
        rw [IsHomeomorph.topologicalKrullDim_eq _
          (pullbackLeftPullbackSndIso f t b).hom.homeomorph.isHomeomorph]
        exact he k (b ≫ t)
      let F' := (Etale.upperStar AddCommGrpCat.{u + 1} (pullback.fst f t)).obj F
      have hF' : F'.IsTorsion := Etale.isTorsion_upperStar _ hF
      have hzH : Subsingleton (Sheaf.H F' q) :=
        subsingleton_H_of_lt_of_isAffine_of_isSepClosed e a hd F' hF' q hq
      obtain ⟨eq⟩ := nonempty_sheafH_extDerivedIso (pullback f t) q
      have hz : IsZero ((Etale.cohomology AddCommGrpCat.{u + 1}
          (pullback f t) q).obj ((DerivedCategory.singleFunctor _ 0).obj F')) := by
        apply AddCommGrpCat.isZero_iff_subsingleton.mpr
        have : Subsingleton ((Sheaf.functorH _ q).obj F') := hzH
        exact (eq.app F').addCommGroupIsoToAddEquiv.symm.injective.subsingleton
      obtain ⟨r, _, hr⟩ := (Etale.strictHenselizationStalkFormula f s F hF q).1
      have := hr
      have hzPlus := hz.of_iso ((Etale.cohomology AddCommGrpCat.{u + 1}
        (pullback f t) q).mapIso ((DerivedCategory.Plus.singleFunctorιIso _ 0).app F'))
      have hz' := hzPlus.of_iso
        (asIso (r ≫ Etale.strictHenselizationCohomologyComparison s f F q))
      exact hz'.of_iso ((pointSmallEtale s).sheafFiber.mapIso
        (Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso
          (Etale.lowerStar AddCommGrpCat.{u + 1} f) F q)).symm
    have : IsZero G := by
      apply (IsZero.iff_id_eq_zero G).mpr
      apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
      intro c
      exact (hstalk c).eq_of_src _ _
    exact this
  have : Subsingleton ((Sheaf.functorH _ n).obj F) := hH
  exact (E.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Affine finite-type families over reduced zero-dimensional w-contractible bases
with separably closed residue fields have ordinary module-object cohomology zero above
`e + 2` on the weak Serre coproduct closure of finite constant-model constructible modules.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph; agent-formulated affine
obligation, motivated on the torsion branch by Stacks Tag 0F0V. An exact reference for
the full topological-coefficient transfer remains wanted
(blueprint: lem-sfb-affine-profinite-family-serre-cd).

Proof:
1. The affine spectrum of C has dimension at most zero. For any geometric point s,
   every affine pointed etale neighborhood has reduced coordinate ring of dimension
   at most zero. Its localization at the pointing kernel is a field. An element
   evaluating to zero is therefore killed by an element outside that kernel, which
   becomes a unit in the strict henselization. Thus the strict henselization is a
   field. Its residue field is separably closed, so the field itself is separably
   closed. This avoids choosing or identifying an algebraic strict henselization.
2. For an affine etale v : V -> U, put f = v followed by g. Etale morphisms do not
   increase topological dimension, including after base change. Pullback pasting
   therefore gives the same geometric fibre bound e for f.
3. Base change the strict-local fibre of f to an algebraic closure of its field.
   Invariance of dimension under field extension and pullback pasting bound its
   dimension by e. The affine Artin theorem over a separably closed field gives
   vanishing above e for every torsion sheaf on this strict-local fibre.
4. Inverse image preserves torsion. The strict-henselization stalk formula and the
   degree-zero derived-functor comparison identify all geometric stalks of R^q f_*F
   with the zero groups from step 3. Geometric stalk conservativity gives R^q f_*F = 0.
5. The affine spectrum hypothesis says every point of C is closed. Together with
   the residue-field hypothesis, affine etale acyclicity kills all positive-degree
   cohomology on C. Leray vanishing with base bound zero gives the uniform torsion
   bound e on V. All arguments include empty schemes and empty fibres.
6. Apply torsionCd_topological_serreHeart_cohomology_vanishes to this uniform bound.
   Its coefficient choices, norm topology, uncompleted module category, generators
   and weak Serre coproduct closure are exactly those in this statement. This last
   transfer remains an independent coefficient theorem with an explicitly wanted
   reference; torsion vanishing is never applied directly to a non-torsion module.
-/
theorem affine_profinite_family_serreHeart_cohomology_vanishes
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    {C U : Scheme.{u}} [IsAffine C] [IsReduced C] [IsAffine U]
    [IsWContractibleRing Γ(C, ⊤)]
    (hCdim : ∀ p : PrimeSpectrum Γ(C, ⊤), p.asIdeal.IsMaximal)
    (hCres : ∀ c : C, IsSepClosed (C.residueField c))
    (g : U ⟶ C) [LocallyOfFiniteType g] [QuasiCompact g] (e : ℕ)
    (he : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (c : Spec (CommRingCat.of K) ⟶ C),
      topologicalKrullDim (pullback g c : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hN : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible Λ U) N)
    (r : ℤ) (hr : (e : ℤ) + 2 < r) :
    IsZero ((DerivedCategory.homologyFunctor _ r).obj
      ((condensedModuleSections Λ U).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N))) := by
  apply torsionCd_topological_serreHeart_cohomology_vanishes ℓ Λ hΛ U e ?_ N hN r hr
  intro V v _ _
  apply Scheme.torsionCd_of_affine_zeroDimensional hCdim hCres (v ≫ g) e
  intro K _ _ c
  rw [← IsHomeomorph.topologicalKrullDim_eq _
    (pullbackRightPullbackFstIso g c v).hom.homeomorph.isHomeomorph]
  exact (pullback.snd v (pullback.fst g c)).topologicalKrullDim_le_of_etale.trans (he K c)

end AlgebraicGeometry.ProEtale.CondensedRing
