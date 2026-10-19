/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker E6
-/
module

public import Sheaf.RepresentationTheory.ProcyclicComplex
public import Sheaf.RepresentationTheory.DiscreteContinuousCohomology
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Sheaf.RepresentationTheory.ProcyclicDeltaFunctor
import Sheaf.RepresentationTheory.ProcyclicInvariants
import Sheaf.RepresentationTheory.ProcyclicEffacement
import Sheaf.RepresentationTheory.ContinuousCochainsInvariantsZero
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal

/-!
# Cohomology comparison for the procyclic action complex

The two-term delta-functor and derived invariants are universal and agree in degree zero.
Their universal properties identify them naturally in every degree.

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer/lem-exc-procyclic-two-term,
proof steps 5--9 (blueprint: lem-exc-procyclic-two-term).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace Rep

private theorem universalDeltaFunctor_iso
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (T R : CohomologicalDeltaFunctor C D) (hT : T.IsUniversal) (hR : R.IsUniversal)
    (e : T.F 0 ≅ R.F 0) (q : ℕ) : Nonempty (T.F q ≅ R.F q) := by
  obtain ⟨α, hα, _⟩ := hT R e.hom
  obtain ⟨β, hβ, _⟩ := hR T e.inv
  let idT : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ 𝟙 (T.F n), by intros; simp⟩
  let idR : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ 𝟙 (R.F n), by intros; simp⟩
  let αβ : CohomologicalDeltaFunctor.Hom T T :=
    ⟨fun n ↦ α.app n ≫ β.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [α.naturality S hS n]
      simp only [Category.assoc]
      rw [β.naturality S hS n]⟩
  let βα : CohomologicalDeltaFunctor.Hom R R :=
    ⟨fun n ↦ β.app n ≫ α.app n, by
      intro S hS n
      simp only [NatTrans.comp_app, ← Category.assoc]
      rw [β.naturality S hS n]
      simp only [Category.assoc]
      rw [α.naturality S hS n]⟩
  have hαβ : αβ = idT := (hT T (𝟙 (T.F 0))).unique
    (by change α.app 0 ≫ β.app 0 = _; rw [hα, hβ]; exact e.hom_inv_id)
    rfl
  have hβα : βα = idR := (hR R (𝟙 (R.F 0))).unique
    (by change β.app 0 ≫ α.app 0 = _; rw [hβ, hα]; exact e.inv_hom_id)
    rfl
  refine ⟨⟨α.app q, β.app q, ?_, ?_⟩⟩
  · exact congrArg (fun f : CohomologicalDeltaFunctor.Hom T T ↦ f.app q) hαβ
  · exact congrArg (fun f : CohomologicalDeltaFunctor.Hom R R ↦ f.app q) hβα

/-- Two natural realizations of fixed vectors are naturally isomorphic. Keeping the
functors abstract here avoids unfolding their chosen constructions during naturality. -/
private theorem invariantRealizations_iso
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type u) [Ring A]
    (V V' : DiscreteContinuousRep.{u, 0, w} A G ⥤ ModuleCat.{w} A)
    (t : ∀ M : DiscreteContinuousRep.{u, 0, w} A G,
      V.obj M ≃ₗ[A] (⨅ g, LinearMap.ker (M.obj.ρ g - LinearMap.id) :
        Submodule A M.obj.V))
    (t' : ∀ M : DiscreteContinuousRep.{u, 0, w} A G,
      V'.obj M ≃ₗ[A] (⨅ g, LinearMap.ker (M.obj.ρ g - LinearMap.id) :
        Submodule A M.obj.V))
    (ht : ∀ (M N : DiscreteContinuousRep.{u, 0, w} A G) (f : M ⟶ N) (x : V.obj M),
      (t N ((V.map f).hom x)).val = f.hom.hom (t M x).val)
    (ht' : ∀ (M N : DiscreteContinuousRep.{u, 0, w} A G) (f : M ⟶ N) (x : V'.obj M),
      (t' N ((V'.map f).hom x)).val = f.hom.hom (t' M x).val) :
    Nonempty (V' ≅ V) := by
  exact ⟨NatIso.ofComponents
    (fun M ↦ ((t' M).trans (t M).symm).toModuleIso) (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (t N).injective
      change t N ((t N).symm (t' N ((V'.map f).hom x))) =
        t N ((V.map f).hom ((t M).symm (t' M x)))
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [ht', ht, LinearEquiv.apply_symm_apply])⟩

set_option linter.style.haveILetI false in
/-- The continuous cohomology functors are naturally represented by the explicit
two-term action complex for the additive generator of `ℤ_[l]`.

Proof: the explicit two-term complex gives a cohomological delta-functor. The coinduced
embedding effaces its positive degrees by the periodic primitive theorem. Its degree zero
is naturally invariants, since the additive generator has dense cyclic span. The chosen
invariants functor is left exact: identify it with the invariant functor in the continuous
cochain degree-zero theorem. Its right derived functors form a universal delta-functor.
Both universal delta-functors therefore agree in degree zero. Extend that isomorphism
and its inverse by universality; uniqueness makes the composites identities.

Source: blueprint, sec-smooth-purity/sk-prop-a1-kummer/lem-exc-procyclic-two-term,
proof steps 5--9 (blueprint: lem-exc-procyclic-two-term-comparison). -/
theorem procyclic_twoTerm_cohomology_comparison
    (l : ℕ) [Fact l.Prime] (s : ℕ) (A : Type u) [Ring A] [Finite A]
    (hA : (l ^ s : ℕ) • (1 : A) = 0) :
    ∀ q : ℕ, Nonempty
      (discreteContinuousCohomologyFunctor.{0, u, w} (Multiplicative ℤ_[l]) A q ≅
        actionTwoTerm A (Multiplicative ℤ_[l])
          (Multiplicative.ofAdd (1 : ℤ_[l])) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{w} A)
            (ComplexShape.up ℕ) q) := by
  classical
  let h := Classical.choose (discreteModules_abelian.{0, u, w} (Multiplicative ℤ_[l]) A)
  letI := h
  letI : Preadditive (DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l])) :=
    h.toPreadditive
  letI : Preadditive (ModuleCat.{w} A) :=
    (inferInstance : Abelian (ModuleCat.{w} A)).toPreadditive
  letI := (Classical.choose_spec
    (discreteModules_abelian.{0, u, w} (Multiplicative ℤ_[l]) A)).choose_spec.1
  letI : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
      TopologicalSpace M.obj.V := fun _ ↦ ⊥
  letI : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
      DiscreteTopology M.obj.V := fun _ ↦ ⟨rfl⟩
  letI : ∀ M : DiscreteContinuousRep.{u, 0, w} A (Multiplicative ℤ_[l]),
      ContinuousConstSMul A M.obj.V := fun _ ↦ ⟨fun _ ↦ continuous_of_discreteTopology⟩
  let comparison := continuousCochains_derived_invariants.{0, u, w} (Multiplicative ℤ_[l]) A
  let V := Classical.choose comparison
  let a := Classical.choose (Classical.choose_spec comparison)
  letI : V.Additive := a
  obtain ⟨t, ht, F, e, hmap, hd, _⟩ :=
    Classical.choose_spec (Classical.choose_spec comparison)
  obtain ⟨V', a', t', ht', hlim, _⟩ := continuousCochains_invariants_zero.{0, u, w}
    (Multiplicative ℤ_[l]) A F e hmap hd
  obtain ⟨eV⟩ := invariantRealizations_iso (Multiplicative ℤ_[l]) A V V' t t' ht ht'
  letI : PreservesFiniteLimits V' := hlim
  letI : PreservesFiniteLimits V := preservesFiniteLimits_of_natIso eV
  obtain ⟨R, hR, hRuniv, ⟨eR⟩⟩ := V.exists_universal_rightDerived_deltaFunctor
  obtain ⟨T, hT⟩ := actionTwoTerm_deltaFunctor.{u, 0, w} (Multiplicative ℤ_[l]) A
    (Multiplicative.ofAdd (1 : ℤ_[l]))
  have hTuniv : T.IsUniversal := effaceable_deltaFunctor_isUniversal T
    (actionTwoTerm_effaceable l s A hA T hT)
  obtain ⟨eT⟩ := actionTwoTerm_homology_zero l A V t ht
  have eT' : T.F 0 ≅ V := by rw [hT]; exact eT
  have eR' : R.F 0 ≅ V := by rw [hR]; exact eR
  intro q
  obtain ⟨eRT⟩ := universalDeltaFunctor_iso R T hRuniv hTuniv (eR' ≪≫ eT'.symm) q
  rw [hR, hT] at eRT
  exact ⟨eRT⟩

end Rep
