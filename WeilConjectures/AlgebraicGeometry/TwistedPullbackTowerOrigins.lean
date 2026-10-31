/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TwistedPullbackTowerDomainDefinitions
import WeilConjectures.AlgebraicGeometry.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ComparisonTorInterval
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Finite origins and ambient lower bounds from uniform tower bounds -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTwistedTowerDomain

private theorem origin_tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {M N : proEtaleDerivedCategory T A} (e : M ≅ N) (a z : ℤ)
    (h : HasProEtaleTorAmplitude T A M a z) : HasProEtaleTorAmplitude T A N a z := by
  refine ⟨h.1, ?_⟩
  intro L P hL f hf hP Q i hi
  obtain ⟨eL⟩ := hL
  exact h.2 L P ⟨eL ≪≫ e.symm⟩ f hf hP Q i hi


/-- Uniform bounds give independent etale origins and the same ambient lower bound.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-tower-geometric/
sk-prop-sp-tower-geometric-gamma.proof.md, paragraph (2); tower-domain steps 5 and 6.
(blueprint: lem-sp-uniform-bounds-origin-lower)

Proof: at each level use finite-ring constructible derived comparison to descend the
bounded constructible complex. Its Tor interval is reflected by the comparison
Tor-interval equivalence; compose the resulting isomorphism with the given level
identification to form OriginIn. These witnesses are independent and require no
transition maps. For every i below a, exact evaluation identifies the i-th ambient
cohomology tower with level cohomology, which vanishes by the support bound. A strict
system with every level zero is zero: every component of its identity is zero, hence
its identity is zero. Apply DerivedCategory.isGE_iff to obtain the ambient bound.
This argument also covers empty schemes and zero complexes. -/
theorem uniform_bounds_origin_lower
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (b : SpTowerShriek.Base l E) (T : Scheme.{u})
    [IsNoetherian T]
    (K : SpTowerShriek.D l E T) (a z s t : ℤ)
    (_haz : a ≤ z) (hst : s ≤ t)
    (h : SpChartAdmissibility.bounds l E T K a z s t) :
    (∀ n : ℕ, OriginIn l E b T n K s t) ∧ K.IsGE a := by
  classical
  constructor
  · intro n
    let A := SpTowerShriek.R l E n
    let F := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
    let R := ProEtale.finiteCoefficientIntrinsicRealization T A
    obtain ⟨L, ⟨eL⟩⟩ := ((finiteRing_constructibleDerived_origin T A).2.2.1
      ((SpTowerShriek.Ev l E T n).obj K)).mpr
        ⟨(h n).1.2.1, (h n).1.1⟩
    obtain ⟨c, d, hcd, hvan⟩ := L.property.2
    have hplus : DerivedCategory.TStructure.t.plus L.obj :=
      ⟨c, (DerivedCategory.isGE_iff L.obj c).2 fun i hi ↦ hvan i (.inl hi)⟩
    let LP : DerivedCategory.Plus _ := ⟨L.obj, hplus⟩
    let level := F.mapDerivedCategoryPlus.obj LP
    let eComp : R.mapDerivedCategory.obj level.obj ≅
        (SpTowerShriek.Ev l E T n).obj K :=
      R.mapDerivedCategory.mapIso (F.mapDerivedCategoryPlusCompatibility.app LP) ≪≫
        (Functor.mapDerivedCategoryCompIso F R).symm.app L.obj ≪≫ eL
    let ori : SpTowerShriek.Origin l E b T n K :=
      { level := level
        realization := eComp
        witness :=
          { complex := LP
            iso := F.mapDerivedCategoryPlusCompatibility.symm.app LP } }
    refine ⟨ori, L.property, ?_⟩
    apply (ProEtale.comparison_torAmplitudeIn_iff A T s t hst LP).mpr
    exact origin_tor_iso T A eComp.symm s t (h n).2.2
  · apply (DerivedCategory.isGE_iff K a).2
    intro i hi
    let H := (DerivedCategory.homologyFunctor (SpTowerShriek.S l E T) i).obj K
    have hz (n : ℕ) : IsZero ((SpTowerShriek.ev l E T n).obj H) := by
      have hn : IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((SpTowerShriek.Ev l E T n).obj K)) := by
        by_contra hn
        exact (not_lt_of_ge ((h n).2.1 hn).1) hi
      exact hn.of_iso
        (((SpTowerShriek.ev l E T n).mapDerivedCategoryHomologyFunctorIso i).app K)
    apply (IsZero.iff_id_eq_zero H).2
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    have heq := congrArg (fun k ↦ k.val.app (op U.unop.2) x)
      ((hz U.unop.1).eq_of_src
        ((SpTowerShriek.ev l E T U.unop.1).map (𝟙 H))
        ((SpTowerShriek.ev l E T U.unop.1).map (0 : H ⟶ H)))
    exact heq


end AlgebraicGeometry.ProEtale.SpTwistedTowerDomain
