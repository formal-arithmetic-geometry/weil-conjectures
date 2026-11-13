/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.Localization.Finiteness
import WeilConjectures.AlgebraicGeometry.AffinePolynomialLocalizedTorOfStalkwise
import WeilConjectures.RingTheory.LocalizedPolynomialFiniteProjectiveDimension

/-! # Pointwise projective dimension from stalkwise finite Tor dimension

Source: Stacks Project, Tag 069C, using Tag 068X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Each prime localization of the coordinate algebra has finite projective dimension
as a module over the localized polynomial ring.
Source: Stacks Project, Tag 069C, proof of (3) implies (1), using Tag 068X. -/
theorem affinePolynomial_localized_finiteProjectiveDimension_of_stalkwise
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (g : MvPolynomial (Fin n) Γ(Y, U) →+* Γ(X, V))
    (hg : Function.Surjective g)
    (hcomp : g.comp (MvPolynomial.C) = (f.appLE U V e).hom) :
    ∀ p : PrimeSpectrum (MvPolynomial (Fin n) Γ(Y, U)), ∃ d : ℕ,
      HasProjectiveDimensionLE
        (((ModuleCat.restrictScalars g).obj (ModuleCat.of Γ(X, V) Γ(X, V))).localizedModule
          p.asIdeal.primeCompl) d := by
  intro p
  by_cases hker : RingHom.ker g ≤ p.asIdeal
  · let R := MvPolynomial (Fin n) Γ(Y, U)
    let M := (ModuleCat.restrictScalars g).obj (ModuleCat.of Γ(X, V) Γ(X, V))
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let φ : ModuleCat.of R R ⟶ M :=
      ModuleCat.semilinearMapAddEquiv g _ _ g.toSemilinearMap
    have : Module.Finite R M := Module.Finite.of_surjective φ.hom hg
    have : Module.Finite (Localization p.asIdeal.primeCompl)
        (M.localizedModule p.asIdeal.primeCompl) :=
      Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
        (M.localizedModuleMkLinearMap _)
    obtain ⟨d, hd⟩ :=
      affinePolynomial_localized_finiteTorDimension_of_stalkwise_of_kernel_le
        f hperfect U hU V hV e n g hg hcomp p hker
    exact ModuleCat.localizedPolynomial_finiteProjectiveDimension_of_finiteTor
      n p (M.localizedModule p.asIdeal.primeCompl) d hd
  · obtain ⟨a, ha_ker, ha_p⟩ := IsConcreteLE.not_le_iff_exists.mp hker
    let M := (ModuleCat.restrictScalars g).obj (ModuleCat.of Γ(X, V) Γ(X, V))
    have ha_zero : ∀ m : M, a • m = 0 := by
      intro m
      change g a • m = 0
      rw [RingHom.mem_ker.mp ha_ker, zero_smul]
    have hsub : Subsingleton (M.localizedModule p.asIdeal.primeCompl) := by
      rw [IsLocalizedModule.subsingleton_iff p.asIdeal.primeCompl
        (M.localizedModuleMkLinearMap _)]
      intro m
      refine ⟨a, ?_, ?_⟩
      · exact ha_p
      · exact ha_zero m
    have : Subsingleton (M.localizedModule p.asIdeal.primeCompl) := hsub
    refine ⟨0, ?_⟩
    have hz : IsZero (M.localizedModule p.asIdeal.primeCompl) :=
      ModuleCat.isZero_iff_subsingleton.mpr hsub
    have := hz.hasProjectiveDimensionLT_zero
    infer_instance

end AlgebraicGeometry
