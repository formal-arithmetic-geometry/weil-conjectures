/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.Localization
import WeilConjectures.AlgebraicGeometry.AffinePolynomialSupportedLocalizationStalk
import WeilConjectures.RingTheory.TorVanishingRestrictionFlatBase
import Mathlib.RingTheory.Flat.Localization

/-! Finite Tor dimension on primes containing the presentation kernel.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite Tor dimension over the affine base for a supported prime localization.
Source: Stacks Project, Tag 069C, proof of (3) implies (1). -/
theorem affinePolynomial_localized_finiteTorDimension_of_stalkwise_of_kernel_le
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hperfect : HasStalkwiseFiniteTorDimension f)
    (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (n : ℕ) (g : MvPolynomial (Fin n) Γ(Y, U) →+* Γ(X, V))
    (hg : Function.Surjective g)
    (hcomp : g.comp (MvPolynomial.C) = (f.appLE U V e).hom)
    (p : PrimeSpectrum (MvPolynomial (Fin n) Γ(Y, U)))
    (hker : RingHom.ker g ≤ p.asIdeal) :
    ∃ d : ℕ, ∀ N : ModuleCat.{u} Γ(Y, U), ∀ i : ℕ, d < i →
      IsZero (((Tor' (ModuleCat.{u} Γ(Y, U)) i).obj
        ((ModuleCat.restrictScalars
          ((algebraMap (MvPolynomial (Fin n) Γ(Y, U))
            (Localization p.asIdeal.primeCompl)).comp MvPolynomial.C)).obj
          (((ModuleCat.restrictScalars g).obj
            (ModuleCat.of Γ(X, V) Γ(X, V))).localizedModule
              p.asIdeal.primeCompl))).obj N) := by
  obtain ⟨x, hx, ⟨α⟩⟩ :=
    affinePolynomial_supportedLocalization_stalk f U V hV e n g hg hcomp p hker
  let := Y.presheaf.algebra_section_stalk ⟨f x, e hx⟩
  have := hU.isLocalization_stalk ⟨f x, e hx⟩
  have : Module.Flat Γ(Y, U) (Y.presheaf.stalk (f x)) :=
    IsLocalization.flat _ (hU.primeIdealOf ⟨f x, e hx⟩).asIdeal.primeCompl
  let L := (ModuleCat.restrictScalars (f.stalkMap x).hom).obj
    (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
  obtain ⟨d, hd⟩ := hperfect x
  refine ⟨d, ?_⟩
  intro N i hi
  have hz := ModuleCat.isZero_tor_restrictScalars_of_flat
    Γ(Y, U) (Y.presheaf.stalk (f x)) L N i
    (hd ((ModuleCat.extendScalars
      (algebraMap Γ(Y, U) (Y.presheaf.stalk (f x)))).obj N) i hi)
  let β := ModuleCat.restrictScalarsComp'App
    (Y.presheaf.germ U (f x) (e hx)).hom (f.stalkMap x).hom
    ((f.stalkMap x).hom.comp (Y.presheaf.germ U (f x) (e hx)).hom) rfl
    (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
  exact hz.of_iso (((Tor' (ModuleCat.{u} Γ(Y, U)) i).mapIso (α ≪≫ β.symm)).app N)

end AlgebraicGeometry
