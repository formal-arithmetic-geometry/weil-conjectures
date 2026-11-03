/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
public import WeilConjectures.ConstructibleSheaf.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import all WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.SixFunctors.Etale.Derived.Stability.HomDevissage

/-! Constructibility and Tor bounds for the locally projective coefficient Hom. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open CoefficientPairingChange

/-- Local finite projectivity gives the constructibility and Tor conclusions.
Source: the finite-projective dual calculation in paragraph 3 of
`thm-coef-finite-hom`.

The trivializing modules have finite underlying sets because the coefficient ring
is finite. The finite-value criterion makes `L` finite locally constant. Every
separably closed geometric point lifts to the cover, where its stalk is projective
and hence flat; the stalk criterion makes `L` flat. The existing single-sheaf and
internal-Hom stability theorems now give bounded constructibility and finite Tor
amplitude. The predicate comparison transports these to the paper's conventions.
(blueprint: lem-coef-locally-projective-coefficient-hom-constructibility). -/
theorem locallyProjectiveCoefficientHom_constructibility
    {A : Type (u + 1)} [CommRing A] [Finite A]
    (T : Scheme.{u})
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ P : ModuleCat.{u + 1} A, Module.Finite A P ∧ Module.Projective A P ∧
        Nonempty (L.over (d.cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj P))
    (N : DerivedCategoryModule A T)
    (hN : DerivedCategory.isBoundedConstructible A T N ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b N) :
    (DerivedCategory.isBoundedConstructible A T
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) ∧
    (DerivedCategory.isBoundedConstructible A T
        (((derivedHom (ModuleCat.{u + 1} A) T).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L))).obj N) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b
        (((derivedHom (ModuleCat.{u + 1} A) T).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L))).obj N))  := by
  classical
  obtain ⟨d, hd⟩ := hL
  have hflc : Scheme.IsFiniteLocallyConstantSheaf L := by
    apply (Scheme.finite_locally_constant_module_values_iff L).1.mp
    refine ⟨d, fun i ↦ ?_⟩
    obtain ⟨P, hP, _, eP⟩ := hd i
    let : Module.Finite A P := hP
    exact ⟨P, Module.finite_of_finite A, eP⟩
  let : Scheme.IsFiniteLocallyConstantSheaf L := hflc
  have hflat : ObjectProperty.flat L := by
    apply (AlgebraicGeometry.Etale.flat_iff_forall_flat_sheafFiber_obj L).mpr
    intro Ω _ _ s
    have : Scheme.JointlySurjective Scheme.etalePrecoverage.{u} :=
      inferInstanceAs (Scheme.JointlySurjective (Scheme.precoverage @Etale))
    obtain ⟨i, x, hx⟩ := d.cover.exists_eq (s default)
    have : Etale (d.cover.f i) := d.cover.map_prop i
    obtain ⟨t, ht, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
      (d.cover.f i) s x hx
    obtain ⟨P, _, hproj, ⟨eP⟩⟩ := hd i
    let : Module.Projective A P := hproj
    have e := Scheme.constantValueStalkIso L (d.cover.etalePrecoverageToEtale i) P eP t
    have hf : ObjectProperty.flat
        (((Scheme.pointSmallEtale (t ≫ d.cover.f i)).sheafFiber
          (A := ModuleCat.{u + 1} A)).obj L) := by
      apply ObjectProperty.prop_of_iso _ e.symm
      exact (ModuleCat.flat_iff_flat P).mpr (Module.Flat.of_projective (R := A))
    rw [ht] at hf
    exact ObjectProperty.prop_of_iso _
      (((Scheme.pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} A)).app L).symm hf
  let : Scheme.IsConstructibleSheaf L := hflc.isConstructibleSheaf
  have hsingle : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) :=
    ⟨DerivedCategory.boundedConstructible_singleFunctor_obj L 0,
      0, 0, torAmplitudeIn_singleFunctor_obj_of_flat A L hflat⟩
  have hNctf : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T N :=
    (AlgebraicGeometry.flatModel_etale_ctf_iff T A N).mp ⟨hN.1.1, hN.1.2, hN.2⟩
  have hHom := constructibleFiniteTor_derivedHom_singleFunctor_of_isFiniteLocallyConstantSheaf
    A L hflat hNctf
  have hs := (AlgebraicGeometry.flatModel_etale_ctf_iff T A _).mpr hsingle
  have hh := (AlgebraicGeometry.flatModel_etale_ctf_iff T A _).mpr hHom
  exact ⟨⟨⟨hs.1, hs.2.1⟩, hs.2.2⟩, ⟨⟨hh.1, hh.2.1⟩, hh.2.2⟩⟩

end AlgebraicGeometry.Etale
