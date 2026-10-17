/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariant

/-!
# The section invariant and the family object lie in `Pic(D^b_{ctf})`

Blueprint `def-pur-section-invariant` and `def-pur-dnc-section-family` place the section
invariant `𝒞(g, s) = Ls^* ω_g` and the family object `F = Ls̃^* ω_{g̃}` in
`Pic(D^b_{ctf}(-, Λ))`: they are ⊗-invertible
(`AlgebraicGeometry.Etale.isInvertible_sectionInvariant`,
`AlgebraicGeometry.Etale.isInvertible_deformationFamilyObject`) and, over a base of finite type
over a field, they lie in `D^b_{ctf}`, since `Rg^!` and `Ls^*` preserve `D^b_{ctf}`
(`sk-thm-sf-ctf-stability`).

## Main statements

- `AlgebraicGeometry.Etale.boundedConstructibleFiniteTor_sectionInvariant`
- `AlgebraicGeometry.Etale.isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant`
- `AlgebraicGeometry.Etale.isInvertible_and_boundedConstructibleFiniteTor_deformationFamilyObject`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}} (d : ℕ)

/-- The dualizing complex `ω_g = Rg^! Λ_B` of a morphism `g` smooth of pure relative dimension
`d` lies in `D^b_{ctf}(V, Λ)`: it is `L[2d]` for a locally constant sheaf `L` whose stalks are
free of rank one (`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`), so `L` is a
finite locally constant, hence constructible, flat sheaf. -/
theorem boundedConstructibleFiniteTor_dualizingComplex (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [HasCompactification g] [HasInvertibleExponent Λ V] :
    DerivedCategory.boundedConstructibleFiniteTor Λ V
      (dualizingComplex (ModuleCat.{u + 1} Λ) g) := by
  obtain ⟨L, hL, hstalk, ⟨e⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ g d
  have : IsFiniteSheaf L := ⟨fun Ω _ _ s ↦ (ModuleCat.isFinitelyGenerated_iff _).2
    (Module.Finite.equiv (hstalk Ω s).some.toLinearEquiv.symm)⟩
  have : IsFiniteLocallyConstantSheaf L := { }
  have : IsConstructibleSheaf L := IsFiniteLocallyConstantSheaf.isConstructibleSheaf ‹_›
  have hflat : ObjectProperty.flat L := (flat_iff_forall_flat_sheafFiber_obj L).2 fun s ↦
    ObjectProperty.prop_of_iso _
      ((((pointSmallEtale s).uliftSheafFiberIso (ModuleCat.{u + 1} Λ)).app L ≪≫
        (hstalk _ s).some).symm)
      ((ModuleCat.flat_iff_flat _).2 (inferInstanceAs (Module.Flat Λ Λ)))
  have hL : DerivedCategory.boundedConstructibleFiniteTor Λ V
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) :=
    ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
      ⟨0, 0, _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat⟩⟩
  have hL₂ := hL.shift (2 * d : ℤ)
  exact ⟨(DerivedCategory.boundedConstructible _ V).prop_of_iso e.symm hL₂.1,
    (DerivedCategory.finiteTorAmplitude _ V).prop_of_iso e.symm hL₂.2⟩

/-- Blueprint `def-pur-section-invariant`: Section invariant

For `g : V ⟶ B` smooth of pure relative dimension `d` and admitting a compactification, and a
section `s` of `g`, the section invariant `𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` is an object of
`Pic(D^b_{ctf}(B, Λ))`: it is ⊗-invertible, and it lies in `D^b_{ctf}(B, Λ)` since `ω_g` does
and `Ls^*` preserves `D^b_{ctf}`. -/
theorem isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant
    (g : V ⟶ B) [SmoothOfRelativeDimension d g] [HasCompactification g]
    [HasInvertibleExponent Λ V] (s : B ⟶ V) :
    DerivedCategory.isInvertible Λ B (sectionInvariant Λ g s) ∧
      DerivedCategory.boundedConstructibleFiniteTor Λ B (sectionInvariant Λ g s) :=
  ⟨isInvertible_sectionInvariant Λ d g s,
    constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) s
      (boundedConstructibleFiniteTor_dualizingComplex Λ d g)⟩

/-- Blueprint `def-pur-dnc-section-family`: Deformation space of a closed section

For `g : V ⟶ B` smooth of pure relative dimension `d` and a closed section `s` of `g`, the family
object `F = Ls̃^* ω_{g̃}` of the deformation to the normal cone of `s` is an object of
`Pic(D^b_{ctf}(𝔸¹_B, Λ))`: it lies in `D^b_{ctf}(𝔸¹_B, Λ)` and is ⊗-invertible. -/
theorem isInvertible_and_boundedConstructibleFiniteTor_deformationFamilyObject
    [HasInvertibleExponent Λ B] (g : V ⟶ B) [SmoothOfRelativeDimension d g] (s : B ⟶ V)
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); B) (deformationFamilyObject Λ g s) ∧
      DerivedCategory.boundedConstructibleFiniteTor Λ 𝔸(ULift.{u} (Fin 1); B)
        (deformationFamilyObject Λ g s) :=
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : HasInvertibleExponent Λ s.ker.deformationSpace :=
    .of_hom (Scheme.Hom.deformationSpaceProj g s ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)
  isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant Λ d _ _

end Etale

end AlgebraicGeometry
