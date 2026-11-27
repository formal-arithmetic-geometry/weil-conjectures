/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import WeilConjectures.RingTheory.LocalizedApproximationCocones
import WeilConjectures.RingTheory.LocalizedApproximationTransitions
import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.Defs

/-! # Localized diagrams of a supplied Noetherian approximation

Localizing a Noetherian approximation of a module over a local homomorphism at the contracted
primes gives a directed system of Noetherian local rings and finite modules with the localized
colimits.

## Implementation details

Localized colimits are obtained by applying `filteredColimitLocalizationAtPrime` to the ring
diagrams; for modules, a numerator and a denominator are lifted to a common stage, and equality
of fractions is descended using eventual equality in the original colimit.

## References

* [Stacks, Tag 00RC] (first reduction paragraph)
* [Stacks, Tag 00QX]
* [Stacks, Tag 00R1]
* [Stacks, Tag 00R6]
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Localization of a supplied Noetherian approximation at the primes contracted from `q`
produces the local diagrams used in the stage-flatness criterion: localized colimits identified
with `R_p` and `M_q`, Noetherian local stages with finite localized modules, and localized
transition base changes. No flatness of the limit is assumed, and no flat stage is selected. -/
theorem exists_localized_noetherian_approximation
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    let R' := ULift.{max u v w} R
    let S' := ULift.{max u v w} S
    let M' := ULift.{max u v w} M
    letI : Algebra R' S' := ULift.algebra' R S'
    ∀
    {Λ : Type (max u v w)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A B : Λ ⥤ CommRingCat.{max u v w}) (η : A ⟶ B)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R'))
      (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S'))
      (D : Λ ⥤ AddCommGrpCat.{max u v w})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M'))
    [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (_hmodel :
      -- (1) the three colimits, compatible with `R' → S'` and the module actions
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R') π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S') κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M') ν)) ∧
      (∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R' S')) ∧
      (∀ (i j : Λ) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : B.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S') (κ.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) x) ∧
      -- (2) finiteness of the stages
      (∀ i, IsNoetherianRing (A.obj i)) ∧
      (∀ i, IsNoetherianRing (B.obj i)) ∧
      (∀ i, Module.Finite (B.obj i) (D.obj i)) ∧
      -- (3) transition base changes
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (η.app i).hom.toAlgebra
        letI := (A.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj i ⊗[A.obj i] A.obj j ≃+* B.obj j,
          ∀ (x : B.obj i) (y : A.obj j),
            e (x ⊗ₜ[A.obj i] y) = (B.map (homOfLE h)).hom x * (η.app j).hom y) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        letI := (B.map (homOfLE h)).hom.toAlgebra
        ∃ e : B.obj j ⊗[B.obj i] D.obj i ≃ₗ[B.obj j] D.obj j,
          ∀ (y : B.obj j) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x))
    (q : PrimeSpectrum S),
    ∃ (Aₗ Bₗ : Λ ⥤ CommRingCat.{max u v w})
      (Dₗ : Λ ⥤ AddCommGrpCat.{max u v w}),
    ∃ hcA : HasColimit Aₗ, letI := hcA
    ∃ hcB : HasColimit Bₗ, letI := hcB
    ∃ hcD : HasColimit Dₗ, letI := hcD
    ∃ hlocalA : ∀ i, IsLocalRing (Aₗ.obj i), letI := hlocalA
    ∃ hlocalB : ∀ i, IsLocalRing (Bₗ.obj i), letI := hlocalB
    ∃ hnoethA : ∀ i, IsNoetherianRing (Aₗ.obj i), letI := hnoethA
    ∃ hnoethB : ∀ i, IsNoetherianRing (Bₗ.obj i), letI := hnoethB
    ∃ hmodule : ∀ i, Module (Bₗ.obj i) (Dₗ.obj i), letI := hmodule
    ∃ hfinite : ∀ i, Module.Finite (Bₗ.obj i) (Dₗ.obj i), letI := hfinite
    ∃ hmoduleLimit : Module (colimit Bₗ : CommRingCat.{max u v w})
        (colimit Dₗ : AddCommGrpCat.{max u v w}), letI := hmoduleLimit
    ∃ (φ : ∀ i, Aₗ.obj i →+* Bₗ.obj i)
      (ψ : (colimit Aₗ : CommRingCat.{max u v w}) →+*
        (colimit Bₗ : CommRingCat.{max u v w})),
      (∀ i, IsLocalHom (φ i)) ∧
      (∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (Aₗ.map f).hom) ∧
      (∀ (i j : Λ) (f : i ⟶ j), IsLocalHom (Bₗ.map f).hom) ∧
      (∀ (i j : Λ) (f : i ⟶ j),
        (Bₗ.map f).hom.comp (φ i) = (φ j).comp (Aₗ.map f).hom) ∧
      (∀ (i j : Λ) (f : i ⟶ j) (b : Bₗ.obj i) (x : Dₗ.obj i),
        (Dₗ.map f).hom (b • x) = (Bₗ.map f).hom b • (Dₗ.map f).hom x) ∧
      (∀ i, ψ.comp (colimit.ι Aₗ i).hom = (colimit.ι Bₗ i).hom.comp (φ i)) ∧
      (∀ (i : Λ) (b : Bₗ.obj i) (x : Dₗ.obj i),
        (colimit.ι Dₗ i).hom (b • x) =
          (colimit.ι Bₗ i).hom b • (colimit.ι Dₗ i).hom x) ∧
      (∀ (i j : Λ) (f : i ⟶ j),
        letI := (φ i).toAlgebra
        letI := (Aₗ.map f).hom.toAlgebra
        ∃ (t : Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j →+* Bₗ.obj j)
          (W : Submonoid (Bₗ.obj i ⊗[Aₗ.obj i] Aₗ.obj j)),
          (∀ (b : Bₗ.obj i) (a : Aₗ.obj j),
            t (b ⊗ₜ[Aₗ.obj i] a) = (Bₗ.map f).hom b * φ j a) ∧
          (letI := t.toAlgebra; IsLocalization W (Bₗ.obj j))) ∧
      (∀ (i j : Λ) (f : i ⟶ j),
        letI := (Bₗ.map f).hom.toAlgebra
        ∃ e : Bₗ.obj j ⊗[Bₗ.obj i] Dₗ.obj i ≃ₗ[Bₗ.obj j] Dₗ.obj j,
          ∀ (b : Bₗ.obj j) (x : Dₗ.obj i),
            e (b ⊗ₜ[Bₗ.obj i] x) = b • (Dₗ.map f).hom x) ∧
      (∃ ρ : R →+* (colimit Aₗ : CommRingCat.{max u v w}),
        letI := ρ.toAlgebra
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ψ
        letI := Module.compHom (colimit Dₗ : AddCommGrpCat.{max u v w}) ρ
        IsLocalization (q.asIdeal.comap (algebraMap R S)).primeCompl
          (colimit Aₗ : CommRingCat.{max u v w}) ∧
        Nonempty (LocalizedModule q.asIdeal.primeCompl M ≃ₗ[R]
          (colimit Dₗ : AddCommGrpCat.{max u v w}))) ∧
      (∀ i, ∃ ρ : A.obj i →+* Aₗ.obj i,
        letI := (φ i).toAlgebra
        letI := Module.compHom (Dₗ.obj i) (φ i)
        letI := ρ.toAlgebra
        letI := Module.compHom (Dₗ.obj i) ρ
        letI : Algebra (A.obj i) (B.obj i) := (η.app i).hom.toAlgebra
        letI : Module (A.obj i) (D.obj i) := Module.compHom (D.obj i) (η.app i).hom
        letI : IsScalarTower (A.obj i) (B.obj i) (D.obj i) :=
          IsScalarTower.of_compHom _ _ _
        IsLocalization
          (q.asIdeal.comap ((ULift.ringEquiv.toRingHom.comp (κ.app i).hom).comp
            (η.app i).hom)).primeCompl (Aₗ.obj i) ∧
        Nonempty (LocalizedModule
          (q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)).primeCompl
          (D.obj i) ≃ₗ[A.obj i] Dₗ.obj i)) := by
  classical
  dsimp only
  intro Λ _ _ _ A B η π κ D ν _ hmodel q
  rcases hmodel with ⟨hcR, hcS, hcM, hcompat, hD, hν, hnoethA, hnoethB,
    hfiniteOriginal, htB, htD⟩
  obtain ⟨Aₗ, Bₗ, Dₗ, hcA, hcB, hcD, hlocalA, hlocalB, hmodule,
    hmoduleLimit, φ, ψ, hφ, hA, hB, hcomm,
    hscalar, hψ, hlimitScalar, hlimit, hstage,
    ρA, ρB, ζ, hρA, hρB, hη, hρAnat, hρBnat, hζ, hζscalar, hℓ⟩ :=
    exists_localized_approximation_cocones R S M A B η π κ D ν
      ⟨hcR, hcS, hcM, hcompat, hD, hν⟩ q
  let := hcA
  let := hcB
  let := hcD
  let := hlocalA
  let := hlocalB
  let := hmodule
  let := hmoduleLimit
  let qᵢ : ∀ i, Ideal (B.obj i) := fun i ↦
    q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)
  have hprime : ∀ i, (qᵢ i).IsPrime := fun i ↦ Ideal.IsPrime.comap _
  have hq (i j : Λ) (f : i ⟶ j) : Ideal.comap (B.map f).hom (qᵢ j) = qᵢ i := by
    dsimp only [qᵢ]
    rw [Ideal.comap_comap]
    congr 1
    rw [RingHom.comp_assoc]
    congr 1
    change (B.map f ≫ κ.app j).hom = (κ.app i).hom
    rw [κ.naturality]
    rfl
  have hρA' : ∀ i, letI := (ρA i).toAlgebra
      IsLocalization ((qᵢ i).comap (η.app i).hom).primeCompl (Aₗ.obj i) := by
    intro i
    simpa only [qᵢ, Ideal.comap_comap] using hρA i
  have hnoetherianA : ∀ i, IsNoetherianRing (Aₗ.obj i) := by
    intro i
    let := (ρA i).toAlgebra
    let := hρA' i
    exact IsLocalization.isNoetherianRing
      ((qᵢ i).comap (η.app i).hom).primeCompl (Aₗ.obj i) (hnoethA i)
  have hnoetherianB : ∀ i, IsNoetherianRing (Bₗ.obj i) := by
    intro i
    let := (ρB i).toAlgebra
    let := hρB i
    exact IsLocalization.isNoetherianRing (qᵢ i).primeCompl (Bₗ.obj i) (hnoethB i)
  have hfinite : ∀ i, Module.Finite (Bₗ.obj i) (Dₗ.obj i) := by
    intro i
    let := (ρB i).toAlgebra
    let := Module.compHom (Dₗ.obj i) (ρB i)
    have : IsScalarTower (B.obj i) (Bₗ.obj i) (Dₗ.obj i) :=
      IsScalarTower.of_compHom _ _ _
    let := hρB i
    obtain ⟨ℓ, _, hloc⟩ := hℓ i
    let := hloc
    let := hfiniteOriginal i
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B.obj i) (M := D.obj i)
    refine ⟨Submodule.fg_def.mpr ?_⟩
    exact ⟨ℓ '' (s : Set (D.obj i)), s.finite_toSet.image ℓ,
      span_eq_top_of_isLocalizedModule (Bₗ.obj i) (qᵢ i).primeCompl ℓ hs⟩
  let := hnoetherianA
  let := hnoetherianB
  let := hfinite
  obtain ⟨htransitionRing, htransitionModule⟩ :=
    localized_approximation_transition_base_change A B η D qᵢ hq Aₗ Bₗ Dₗ φ
      ρA ρB ζ hρA' hρB hη hρAnat hρBnat hζ hscalar hℓ htB htD
  exact ⟨Aₗ, Bₗ, Dₗ, hcA, hcB, hcD, hlocalA, hlocalB, hnoetherianA,
    hnoetherianB, hmodule, hfinite, hmoduleLimit, φ, ψ, hφ, hA, hB, hcomm,
    hscalar, hψ, hlimitScalar, htransitionRing, htransitionModule, hlimit, hstage⟩


end Algebra
