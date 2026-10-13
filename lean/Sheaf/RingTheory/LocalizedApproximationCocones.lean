/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Localization.Defs

/-! # Cocones for prime-localized approximation diagrams

Source: Stacks Project, Algebra, Tag 00RC, first reduction, and Tag 037D.
(blueprint: lem-weil-pbc-localized-approximation-cocones)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Construct the localized ring and module cocones, without finiteness or tensor hypotheses.

Source: Stacks Project, Algebra, Tag 00RC, first reduction paragraph; Tag 037D.
(blueprint: lem-weil-pbc-localized-approximation-cocones)

Proof:
1. Contract q along each top-stage cocone map followed by ULift.down and then along
   the base-to-top map. Cocone naturality and the commuting squares identify the
   contractions along transitions. Take Localization.AtPrime of both stage rings
   and LocalizedModule of each stage module. The transition maps send x/s to
   f(x)/f(s). They are well defined because a denominator outside the earlier prime
   maps outside the later prime; semilinearity carries the fraction relation to the
   fraction relation. Uniqueness on numerator-one images proves the functor laws,
   the ring squares, and all displayed naturality identities for the maps ρA, ρB, ζ.
2. Localize the two supplied ring colimit cocones using Tag 037D. Transport their
   colimit comparisons through the canonical ULift ring equivalences. For modules,
   lift a numerator and denominator to a common stage. Equality of fractions has
   a multiplier outside q; lift that multiplier and descend the zero relation to
   a later stage using eventual equality in the supplied group colimit. This gives
   the localized group colimit and its scalar action by multiplication of fractions.
   The cocone maps are semilinear for this action. The commuting ring squares induce ψ.
3. Prime localizations are local. A fraction is a nonunit precisely when its numerator
   belongs to the contracted prime; this criterion proves locality of every induced
   ring map.
4. The base limit is R at q contracted to R. The module limit is M at q. The fraction
   comparisons preserve the restricted R-action, giving the limit linear equivalence.
   At each stage the same calculation gives the A_i-linear module equivalence and
   base localization witness. The numerator-one linear map ℓ is IsLocalizedModule:
   denominator scalars are invertible, every fraction has a numerator and denominator,
   and an equality of numerator-one images is killed by a denominator.
No Noetherianity, finiteness, or transition tensor equivalence is needed here. -/
theorem exists_localized_approximation_cocones
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
    (hmodel :
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
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) x))
    (q : PrimeSpectrum S),
    ∃ (Aₗ Bₗ : Λ ⥤ CommRingCat.{max u v w})
      (Dₗ : Λ ⥤ AddCommGrpCat.{max u v w}),
    ∃ hcA : HasColimit Aₗ, letI := hcA
    ∃ hcB : HasColimit Bₗ, letI := hcB
    ∃ hcD : HasColimit Dₗ, letI := hcD
    ∃ hlocalA : ∀ i, IsLocalRing (Aₗ.obj i), letI := hlocalA
    ∃ hlocalB : ∀ i, IsLocalRing (Bₗ.obj i), letI := hlocalB
    ∃ hmodule : ∀ i, Module (Bₗ.obj i) (Dₗ.obj i), letI := hmodule
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
          (D.obj i) ≃ₗ[A.obj i] Dₗ.obj i)) ∧
      (∃ (ρA : ∀ i, A.obj i →+* Aₗ.obj i)
        (ρB : ∀ i, B.obj i →+* Bₗ.obj i)
        (ζ : ∀ i, D.obj i →+ Dₗ.obj i),
        (∀ i, letI := (ρA i).toAlgebra
          IsLocalization
            (q.asIdeal.comap ((ULift.ringEquiv.toRingHom.comp (κ.app i).hom).comp
              (η.app i).hom)).primeCompl (Aₗ.obj i)) ∧
        (∀ i, letI := (ρB i).toAlgebra
          IsLocalization
            (q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)).primeCompl
            (Bₗ.obj i)) ∧
        (∀ i, (ρB i).comp (η.app i).hom = (φ i).comp (ρA i)) ∧
        (∀ (i j : Λ) (f : i ⟶ j),
          (ρA j).comp (A.map f).hom = (Aₗ.map f).hom.comp (ρA i)) ∧
        (∀ (i j : Λ) (f : i ⟶ j),
          (ρB j).comp (B.map f).hom = (Bₗ.map f).hom.comp (ρB i)) ∧
        (∀ (i j : Λ) (f : i ⟶ j) (x : D.obj i),
          ζ j ((D.map f).hom x) = (Dₗ.map f).hom (ζ i x)) ∧
        (∀ i (b : B.obj i) (x : D.obj i), ζ i (b • x) = ρB i b • ζ i x) ∧
        (∀ i, letI := Module.compHom (Dₗ.obj i) (ρB i)
          ∃ ℓ : D.obj i →ₗ[B.obj i] Dₗ.obj i,
            (∀ x, ℓ x = ζ i x) ∧
            IsLocalizedModule
              (q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)).primeCompl
              ℓ)) := by sorry

end Algebra
