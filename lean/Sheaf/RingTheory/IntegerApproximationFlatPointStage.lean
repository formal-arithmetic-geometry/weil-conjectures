/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Basic
import Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Sheaf.RingTheory.ColimitEventuallyFlat

/-! # Descent of one flat point in a supplied integer approximation

Source: Stacks Project, Algebra, Tags 00RC, 00R1 and 00R6.
(blueprint: lem-weil-pbc-integer-approximation-flat-point-stage)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- A flat point of the limit of a supplied finite-type integer approximation occurs
at a stage. This asserts only stage flatness, without constructing a model or an open locus.

Source: Stacks Project, Algebra, Theorem Tag 00RC, first reduction paragraph,
using Lemmas Tags 00R1 and 00R6.
(blueprint: lem-weil-pbc-integer-approximation-flat-point-stage)

Proof:
Contract q along the stage maps to S and its inverse image along the maps to R.
The lifted limit rings are canonically isomorphic to R and S, and the lifted limit
module to M. Localize both ring diagrams and the module diagram at the contractions.
Compatibility of the cocones makes the contractions compatible with all transitions,
so the induced maps of local rings are local. Localization at a prime commutes with
filtered ring colimits (Tag 037D). For the module, lift numerators and denominators to
a common stage using the supplied colimits; an equality of fractions is witnessed by
a multiplier outside the prime, and its zero relation holds at a later stage. Hence
its localized colimit is M_q. Every stage ring is Noetherian: its base is finite type
over the integers, and its top is finite type over that base. Their prime localizations
are Noetherian local rings, and localization preserves finiteness of the stage modules.
Localize the supplied transition tensor isomorphisms. The ring comparison identifies
the localized later top ring as a further localization of the base change of the earlier
localized top ring. Tensor-localization compatibility identifies the localized module
base changes. Thus all hypotheses of Tag 00R6 hold. Since the localized limit base
is R at the inverse image of q, flatness over it follows from the given R-flatness:
flatness over a localization is equivalent to flatness over its base. Tag 00R6 gives
a flat localized stage module over the localized stage base. Restricting scalars
along that flat localization map makes it flat over the unlocalized stage base.
Transport through the canonical lift equivalences changes neither the contracted
prime nor these scalar actions. No openness theorem is used.
-/
theorem exists_flat_integer_approximation_stage_at_prime
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
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M') (ν.app i)) x) ∧
      -- (2) finiteness of the stages
      (∀ i, Algebra.FiniteType ℤ (A.obj i)) ∧
      (∀ i, letI := (η.app i).hom.toAlgebra; Algebra.FiniteType (A.obj i) (B.obj i)) ∧
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
    (q : PrimeSpectrum S)
    (hq : Module.Flat R (LocalizedModule q.asIdeal.primeCompl M)),
    ∃ i : Λ,
      letI : Algebra (A.obj i) (B.obj i) := (η.app i).hom.toAlgebra
      letI : Module (A.obj i) (D.obj i) := Module.compHom (D.obj i) (η.app i).hom
      letI : IsScalarTower (A.obj i) (B.obj i) (D.obj i) :=
        IsScalarTower.of_compHom _ _ _
      Module.Flat (A.obj i)
        (LocalizedModule
          (q.asIdeal.comap (ULift.ringEquiv.toRingHom.comp (κ.app i).hom)).primeCompl
          (D.obj i)) := by sorry

end Algebra
