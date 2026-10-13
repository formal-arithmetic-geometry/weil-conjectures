/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology

import Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime
import Sheaf.RingTheory.ColimitEventuallyFlat
import Sheaf.RingTheory.FlatModuleAtPrime
import Sheaf.RingTheory.OpenFlatLocus

/-! # Flat loci in a finite-type approximation

Source: Stacks Project, Tag 02JO (1), proof first paragraph and start of second paragraph.
(blueprint: lem-pc-finite-type-approximation-flat-loci)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra

/-- Flat loci in a supplied approximation are open, persistent, and cover the limit.

Source: Stacks Project, Tag 02JO (1), proof first paragraph and start of second paragraph.
(blueprint: lem-pc-finite-type-approximation-flat-loci)

Proof:
The finite-type integer base rings and their finite-type top rings are Noetherian.
The top algebras and their finite stage modules are therefore finitely presented.
For each prime q of S, contract q along the compatible
maps to B_i and A_i and localize all three diagrams. Localization commutes with
the ring colimits; fraction representatives and eventual vanishing give the
module colimit. The canonical transition tensor isomorphisms localize to the
base-change/localization maps in Tag 00R6. The localized limit module is flat
over the contracted local base since M is R-flat. Tag 00R6 therefore gives a
stage flat at the contraction of q over the corresponding localized base. Flatness
of a module over a localization is equivalent to flatness over the base, so this
is a point of the flat locus over A_i. Define U_i to be that full flat locus;
Tag 00RC makes it open. For i <= j and a prime q_j contracting to q_i in U_i,
the canonical ring and module tensor comparisons identify the later localized
module with a further localization of A_j tensor_(A_i) (D_i localized at q_i).
Base change preserves flatness over A_j, and localization of the top-module factor
preserves it. Thus the inverse image of U_i is contained in U_j. The contracted
primes found above give the required pointwise cover of the limit spectrum.
No compactness or unit-relation descent is performed in this theorem.
-/
theorem exists_flat_finiteType_approximation_loci
    (R S : Type u) (M : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (A B : Λ ⥤ CommRingCat.{u}) (η : A ⟶ B)
      (π : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
      (κ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
      (D : Λ ⥤ AddCommGrpCat.{v})
      (ν : D ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
    [∀ i : Λ, Module (B.obj i) (D.obj i)]
    (hmodel :
      -- (1) the three colimits, compatible with `R → S` and the module actions
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of R) π)) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of S) κ)) ∧
      Nonempty (IsColimit (Cocone.mk (AddCommGrpCat.of M) ν)) ∧
      (∀ i, η.app i ≫ κ.app i = π.app i ≫ CommRingCat.ofHom (algebraMap R S)) ∧
      (∀ (i j : Λ) (h : i ≤ j) (y : B.obj i) (x : D.obj i),
        (D.map (homOfLE h)).hom (y • x) =
          (B.map (homOfLE h)).hom y • (D.map (homOfLE h)).hom x) ∧
      (∀ i (y : B.obj i) (x : D.obj i),
        (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) (y • x) =
          (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) y •
            (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x) ∧
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
            e (y ⊗ₜ[B.obj i] x) = y • (D.map (homOfLE h)).hom x) ∧
      -- (4) base changes to the limit
      (∀ i,
        letI := (η.app i).hom.toAlgebra
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of R) (π.app i)).toAlgebra
        ∃ e : B.obj i ⊗[A.obj i] R ≃+* S,
          ∀ (x : B.obj i) (y : R),
            e (x ⊗ₜ[A.obj i] y) =
              (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)) x * algebraMap R S y) ∧
      (∀ i,
        letI := (@CommRingCat.Hom.hom _ (CommRingCat.of S) (κ.app i)).toAlgebra
        ∃ e : S ⊗[B.obj i] D.obj i ≃ₗ[S] M,
          ∀ (y : S) (x : D.obj i),
            e (y ⊗ₜ[B.obj i] x) = y • (@AddCommGrpCat.Hom.hom _ (AddCommGrpCat.of M) (ν.app i)) x))
    (hflat : letI : Module R M := Module.compHom M (algebraMap R S)
      Module.Flat R M) :
    ∃ U : (i : Λ) → Set (PrimeSpectrum (B.obj i)),
      (∀ i, IsOpen (U i)) ∧
      (∀ i (q : PrimeSpectrum (B.obj i)), q ∈ U i →
        letI : Module (A.obj i) (LocalizedModule q.asIdeal.primeCompl (D.obj i)) :=
          Module.compHom _ (η.app i).hom
        Module.Flat (A.obj i) (LocalizedModule q.asIdeal.primeCompl (D.obj i))) ∧
      (∀ (i j : Λ) (h : i ≤ j),
        PrimeSpectrum.comap (B.map (homOfLE h)).hom ⁻¹' U i ⊆ U j) ∧
      (∀ q : PrimeSpectrum S, ∃ i, PrimeSpectrum.comap (κ.app i).hom q ∈ U i) := by sorry

end Algebra
