/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
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

/-! # A flat point in a supplied finite-type approximation

Source: Stacks Project, Tag 02JO (1), proof first paragraph and start of second paragraph.
(blueprint: lem-pc-finite-type-approximation-flat-point)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

set_option autoImplicit false

namespace Algebra

/-- At every prime of the limit, a contracted stage module is flat over its base.

Source: Stacks Project, Algebra, Tag 02JO (1), first paragraph, and Tag 00R6.
(blueprint: lem-pc-finite-type-approximation-flat-point)

Proof:
Contract the given prime q of S to B_i and then to A_i. Localize A_i, B_i and D_i
at these primes. Naturality of the coprojections ensures that all transition ring
maps are local. Since A_i is finite type over the integers and B_i is finite type
over A_i, both rings are Noetherian, as are their localizations; the localized
modules are finite. Localization commutes with the two ring colimits. For the
module colimit, write a fraction with numerator from D_i and denominator from B_j,
then pass to a common upper stage. If a fraction vanishes, a multiplier outside q
kills its numerator; lift the multiplier and descend the resulting zero equality
using the supplied group colimit and semilinearity. Thus the localized module
colimit is M_q with its canonical actions. Localizing the supplied transition
ring tensor equivalences gives the localization hypothesis of Tag 00R6; localizing
the module tensor equivalences gives its module base-change hypothesis. The limit
module M_q is flat over the contracted localization of R since M is R-flat
(Tag 00HT). Apply RingTheory.exists_flat_stage to these localized diagrams.
Finally use flatness over a localization if and only if flatness over the original
base to return flatness over A_i. No open subset or persistence claim is used.
-/
theorem exists_flat_finiteType_approximation_point
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
    ∀ q : PrimeSpectrum S, ∃ i,
      letI : Module (A.obj i)
          (LocalizedModule (PrimeSpectrum.comap (κ.app i).hom q).asIdeal.primeCompl
            (D.obj i)) := Module.compHom _ (η.app i).hom
      Module.Flat (A.obj i)
        (LocalizedModule (PrimeSpectrum.comap (κ.app i).hom q).asIdeal.primeCompl
          (D.obj i)) := by sorry

end Algebra
