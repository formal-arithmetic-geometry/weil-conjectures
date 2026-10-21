/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.LocalizedFiniteModuleSpread
import WeilConjectures.Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible

/-!
# Picard group of a regular-local localization

Source: Stacks Project, More on Algebra, Tag 0AFZ (lemma-regular-local-Pic-zero),
read with Tags 0B8I and 00NX (blueprint: lem-trf-regular-local-pic-zero).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingTheory

open TensorProduct in
private theorem invertible_of_prime_localizations
    (R : Type u) [CommRing R] (L : Type v) [AddCommGroup L] [Module R L]
    [Module.Finite R L] [Module.Projective R L]
    (hL : ∀ (q : Ideal R) [q.IsPrime],
      Nonempty (LocalizedModule q.primeCompl L ≃ₗ[Localization.AtPrime q]
        Localization.AtPrime q)) : Module.Invertible R L := by
  let : Module.FinitePresentation R L := Module.finitePresentation_of_projective R L
  let dl (q : Ideal R) [q.IsMaximal] :
      Module.Dual R L →ₗ[R]
        Module.Dual (Localization.AtPrime q) (LocalizedModule q.primeCompl L) :=
    IsLocalizedModule.mapExtendScalars q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl L)
      (Algebra.linearMap R (Localization.AtPrime q)) (Localization.AtPrime q)
  let e (q : Ideal R) [q.IsMaximal] :=
    IsLocalization.moduleTensorEquiv q.primeCompl (Localization.AtPrime q)
      (Module.Dual (Localization.AtPrime q) (LocalizedModule q.primeCompl L))
      (LocalizedModule q.primeCompl L)
  refine ⟨bijective_of_isLocalized_maximal
    (fun q _ ↦ Module.Dual (Localization.AtPrime q) (LocalizedModule q.primeCompl L)
      ⊗[R] LocalizedModule q.primeCompl L)
    (fun q _ ↦ TensorProduct.map (dl q) (LocalizedModule.mkLinearMap q.primeCompl L))
    (fun q _ ↦ Localization.AtPrime q)
    (fun q _ ↦ Algebra.linearMap R (Localization.AtPrime q))
    (contractLeft R L) ?_⟩
  intro q hq
  let : Module.Invertible (Localization.AtPrime q) (LocalizedModule q.primeCompl L) :=
    Module.Invertible.congr (hL q).some.symm
  have hmap : IsLocalizedModule.map q.primeCompl
      (TensorProduct.map (dl q) (LocalizedModule.mkLinearMap q.primeCompl L))
      (Algebra.linearMap R (Localization.AtPrime q)) (contractLeft R L) =
      ((contractLeft (Localization.AtPrime q)
        (LocalizedModule q.primeCompl L)).restrictScalars R) ∘ₗ
        ((e q).symm.restrictScalars R).toLinearMap := by
    refine IsLocalizedModule.linearMap_ext q.primeCompl
      (TensorProduct.map (dl q) (LocalizedModule.mkLinearMap q.primeCompl L))
      (Algebra.linearMap R (Localization.AtPrime q)) ?_
    rw [IsLocalizedModule.map_comp]
    ext φ m
    exact (IsLocalizedModule.map_apply q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl L)
      (Algebra.linearMap R (Localization.AtPrime q)) φ m).symm
  rw [hmap]
  exact (Module.Invertible.bijective (R := Localization.AtPrime q)
    (M := LocalizedModule q.primeCompl L)).comp (e q).symm.bijective

/--
A finite projective module over a localization of a regular local ring is free of rank one
when all of its prime localizations are free of rank one, hence it is isomorphic to the ring.
Source: Stacks Project, More on Algebra, Tag 0AFZ, lemma-regular-local-Pic-zero, line 36780,
read with Tags 0B8I and 00NX (blueprint: lem-trf-regular-local-pic-zero).

Proof: The dual evaluation map is bijective after localization at every maximal ideal,
since the corresponding localization of `P` is isomorphic to the local ring. Localization
of Hom commutes with the finite presentation of `P`, and locality of bijectivity therefore
makes `P` invertible. Descend `P` to a finite `A`-module using
`lem-trf-localized-finite-module-spread`. The source theorem
`IsRegularLocalRing.exists_hasProjectiveDimensionLE` gives this module finite projective
dimension. The source localization theorem then makes its projective localization stably
free: it localizes a finite free resolution and splits the successive exact sequences.
Mathlib's `Module.free_of_isStablyFree_of_invertible` trivializes the invertible localization
by the determinant argument. Compose this equivalence with the descent equivalence.
This is the finite-resolution and determinant argument of Tag 0AFZ, expressed through
stable freeness rather than through a separate construction of `K₀`.
-/
theorem regularLocalPicardZero
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (f : A)
    (P : Type v) [AddCommGroup P] [Module (Localization.Away f) P]
    [Module.Finite (Localization.Away f) P]
    [Module.Projective (Localization.Away f) P]
    (hP : ∀ (q : Ideal (Localization.Away f)) [q.IsPrime],
      Nonempty (LocalizedModule q.primeCompl P ≃ₗ[Localization.AtPrime q]
        Localization.AtPrime q)) :
    Nonempty (P ≃ₗ[Localization.Away f] Localization.Away f) := by
  classical
  let : Module.Invertible (Localization.Away f) P :=
    invertible_of_prime_localizations (Localization.Away f) P hP
  obtain ⟨M, hM, ⟨e⟩⟩ := Module.exists_finite_localizationAway_model f P
  let : Module.Finite A M := hM
  obtain ⟨d, hd⟩ := IsRegularLocalRing.exists_hasProjectiveDimensionLE M
  let N := LocalizedModule (Submonoid.powers f) M
  let : Module.Invertible (Localization.Away f) N := Module.Invertible.congr e.symm
  let : Module.Projective (Localization.Away f) N := Module.Projective.of_equiv' e.symm
  let : Module.IsStablyFree (Localization.Away f) N :=
    Module.isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE
      (Submonoid.powers f) d M hd N (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
  let : Module.Free (Localization.Away f) N :=
    Module.free_of_isStablyFree_of_invertible (Localization.Away f) N
  obtain ⟨eN⟩ := Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free (Localization.Away f) N)
  exact ⟨e.symm.trans eN⟩

end RingTheory
