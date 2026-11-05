/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Smooth.Fiber
public import WeilConjectures.Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Weakly étale algebras

-/

@[expose] public section

universe u u₁ u₂ u₃ u₄ u₅

open TensorProduct

open CategoryTheory Limits

-- `(S ⊗[R] S) (T ⊗[R] A) S (T ⊗[S] A)`

namespace Algebra

section

end

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The multiplication map `S ⊗[R] S → S` is flat iff the kernel of the multiplication map
(i.e. `KaehlerDifferential.ideal R S`) is a pure ideal in `S ⊗[R] S`. -/
lemma flat_lmul'_iff_kaehlerDifferential_ideal_pure :
    (TensorProduct.lmul' (S := S) R).toRingHom.Flat ↔ (KaehlerDifferential.ideal R S).Pure :=
  RingHom.flat_iff_pure_ker_of_surjective (fun x ↦ ⟨1 ⊗ₜ x, by simp⟩)

lemma FormallyUnramified.of_flat_lmul' (h : (TensorProduct.lmul' (S := S) R).Flat) :
    FormallyUnramified R S := by
  have hp : (KaehlerDifferential.ideal R S).Pure :=
    flat_lmul'_iff_kaehlerDifferential_ideal_pure.mp h
  rw [formallyUnramified_iff]
  exact (Ideal.cotangent_subsingleton_iff _).mpr (Ideal.isIdempotentElem_of_pure _)

namespace WeaklyEtale

instance (priority := low) [WeaklyEtale R S] : FormallyUnramified R S :=
  .of_flat_lmul' (flat_lmul' R S)

instance (priority := low) [WeaklyEtale R S] [FinitePresentation R S] : Etale R S :=
  .of_formallyUnramified_of_flat

end WeaklyEtale

end Algebra

namespace RingHom

@[algebraize]
def WeaklyEtale {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.WeaklyEtale R S

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma weaklyEtale_algebraMap_iff [Algebra R S] :
    (algebraMap R S).WeaklyEtale ↔ Algebra.WeaklyEtale R S := by
  rw [WeaklyEtale, toAlgebra_algebraMap]

/-- A weakly étale ring map is formally unramified. -/
lemma WeaklyEtale.formallyUnramified {f : R →+* S} (hf : f.WeaklyEtale) :
    f.FormallyUnramified := by
  algebraize [f]
  have : Algebra.WeaklyEtale R S := hf
  exact (inferInstance : Algebra.FormallyUnramified R S)

variable {f} in
lemma WeaklyEtale.comp {T : Type*} [CommRing T] {g : S →+* T} (hf : f.WeaklyEtale)
    (hg : g.WeaklyEtale) :
    (g.comp f).WeaklyEtale := by
  algebraize [f, g, g.comp f]
  exact .trans _ S _

end RingHom
