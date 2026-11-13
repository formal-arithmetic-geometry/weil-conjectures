/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Basic
import WeilConjectures.AlgebraicGeometry.SmoothAtPrimeArtinianLiftingForward
import WeilConjectures.AlgebraicGeometry.SmoothAtPrimeArtinianLiftingReverse

/-!
# Smoothness near a prime and lifting along Artinian small extensions

## References

* [Stacks Project, Tag 02HT](https://stacks.math.columbia.edu/tag/02HT)
* [Stacks Project, Tag 02HS](https://stacks.math.columbia.edu/tag/02HS)
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite type ring map over a Noetherian ring is smooth on an open neighbourhood of `q`
exactly when every compatible diagram at `q` lifts along every Artinian small extension.
The small-extension conditions are spelled out using module length, not square-zero alone.
-/
theorem smooth_on_open_iff_artinian_lifting
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    (φ₀ : R →+* A) (hfinite : φ₀.FiniteType) (q : Ideal A) [q.IsPrime] :
    (∃ W : (Spec (CommRingCat.of A)).Opens,
      (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ W ∧
        Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom φ₀))) ↔
    (∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp φ₀ = φ.comp ρ → Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp φ₀ = ρ) := by
  constructor
  · exact smooth_on_open_artinian_lifting_forward φ₀ hfinite q
  · exact artinian_lifting_smooth_on_open_reverse φ₀ hfinite q

end AlgebraicGeometry
