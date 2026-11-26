/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PairHenselization
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.PairHenselizationFiberSeparable
import WeilConjectures.RingTheory.PairHenselizationFiberProjection
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localization description of a fibre of a pair henselization

For a prime `q` of a Noetherian pair henselization over `A` with contraction `p`, the fibre of
`q` over `C` is a localization of the fibre of `p` over `C`.

## Implementation details

The fibre over `p` is the finite product of the residue fields of the primes over `p`
(Tag 0AH1). Tensoring with `C`, the projection to the `q` factor is the localization at the
idempotent which is one at `q` and zero at the other factors.

## References

* [Stacks, Tag 0AH1]
* [Stacks, Tag 0AH3]
* [Stacks, Tag 0A02]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

private theorem localization_of_idempotent_projection
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (e : R) (he : IsIdempotentElem e) (hef : f e = 1)
    (hsurj : Function.Surjective f) (hker : ∀ x, f x = 0 → e * x = 0) :
    let _ := f.toAlgebra
    IsLocalization (Submonoid.powers e) S := by
  let _ := f.toAlgebra
  apply IsLocalization.away_of_isIdempotentElem_of_mul he ?_ hsurj
  intro x y
  change f x = f y ↔ e * x = e * y
  constructor
  · intro hxy
    have h := hker (x - y) (by simp only [map_sub, hxy, sub_self])
    exact sub_eq_zero.mp (by simpa only [mul_sub] using h)
  · intro hxy
    have h := congrArg f hxy
    simpa only [map_mul, hef, one_mul] using h

/-- The residue extension at a prime `q` of a Noetherian pair henselization is separable, and
for any map to `C` the fibre of `q` is a localization of the fibre of the contracted prime. -/
theorem pair_henselization_fiber_localization
    (A : Type u) [CommRing A] (I : Ideal A)
    (c : Cocone (ObjectProperty.ι
      (fun D : Under (CommRingCat.of A) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map D.hom) ∧
          Function.Bijective (Ideal.quotientMap (I.map D.hom.hom) D.hom.hom
            (Ideal.le_comap_map)))))
    (hc : IsColimit c) [IsNoetherianRing c.pt.right]
    (C : Type u) [CommRing C] (g : c.pt.right →+* C)
    (q : Ideal c.pt.right) [q.IsPrime] :
    letI := c.pt.hom.hom.toAlgebra
    letI := g.toAlgebra
    letI := (g.comp c.pt.hom.hom).toAlgebra
    letI : IsScalarTower A c.pt.right C :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let p := q.comap c.pt.hom.hom
    ∀ (ρ : p.ResidueField →ₐ[A] q.ResidueField),
      ρ = Ideal.ResidueField.mapₐ p q (Algebra.ofId A c.pt.right) rfl →
    ∀ (φ : p.Fiber C →+* q.Fiber C),
      (∀ (x : p.ResidueField) (y : C),
        φ (TensorProduct.tmul A x y) = TensorProduct.tmul c.pt.right (ρ x) y) →
    letI := ρ.toRingHom.toAlgebra
    letI := φ.toAlgebra
    Algebra.IsSeparable p.ResidueField q.ResidueField ∧
      ∃ M : Submonoid (p.Fiber C), IsLocalization M (q.Fiber C) := by
  dsimp
  let _ := c.pt.hom.hom.toAlgebra
  let _ := g.toAlgebra
  let _ := (g.comp c.pt.hom.hom).toAlgebra
  let _ : IsScalarTower A c.pt.right C :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro ρ hρ φ hφ
  let _ := ρ.toRingHom.toAlgebra
  let _ := φ.toAlgebra
  refine ⟨pair_henselization_fiber_separable A I c hc q ρ hρ, ?_⟩
  obtain ⟨e, he, heφ, hsurj, hker⟩ :=
    pair_henselization_fiber_projection A I c hc C g q ρ hρ φ hφ
  exact ⟨Submonoid.powers e,
    localization_of_idempotent_projection φ e he heφ hsurj hker⟩

end RingTheory
