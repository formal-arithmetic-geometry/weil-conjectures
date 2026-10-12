module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Algebra, Lemma 02HT, (1) implies (3); Definition 02HS.
(blueprint: lem-weil-pbc-smooth-at-prime-artinian-lifting-forward).

Proof in words, with step numbers inherited from the parent plan:
1. Principal opens form a basis of Spec A (def-weil-affine-spectrum). The localization
   map identifies Spec A_g with D(g) (lem-weil-pbc-principal-localization-open-immersion,
   def-weil-open-immersion). Smoothness is unchanged by that isomorphism and by restriction
   (lem-weil-pbc-smooth-restrict-open-subschemes,
   lem-weil-pbc-morphism-factors-through-open-subscheme). Thus an open smooth neighbourhood
   exists iff some g outside q makes R -> A_g smooth
   (lem-weil-pbc-smooth-ring-map-iff-smooth-affine, def-weil-pbc-smooth-ring-map).
2. The kernel I of a small extension is a simple module. Its annihilator is the unique
   maximal ideal m' of B', so m'I = 0. Since B is nonzero, I is proper and contained in m',
   hence I squared is zero. Surjectivity also gives preimage(m_B) = m' and B'/I = B.
3. Given a smooth A_g and a diagram, a(g) is a unit because its preimage maximal ideal is q.
   Factor a through A_g; square-zero lifting for this smooth algebra gives a map to B'
   (lem-weil-pbc-smooth-ring-map-square-zero-lifting). Compose with A -> A_g to get a'.
-/
theorem smooth_on_open_artinian_lifting_forward
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    (φ₀ : R →+* A) (hfinite : φ₀.FiniteType) (q : Ideal A) [q.IsPrime] :
    (∃ W : (Spec (CommRingCat.of A)).Opens,
      (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ W ∧
        Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom φ₀))) →
    (∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp φ₀ = φ.comp ρ → Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp φ₀ = ρ) := by
  sorry

end AlgebraicGeometry
