/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange
import Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Degree subtraction for the complement of an affine étale diagonal

Source: Stacks Project, Tag 03XW, proof of lemma-neighbourhood-scheme, second and
third paragraphs (blueprint: lem-a1-affine-etale-diagonal-complement-degree).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- The diagonal of an étale map of affine schemes is clopen, and its affine complement
has fibre degree at most one less. The fibre decomposition is specified by its two
canonical inclusions; the ring equivalence is restriction to these pieces, identifying
the diagonal piece with the base field by `ΓSpecIso`. Thus it is an equivalence of
algebras over that field, with the structures induced by the second projections.

Source: Stacks Project, Tag 03XW, proof, second and third paragraphs
(blueprint: lem-a1-affine-etale-diagonal-complement-degree).

Proof:
1. Write the affines as Spec A and Spec B. Their self-product is Spec (B ⊗[A] B)
   by lem-weil-pbc-fibre-product-affine-spectra. The diagonal is closed because a map
   from an affine scheme to an affine scheme is separated
   (lem-weil-pbc-affine-source-morphism-separated, def-weil-proper-morphism), and open
   because the étale map is unramified (def-weil-etale-morphism,
   def-weil-unramified-morphism). Its second projection is the identity.
2. The clopen diagonal image is D(e) for an idempotent e
   (lem-weil-pbc-spec-clopen-idempotent). The complementary open is D(1-e), hence affine
   by lem-weil-pbc-principal-localization-open-immersion. Its localization is R/(e),
   since e(1-e)=0, so its inclusion is also closed (def-weil-closed-immersion).
3. The second projection is étale and has fibre degrees bounded by n, by base change
   (lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-fibre-degree-base-change).
   Restricting it to the complementary open stays étale (lem-a1-etale-open-restriction).
4. Sheaf gluing on the disjoint open cover identifies R with B × C₀, as B-algebras.
   Pull back to any Spec K → T'. The diagonal piece becomes Spec K, and the other
   piece is the fibre of the restricted map (def-pc-fibre-product). On coordinate
   algebras this is (B × C₀) ⊗[B] K ≅ K × (C₀ ⊗[B] K), by the maps on pure tensors
   (b,c) ⊗ k ↦ (u(b)k,c ⊗ k), with inverse given separately on the two summands.
   This is precisely the stated restriction equivalence on global sections.
5. By lem-weil-pbc-fibre-degree-bound-field-points this product algebra is finite
   dimensional of dimension at most n. Projection makes C finite dimensional; a basis
   of C together with (1,0) gives dimension 1 + dim C, so dim C ≤ n-1. Its spectrum is
   finite over K (def-weil-finite-integral-morphism). Residue-field points give
   def-weil-pbc-fibre-degree-bound for the complement.
6. When n=1 every complementary residue fibre has zero coordinate algebra, hence is
   empty. Any point of the complement would induce a point in such a fibre, so the
   complement is empty. The diagonal is surjective, making a universally injective
   (def-weil-radicial-morphism). Apply lem-weil-pbc-radicial-etale-open. -/
theorem affine_etale_diagonal_complement_degree {S T T' : Scheme.{u}}
    [IsAffine T] [IsAffine T'] (t : T ⟶ S) (t' : T' ⟶ S)
    (a : Over.mk t' ⟶ Over.mk t) [Etale a.left] (n : ℕ) (hn : 1 ≤ n)
    (ha : BoundsFiberDegrees a.left n) :
    IsOpenImmersion (pullback.diagonal a.left) ∧
    IsClosedImmersion (pullback.diagonal a.left) ∧
    ∃ U : (pullback a.left a.left).Opens,
      (U : Set (pullback a.left a.left : Scheme.{u})) = (Set.range (pullback.diagonal a.left))ᶜ ∧
      IsClosedImmersion U.ι ∧ IsAffine U.toScheme ∧
      Etale (U.ι ≫ pullback.snd a.left a.left) ∧
      BoundsFiberDegrees (U.ι ≫ pullback.snd a.left a.left) (n - 1) ∧
      (∀ (K : Type u) [Field K] (g : Spec (CommRingCat.of K) ⟶ T'),
        IsFinite (pullback.snd (U.ι ≫ pullback.snd a.left a.left) g) ∧
        (pullback.snd (U.ι ≫ pullback.snd a.left a.left) g).finrankΓ ≤ n - 1 ∧
        ∃ (s : Spec (CommRingCat.of K) ⟶ pullback (pullback.snd a.left a.left) g)
          (j : pullback (U.ι ≫ pullback.snd a.left a.left) g ⟶
            pullback (pullback.snd a.left a.left) g),
          s ≫ pullback.fst (pullback.snd a.left a.left) g = g ≫ pullback.diagonal a.left ∧
          s ≫ pullback.snd (pullback.snd a.left a.left) g = 𝟙 _ ∧
          j ≫ pullback.fst (pullback.snd a.left a.left) g =
            pullback.fst (U.ι ≫ pullback.snd a.left a.left) g ≫ U.ι ∧
          j ≫ pullback.snd (pullback.snd a.left a.left) g =
            pullback.snd (U.ι ≫ pullback.snd a.left a.left) g ∧
          IsIso (coprod.desc s j) ∧
          ∃ e : Γ(pullback (pullback.snd a.left a.left) g, ⊤) ≃+*
            K × Γ(pullback (U.ι ≫ pullback.snd a.left a.left) g, ⊤),
            ∀ r, e r = ((s.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom r,
              j.appTop.hom r)) ∧
      (n = 1 → IsEmpty U.toScheme ∧ IsOpenImmersion a.left) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
