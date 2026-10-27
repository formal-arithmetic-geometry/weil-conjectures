module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.Algebra.FiniteTypeLiftNilpotent
import WeilConjectures.RingTheory.NakayamaNilpotent

/-!
# Local finite presentation is invariant under flat nilpotent deformation

Source: Stacks Project, More on Morphisms, Tag 06AG, `lemma-deform-property`, clause (13)
(blueprint: lem-sfb-flat-deformation-lfp).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A flat morphism to `Spec A` is locally of finite presentation if and only if its base
change to `Spec (A ⧸ I)` is locally of finite presentation, when a positive power of `I` is zero.
No Noetherian or prior finite-type assumption is required.

Source: Stacks Project, More on Morphisms, Tag 06AG, `lemma-deform-property`, clause (13),
with `X' = Y`, `Y' = S' = Spec A`, and `S = Spec (A ⧸ I)`.
(blueprint: lem-sfb-flat-deformation-lfp)

Proof, following the eight steps of the node:
1. Put `A₀ = A/I`. For each affine open `U = Spec B` in `Y`, its inverse image in the
   pullback is `Spec (A₀ ⊗[A] B) = Spec (B/IB)` by
   `lem-weil-pbc-fibre-product-affine-spectra`. The maps are `ā ⊗ b ↦ ab mod IB` and
   `b mod IB ↦ 1 ⊗ b`; tensor balancing proves they are inverse. These opens cover.
2. If `f` is locally finitely presented, `lem-weil-pbc-lfp-affine-opens-finite-presentation`
   makes every `B` finitely presented over `A`. By
   `lem-weil-pbc-finite-presentation-base-change-composition`, its reduction is finitely
   presented over `A₀`. The affine cover and `def-sbc-locally-finite-presentation` give
   local finite presentation of the pullback projection.
3. Conversely, suppose the projection is locally finitely presented. The affine flatness
   criterion `lem-weil-pbc-flat-morphism-affine-criterion` makes `B` flat over `A`.
   The reduced affine-open criterion makes `B₀ = B/IB` finitely presented over `A₀`.
4. Finite presentation implies finite type, by `def-weil-pbc-finitely-presented-algebra`.
   Apply `lem-weil-pbc-finite-type-lift-nilpotent` to lift finitely many generators to `B`.
   The universal property `def-weil-pbc-mv-polynomial-ring` gives a surjection
   `P = A[x₁,…,xₙ] → B`. Write `K` for its kernel, obtaining `0 → K → P → B → 0`.
5. Since `B` is flat over `A`, `lem-weil-pbc-flat-quotient-tensor-injective` makes tensoring
   this sequence with `A₀` exact on the left as well. For any module `M`, identify
   `A₀ ⊗[A] M` with `M/IM` by the mutually inverse balanced maps above.
   Coefficient reduction gives `P/IP = A₀[x₁,…,xₙ] = P₀`. Thus `K/IK` is the kernel of
   `P₀ → B₀`, as a `P₀`-module; this injection is where flatness is used.
6. By `lem-weil-pbc-finite-presentation-surjection-kernel-fg`, that reduced kernel has
   finitely many ideal generators. Lift them to `g₁,…,gₘ` in `K`. Coefficient reduction
   `P → P₀` is surjective, so `P^m → K`, `(cⱼ) ↦ ∑ cⱼ gⱼ`, is surjective modulo `I`.
7. Apply `lem-weil-pbc-nakayama-nilpotent` over `P` with ideal `J = IP` to this map.
   Expanding products gives `J^N = 0`, and `JK = IK` because `K` is an ideal of `P`.
   Nilpotent Nakayama needs no finiteness hypothesis and makes the map surjective.
   Therefore `K` is generated as an ideal by the finitely many `gⱼ`.
8. Hence `B = P/(g₁,…,gₘ)` is finitely presented by
   `def-weil-pbc-finitely-presented-algebra`. Apply `def-sbc-locally-finite-presentation`
   to the arbitrary affine opens `U` and the affine base to conclude the converse.
-/
theorem locallyOfFinitePresentation_iff_of_flat_nilpotent_quotient
    {A : Type u} [CommRing A] (I : Ideal A) (N : ℕ) (hN : 0 < N)
    (hI : I ^ N = ⊥) {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of A)) [Flat f] :
    LocallyOfFinitePresentation f ↔
      LocallyOfFinitePresentation
        (pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  sorry

end AlgebraicGeometry
