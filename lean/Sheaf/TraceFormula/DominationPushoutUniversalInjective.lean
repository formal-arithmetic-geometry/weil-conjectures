module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Sheaf.RingTheory.UniversalInjectiveFiniteTest

/-!
# Domination and universal injectivity of a pushout leg

Source: Stacks Project, Algebra, Tag 0AUM, `lemma-domination-universally-injective`
(blueprint: lem-trf-domination-pushout-universal-injective).
-/

@[expose] public section
set_option autoImplicit false

universe u v w

namespace LinearMap

/-- For maps of modules with a common source, domination is equivalent to universal
injectivity of the canonical pushout leg.  Domination of `a` by `b` is rendered with
`a ⊗ id_L = a.rTensor L` and `b ⊗ id_L = b.rTensor L`, as in the source; the pushout
`Q'' = Q ⊔_P Q'` is formed in `ModuleCat R` (the three modules share a universe `w`,
independent of the universe of `R`), its leg `b' : Q' → Q''` is `pushout.inr`, and
universal injectivity of `b'` is injectivity of `L ⊗ b' = b'.lTensor L` for every `L`.
Source: Stacks Project, Algebra, Tag 0AUM, `lemma-domination-universally-injective`.
(blueprint: lem-trf-domination-pushout-universal-injective).

Proof (the node's steps):
1. Put `D = Q' ⊕ Q`, `δ x = (b x, -a x)`, `E = D / δ(P)` with quotient `π`,
   `j y = π (y, 0)`, `k z = π (0, z)`.  Then `j ∘ b = k ∘ a`, and `E` has the pushout
   universal property (a pair `u, v` with `u ∘ b = v ∘ a` gives `(y, z) ↦ u y + v z`,
   which kills `δ(P)`); so the comparison `E ≅ Q''` carries `j` to `b'`.  The sequence
   `P → D → E → 0` is exact.
2. For an arbitrary `L`, `D ⊗ L ≅ (Q' ⊗ L) ⊕ (Q ⊗ L)` by `F`, `G` (checked on pure
   tensors); in these coordinates `F δ_L w = (b_L w, -a_L w)` and `π_L G (s, 0) = j_L s`.
3. Tensor right exactness applied to `P → D → E → 0` gives `ker π_L = im δ_L`.
4. Hence `ker j_L = b_L (ker a_L)`: if `j_L s = 0` then `G (s, 0) = δ_L w`, and `F` gives
   `a_L w = 0`, `s = b_L w`; conversely `a_L w = 0` gives `j_L (b_L w) = π_L δ_L w = 0`.
5. So `j_L` is injective iff `ker a_L ⊆ ker b_L`; over all `L` this is domination.  The
   isomorphism `E ≅ Q''` survives tensoring, so `j_L` is injective iff `b' ⊗ id_L` is, and
   the swap `V ⊗ L ≅ L ⊗ V` turns this into injectivity of `L ⊗ b'`.  The finite-test
   criterion for universal injectivity is `LinearMap.universally_injective_tensor_iff`.
-/
theorem domination_iff_pushout_leg_universally_injective
    (R : Type u) [CommRing R]
    (P Q Q' : Type w) [AddCommGroup P] [AddCommGroup Q] [AddCommGroup Q']
    [Module R P] [Module R Q] [Module R Q']
    (a : P →ₗ[R] Q) (b : P →ₗ[R] Q') :
    ((∀ (L : Type v) [AddCommGroup L] [Module R L],
        LinearMap.ker (a.rTensor L) ≤ LinearMap.ker (b.rTensor L)) ↔
      ∀ (L : Type v) [AddCommGroup L] [Module R L],
        Function.Injective
          (LinearMap.lTensor L
            ((CategoryTheory.Limits.pushout.inr (ModuleCat.ofHom a)
              (ModuleCat.ofHom b)).hom))) := by
  sorry

end LinearMap
