module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Extension.ExtendScalars
import WeilConjectures.RingTheory.JacobiZariskiHomologySequence

/-!
# The conormal exact sequence of two compatible ring quotients

Source: Stacks Project, Algebra, Tag 065V, `lemma-application-NL`
(blueprint: lem-sfb-ring-two-quotients-conormal-exact).
-/

@[expose] public section

universe u v w

namespace Algebra.Extension

/-- Source: Stacks Project, Algebra, Tag 065V, `lemma-application-NL`
(blueprint: lem-sfb-ring-two-quotients-conormal-exact).

The algebra structures and scalar tower encode the compatible maps `A → B → C`.
The two `ofSurjective` extensions have conormal modules `I/I²` and `J/J²`, with
Mathlib's canonical `C`-module structures. The representative equation specifies
`u([a]) = [α(a)]`. The second arrow is the canonical `cotangentComplex`, whose
`cotangentComplex_mk` formula is `[b] ↦ 1 ⊗ db` in `C ⊗[B] Ω[B⁄A]`.

Proof (the node's five steps):
1. The structure map sends `I` into `J` and `I²` into `J²`, giving the well-defined
   `C`-linear map `u`. Leibniz and the tensor balancing relations show that
   `b ↦ 1 ⊗ db` kills `J²`, descends `C`-linearly, and vanishes on the image of `u`
   (def-weil-pbc-kahler-differentials and def-weil-pbc-module-tensor-product).
2. Lift each `c ∈ C` through `A` to see that `B → C` is surjective. Apply
   lem-weil-pbc-jacobi-zariski-surjection-h1 to both quotient maps to obtain
   `H₁(L_{C/A}) ≃ I/I²` and `H₁(L_{C/B}) ≃ J/J²`. Constant polynomials `a ∈ I`
   and `b ∈ J` are cycles, and the explicit lift-evaluation formula sends them
   to `[a]` and `[b]`, respectively; these classes exhaust the conormal modules.
3. Apply lem-weil-pbc-jacobi-zariski-homology-sequence to `A → B → C`.
   The coefficientwise map on canonical polynomial presentations takes the
   constant cycle of `a` to that of `α(a)`, so under the identifications of
   step 2 its middle map is precisely `u`.
4. The connecting-map coefficient formula of that same Jacobi–Zariski node
   sends the constant cycle of `b ∈ J` to `1 ⊗ db`. Thus its connecting map is
   precisely the displayed `cotangentComplex` after the conormal identification.
5. The surjection-H₁ node gives `Ω[C⁄A] = 0`, so Jacobi–Zariski exactness makes
   the second arrow surjective. If its value on `y` is zero, lift `y` through
   the conormal isomorphism: exactness supplies a preimage in `H₁(L_{C/A})`,
   and step 3 supplies a preimage under `u`. Conversely the composite is zero
   by step 1. Hence the kernel is the image. No further ring hypothesis enters. -/
theorem two_quotients_conormal_exact
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hπ : Function.Surjective (algebraMap A C)) :
    ∃ hβ : Function.Surjective (IsScalarTower.toAlgHom A B C),
      ∃ u : (ofSurjective (Algebra.ofId A C) hπ).Cotangent →ₗ[C]
          (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).Cotangent,
        (∀ (a : (ofSurjective (Algebra.ofId A C) hπ).ker)
          (b : (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).ker),
          (b.1 : B) = algebraMap A B (a.1 : A) →
            u (Cotangent.mk a) = Cotangent.mk b) ∧
        Function.Exact u
          (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).cotangentComplex ∧
        Function.Surjective
          (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).cotangentComplex := by
  sorry

end Algebra.Extension
