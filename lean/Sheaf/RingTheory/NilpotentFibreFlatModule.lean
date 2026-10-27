module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Sheaf.RingTheory.NilpotentIdealFlatnessCriterion

/-! # Nilpotent fibre criterion for flat modules

Source: Stacks Project, Algebra, Tag 06A5, `lemma-criterion-flatness-fibre-nilpotent`,
first conclusion with `S = S' = A`
(blueprint: lem-sfb-nilpotent-fibre-flat-module).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Module.Flat

/-- Flatness over the base and over a nilpotent closed fibre implies flatness over the algebra.
Source: Stacks Project, Algebra, Tag 06A5, `lemma-criterion-flatness-fibre-nilpotent`,
first conclusion with `S = S' = A`
(blueprint: lem-sfb-nilpotent-fibre-flat-module).

The ideal `I.map (algebraMap R A)` is `IA`. Its product with the full `A`-submodule
of `M` is `IM`: every generator `(algebraMap R A i) • m` lies in this product, and
`a • ((algebraMap R A i) • m) = (algebraMap R A i) • (a • m)` gives the converse.
Thus the displayed quotient has the canonical `A/IA`-action on `M/IM`.

Proof:
1. By `def-weil-pbc-flat-ring-map`, flatness over `R` makes
   `I ⊗[R] M → R ⊗[R] M` injective. Under `R ⊗[R] M ≃ M`, whose inverse sends
   `m` to `1 ⊗ m`, this is the multiplication map `μ_R : I ⊗[R] M → M`.
2. Put `J = IA`. By `def-weil-pbc-module-tensor-product`, the tensor universal
   property gives `θ : I ⊗[R] M → J ⊗[A] M`, sending `i ⊗ m` to `f(i) ⊗ m`.
   It is surjective: write any `j ∈ J` as a finite sum of `a * f(i)`, and use
   `(a * f(i)) ⊗ m = f(i) ⊗ (a • m)` to lift each pure tensor.
3. The multiplication map `μ_A : J ⊗[A] M → M` satisfies `μ_A θ = μ_R`,
   first on pure tensors and then everywhere by the tensor universal property.
   If `μ_A z = 0`, lift `z = θ y`; injectivity of `μ_R` gives `y = 0`, hence `z = 0`.
4. Expand a product of `N` sums of generators of `J`. Each term contains an image
   of a product of `N` elements of `I`, so `I ^ N = 0` implies `J ^ N = 0`.
   The equality `JM = IM` explained above identifies the flat fibre quotient with `M/JM`.
5. Apply `lem-sfb-nilpotent-ideal-flatness-criterion`, namely
   `Module.Flat.of_nilpotent_ideal_multiplication_injective`, to `A`, `J` and `M`.
   Steps 3 and 4 and the given fibre flatness are exactly its hypotheses, so `M`
   is flat over `A`. No finiteness or Noetherian assumption occurs. -/
theorem of_nilpotent_fibre
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) (N : ℕ) (hN : 1 ≤ N) (hI : I ^ N = ⊥)
    {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (hflat : Module.Flat R M)
    (hfibre : Module.Flat (A ⧸ I.map (algebraMap R A))
      (M ⧸ (I.map (algebraMap R A)) • (⊤ : Submodule A M))) :
    Module.Flat A M := by
  sorry

end Module.Flat
