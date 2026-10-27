module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.GoingDown
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Generic reducedness under field extension

Source: Stacks Project, `algebra.tex`, Tags 00I4 and 00HS, with faithfully flat descent
(blueprint: lem-per-field-extension-generic-reducedness).

Generic reducedness is expressed directly using Mathlib's minimal primes and reduced prime
localizations. The tensor product has its standard commutative algebra multiplication.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Generic reducedness of a commutative algebra over a characteristic-zero field is invariant
under arbitrary extension of that field. There are no finiteness or nontriviality assumptions
on the algebra. The prime-instance binders only allow formation of `Localization.AtPrime`;
membership in `minimalPrimes` already implies primality.

Source: Stacks Project, `algebra.tex`, Tags 00I4 (perfect reduced tensor products) and 00HS
(flat going down), together with 00HQ, 00HR, 00HT and 05CK for faithfully flat descent
(blueprint: lem-per-field-extension-generic-reducedness).

Proof plan:
1. Put `B = E ⊗[F] A` and `i(a) = 1 ⊗ a`. If `A` is the zero ring, bilinearity and
   generation by pure tensors make `B` the zero ring. Both conditions are vacuous because
   neither ring has a prime ideal (`def-weil-pbc-module-tensor-product`).
2. The map `A → A ⊗[F] E` is faithfully flat by
   `lem-weil-pbc-field-extension-base-change-faithfully-flat`. The switch isomorphism
   `a ⊗ e ↦ e ⊗ a`, whose inverse reverses the factors, identifies this map with `i`.
   Both maps preserve the bilinear relations and multiplication, so `i` is faithfully flat
   (`def-weil-pbc-faithfully-flat-ring-map`).
3. A minimal prime `q` of `B` contracts to a minimal prime `p` of `A`: any strictly smaller
   prime below `p` lifts below `q` by `lem-sc-flat-going-down`, contradicting minimality.
4. For any prime `p` of `A`, put `S = A \ p` and `C = E ⊗[F] A_p`. The inverse maps
   `e ⊗ (a/s) ↦ (e ⊗ a)/i(s)` and `b/i(s) ↦ j(b) * (1 ⊗ (s/1))⁻¹`, where
   `j(e ⊗ a) = e ⊗ (a/1)`, identify `C` with `i(S)⁻¹B`. The fraction relation
   `u * (a*s' - a'*s) = 0` becomes the same relation after inverting `i(u)`; the tensor
   relations are bilinearity. The composites fix pure tensors and denominator inverses,
   which generate the rings. Thus `j(b) = 0` iff `i(s)*b = 0` for some `s ∉ p`
   (`def-weil-pbc-localization-at-prime`, `def-weil-pbc-module-localization`, and
   `def-weil-pbc-module-tensor-product`).
5. Suppose `A` is generically reduced and `q` is minimal in `B`. By step 3 its contraction
   `p` is minimal, so `A_p` is reduced. Characteristic zero makes `F` perfect, and `E`
   is reduced. Hence `C` is reduced by `lem-weil-pbc-perfect-reduced-tensor` (Tag 00I4).
   If `(b/t)^n = 0` in `B_q`, with `n ≥ 1` and `t ∉ q`, choose `u ∉ q` with `u*b^n = 0`.
   Then `j(u*b)^n = j(u^(n-1)*u*b^n) = 0`, so `j(u*b) = 0`. Step 4 supplies `s ∉ p`
   with `i(s)*u*b = 0`. Since `i(s)*u ∉ q`, the fraction zero criterion gives `b/t = 0`.
6. Conversely, suppose `B` is generically reduced and `p` is minimal in `A`. Lift `p` to
   a prime `q₀` of `B` using `lem-weil-pbc-faithfully-flat-surjective-spectrum`, and choose
   a minimal `q ≤ q₀` by `lem-weil-pbc-prime-contains-minimal-prime`. Its contraction is
   prime and contained in `p`, hence equals `p`. Thus `B_q` is reduced.
7. The map `A_p → B_q` is flat and local by `lem-weil-pbc-flat-local-ring-maps`, hence
   faithfully flat by `lem-weil-pbc-flat-local-hom-faithfully-flat`. Apply
   `lem-weil-pbc-faithfully-flat-universally-injective` to the module `A_p`: under the
   isomorphism `A_p ⊗[A_p] B_q ≃ B_q`, given by `a ⊗ b ↦ i_q(a)*b` with inverse
   `b ↦ 1 ⊗ b`, this says the local map is injective. A nilpotent of `A_p` maps to zero
   in reduced `B_q`, hence is zero. Therefore `A_p` is reduced for every minimal `p`.
-/
theorem genericallyReduced_iff_field_extension
    (F : Type u) (E : Type v) (A : Type w)
    [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] :
    (∀ (p : Ideal A) [p.IsPrime], p ∈ minimalPrimes A →
      IsReduced (Localization.AtPrime p)) ↔
    (∀ (q : Ideal (E ⊗[F] A)) [q.IsPrime], q ∈ minimalPrimes (E ⊗[F] A) →
      IsReduced (Localization.AtPrime q)) := by
  sorry

end Algebra
