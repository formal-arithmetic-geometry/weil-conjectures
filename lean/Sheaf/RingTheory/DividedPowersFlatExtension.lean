module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Extension of divided powers along a flat ring map

Source: Stacks Project, Tag 07H1, Lemma `lemma-gamma-extends`, uniqueness and
existence under condition (3) (blueprint: lem-sfb-pd-flat-extension).
-/

@[expose] public section

universe u v

namespace DividedPowers

/-- Divided powers extend uniquely to the extended ideal along a flat ring map.

Source: Stacks Project, Tag 07H1, Lemma `lemma-gamma-extends`, flat case
(blueprint: lem-sfb-pd-flat-extension).

Proof plan:
1. For `z = ∑ i, b i * f (x i)` with `x i ∈ I`, the addition and scalar axioms
   force the degree-`n` operation to be the sum over all multiindices of total
   degree `n` of `∏ i, b i ^ e i * f (γ.dpow (e i) (x i))`. This proves uniqueness.
   For positive `n`, some exponent is positive in every term, so this sum is in
   `I.map f`. This is the expression of lem-sfb-pd-linear-substitution.
2. Given two presentations of `z`, apply the equational criterion for flatness
   (lem-weil-pbc-flat-equational-criterion) to their difference. Obtain a common
   tuple `c j` and matrices over `A` expressing both coefficient tuples, with the
   same source tuple `y j ∈ I`. Applying lem-sfb-pd-linear-substitution to each
   presentation gives the same value. Define the positive operations by this
   well-defined formula; on the ideal the zeroth operation is one, and off the
   ideal all operations are zero, as required by `DividedPowers`.
3. The degree-one formula is `z`; scaling all coefficients by `c` scales degree
   `n` by `c ^ n`. Concatenating presentations of `z` and `w`, then partitioning
   the multiindices by degree in the first block, gives the addition axiom. The
   empty presentation gives zero for positive operations at zero.
4. A one-term presentation gives compatibility on `f(I)`. Apply `f` to the
   product and iteration axioms for `γ` to get them on these generators; the
   iteration uses `γ.dpow m x ∈ I` for `m > 0`. The ideal-valuedness from step 1
   and the three global axioms from step 3 allow lem-sfb-pd-generator-criterion
   to extend the remaining two axioms to all of `I.map f`. Combine existence,
   compatibility, and uniqueness from step 1.
-/
theorem existsUnique_extension_of_flat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (I : Ideal A) (γ : DividedPowers I) :
    ∃! δ : DividedPowers (I.map f),
      ∀ (x : A), x ∈ I → ∀ (n : ℕ), 1 ≤ n → δ.dpow n (f x) = f (γ.dpow n x) := by
  sorry

end DividedPowers
