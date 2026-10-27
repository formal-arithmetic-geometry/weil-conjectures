module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Restriction kernels on finite unions of principal opens

Source: Stacks Project, Morphisms, Tag 056C (example-scheme-theoretic-closure), and
Schemes, Tag 01HV (lemma-spec-sheaves), parts (3) and (5).
(blueprint: lem-trf-principal-union-restriction-kernel-localization)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- On `Spec A`, the kernel of restriction from `D(g)` to
`D(g) ∩ ⋃ i, D(f i)`, transported to `A[1/g]` by the canonical localization
isomorphism, consists exactly of fractions whose numerator vanishes in every `A[1/f i]`.

Source: Stacks Project, Morphisms, Tag 056C (example-scheme-theoretic-closure), and
Schemes, Tag 01HV (lemma-spec-sheaves), parts (3) and (5).
(blueprint: lem-trf-principal-union-restriction-kernel-localization)

Proof plan:
1. The opens `D(g) ∩ D(f i)` cover the intersection. Sheaf uniqueness says a
   section is zero there iff its restrictions to all these opens are zero, including
   the empty cover (def-weil-affine-spectrum; def-weil-pbc-sites-and-cohomology).
2. Write the section as `a/g^r`. On `D(f i)`, put `a_i` and `g_i` for the images
   in `A[1/f i]`. Its further restriction to the basic open of `g_i` is zero iff
   `g_i^e_i * a_i = 0` for some natural exponent `e_i`: use the canonical
   restriction/localization identification and the zero-fraction relation
   (lem-weil-pbc-affine-open-section-vanishing-prime, part (b);
   lem-weil-pbc-basic-open-function, part (a); def-weil-ring-localization-away).
3. Choose `N` to be the maximum of `0` and the finitely many `e_i`. Then
   `b = g^N * a` vanishes in every `A[1/f i]`, and the fraction relation gives
   `a/g^r = b/g^(r+N)`. For `n = 0`, use `N = 0`.
4. Conversely, a numerator vanishing in every `A[1/f i]` gives zero on each
   intersection, hence zero on their union by Step 1. The fraction relation and
   sheaf uniqueness apply also to zero rings and nilpotent denominators.
-/
theorem principalUnion_restriction_kernel_localization
    (A : Type u) [CommRing A] (n : ℕ) (f : Fin n → A) (g : A) :
    {z : Localization.Away g |
      (Spec (CommRingCat.of A)).presheaf.map
        (homOfLE (inf_le_left :
          PrimeSpectrum.basicOpen g ⊓ (⨆ i : Fin n, PrimeSpectrum.basicOpen (f i)) ≤
            PrimeSpectrum.basicOpen g)).op
        ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
          ((Spec.structureSheaf A).obj.obj (op (PrimeSpectrum.basicOpen g)))) z) = 0} =
    {z : Localization.Away g | ∃ a : A,
      (∀ i : Fin n, algebraMap A (Localization.Away (f i)) a = 0) ∧
        ∃ r : ℕ, z = Localization.mk (S := Submonoid.powers g) a ⟨g ^ r, ⟨r, rfl⟩⟩} := by
  sorry

end AlgebraicGeometry
