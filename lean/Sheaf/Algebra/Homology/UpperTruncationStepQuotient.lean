/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Coordinates of the quotient of successive upper truncations

Source: Stacks Project, Tags 0118, 0114, and 08J5.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The cokernel of the inclusion of successive canonical upper truncations is
supported in degrees `q - 1` and `q`, with its induced differential a monomorphism.
Source: Stacks Project, [Tag 0118](https://stacks.math.columbia.edu/tag/0118),
[Tag 0114](https://stacks.math.columbia.edu/tag/0114), and
[Remark 08J5](https://stacks.math.columbia.edu/tag/08J5)
(blueprint: lem-weil-pbc-upper-step-quotient-coordinates).

Proof: the compatibility with the inclusions into `K` determines `i` uniquely,
since the latter inclusion is mono. Below `q - 1`, identify both truncations
with `K`; then `i` is the identity. At `q - 1`, it is the kernel inclusion
`kernel.ι (K.d (q - 1) q)` after the canonical cycles identification. At `q`,
its source is zero and its target is `K.cycles q`. Above `q` both objects are
zero. Evaluation preserves cokernels in the abelian category of complexes.
The degreewise cokernel universal properties therefore give zero objects away
from the two named degrees and the isomorphisms `e₀` and `e₁`, with exactly the
stated identities for the cokernel projection. The differential identity follows
from the chain-map identity for that projection; cancel its epimorphic component
in degree `q - 1`. The composite of the resulting differential with the cycles
inclusion is the coimage factor of `K.d (q - 1) q`, which is mono in an abelian
category (the coimage-to-image map is an isomorphism). Consequently the
quotient differential itself is mono. This also covers zero differentials and
the zero complex: the coimage is then zero.
-/
theorem upperTruncationStep_quotientCoordinates
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (q : ℤ)
    (i : K.truncLE (q - 1) ⟶ K.truncLE q)
    (hi : i ≫ K.ιTruncLE q = K.ιTruncLE (q - 1)) :
    (∀ r : ℤ, r ≠ q - 1 → r ≠ q → IsZero ((cokernel i).X r)) ∧
    ∃ (e₀ : (cokernel i).X (q - 1) ≅ cokernel (kernel.ι (K.d (q - 1) q)))
      (e₁ : (cokernel i).X q ≅ K.cycles q),
      (cokernel.π i).f (q - 1) ≫ e₀.hom =
        (K.ιTruncLE q).f (q - 1) ≫ cokernel.π (kernel.ι (K.d (q - 1) q)) ∧
      (cokernel.π i).f q ≫ e₁.hom = (K.truncLEXIsoCycles q).hom ∧
      cokernel.π (kernel.ι (K.d (q - 1) q)) ≫ e₀.inv ≫
          (cokernel i).d (q - 1) q ≫ e₁.hom ≫ K.iCycles q = K.d (q - 1) q ∧
      Mono ((cokernel i).d (q - 1) q) := by sorry

end CochainComplex
