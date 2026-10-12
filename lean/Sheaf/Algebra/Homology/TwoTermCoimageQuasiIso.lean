/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Cohomology projection of a two-term coimage complex

Source: Stacks Project, Tags 010V, 0118, and 08J5.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A two-term complex consisting of the coimage of the incoming differential
and the cycles maps quasi-isomorphically to the single cohomology object.
Source: Stacks Project, [Section 010V](https://stacks.math.columbia.edu/tag/010V),
[Tag 0118](https://stacks.math.columbia.edu/tag/0118), and
[Remark 08J5](https://stacks.math.columbia.edu/tag/08J5)
(blueprint: lem-weil-pbc-two-term-coimage-quasiiso).

Proof: away from `q - 1` and `q`, the source has a zero term, hence zero
cohomology. At `q - 1`, its outgoing differential is mono and its incoming
term is zero, so its cohomology is zero. The single complex has zero
cohomology in all these degrees too, and any map between zero objects is
an isomorphism. At `q`, the outgoing term is zero. Identify its cycles with
`M.X q`, and then with `K.cycles q` using `e₁`. Under this identification the
image of the incoming differential is the image of `K.toCycles (q - 1) q`:
by `hd`, the composites into `K.X q` agree after precomposing with the epi
`cokernel.π (kernel.ι (K.d (q - 1) q))` and the isomorphism `e₀.inv`;
cancel the mono cycles inclusion to get equality of these corestrictions.
Precomposition with an epi preserves the image. Thus the source cohomology
is the cokernel of the boundaries inclusion into `K.cycles q`, namely
`K.homology q`. The equation `hb` says the induced map on that cokernel is
the identity, after the canonical identification of the target single-complex
cohomology with `K.homology q`. It is therefore an isomorphism in every degree.
For the zero complex or a zero incoming differential the same calculation
has zero coimage and reduces to the identity on cycles; there is no boundedness
hypothesis on `K` and no positivity hypothesis on `q`.
-/
theorem twoTermCoimage_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (K M : CochainComplex C ℤ) (q : ℤ)
    (hM : ∀ r : ℤ, r ≠ q - 1 → r ≠ q → IsZero (M.X r))
    (e₀ : M.X (q - 1) ≅ cokernel (kernel.ι (K.d (q - 1) q)))
    (e₁ : M.X q ≅ K.cycles q)
    (hd : cokernel.π (kernel.ι (K.d (q - 1) q)) ≫ e₀.inv ≫
      M.d (q - 1) q ≫ e₁.hom ≫ K.iCycles q = K.d (q - 1) q)
    (hm : Mono (M.d (q - 1) q))
    (b : M ⟶ (singleFunctor C q).obj (K.homology q))
    (hb : e₁.inv ≫ b.f q ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
      K.homologyπ q) : QuasiIso b := by sorry

end CochainComplex
