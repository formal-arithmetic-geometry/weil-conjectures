/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.CategoryTheory.YonedaDerivedExtComparison
public import Sheaf.CategoryTheory.YonedaZeroSplice
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Pullback of a Yoneda prefix and replacement of its short exact tail

Source: Stacks Project, Derived Categories, Tags 06XT and 06XP; Homology,
Section 010I and Tags 05PJ, 05PK, 08N5
(blueprint: lem-coef-yoneda-pullback-splice).

We reuse actual exact sequences, endpoint-fixed equivalence, and `RightSplice`.
The kernel equations determine the induced kernel map. A pullback square specifies
precisely the replacement of the prefix's last middle term. Isomorphisms identify
retained terms, and the comparison agrees with the pullback projection and `p`
under these identifications. No Ext comparison or resolution is assumed.
-/

@[expose] public section

universe u v

namespace CategoryTheory.YonedaExtension

open CategoryTheory.Limits

/-- Replacing the last middle term of an extension along `p` with epic composite
onto the quotient gives a pulled-back prefix, an exact right splice, and its
specified endpoint-fixed comparison to the original extension.

The degree is `n + 2`, so `n = 0` includes degree two. The arrow `e` is the final
arrow after identifying the right endpoint with `F`; `he` records this naming.
`B` is the prefix ending in `kernel e`. Its retained part is identified by `t`,
and its final arrow is the factorization `d`. The morphism `b` is the pullback
comparison from `H` to `B`: its earlier components are isomorphisms, and its
last-middle square is a pullback. Since `H.sequence` is a complex, its incoming
arrow has zero component in `kernel (p ≫ e)`. The splice `G` is specified by `s`;
the equations on `φ` say that it is the pullback projection at the replaced term,
`p` at the appended term, and the identities on all retained terms after their
specified identifications.

Source: Stacks Project, Derived Categories, Tags 06XT and 06XP; Homology,
Section 010I, Tags 05PJ, 05PK, 08N5
(blueprint: lem-coef-yoneda-pullback-splice).

Proof plan (the node's seven steps):
1. Factor the penultimate arrow through `kernel e` to obtain `d`. Exactness and
`ShortComplex.exact_iff_epi_kernel_lift` make `d` epic. The kernel inclusion is
monic, so replacing the final arrow by `d` preserves preceding exactness, giving
`B`. The kernel sequence of the epic `p ≫ e` is short exact. Its kernel inclusion
followed by `p` uniquely factors through `kernel e`, giving `a`.
2. Form the pullback of `d` and `a`, equivalently the kernel of their difference
on the biproduct. The incoming arrow is the unique lift with original component
in the old middle term and zero component in the new kernel. This also makes
its composite with the preceding differential zero.
3. The pullback projection onto the new kernel is epic: lift any generalized
element after an epimorphic refinement along `d`, then use the pullback property.
The epimorphism criterion of `lem-sp-abelian-refinements` proves epicity.
4. To prove exactness at the pullback, project an element killed by its second
projection to the old middle term, lift it after an epimorphic refinement using
original exactness, and compare both pullback projections. The exactness
criterion of `lem-sp-abelian-refinements` gives the result.
5. In degree two the new first arrow is monic since its first projection is the
old monomorphism. In higher degrees its kernel equals the old incoming arrow's
kernel, by the two pullback projections. All earlier terms are unchanged. These
checks, with the epic last projection, give the extension `H` in every degree.
6. Splice using the projection followed by the kernel inclusion. Monicity of
that inclusion preserves the kernel at the pullback term. At `P`, the induced
map to `kernel (p ≫ e)` is the epic projection, so the kernel-lift exactness
criterion gives exactness. Other terms and endpoint conditions are unchanged.
7. Use the first pullback projection, `p`, and identities on retained terms for
`φ`. The incoming square is the lift equation; the joining square is the
pullback equation followed by the kernel inclusion and the defining equation
of `a`. The final square is the definition of `p ≫ e`. Both endpoint maps are
identities. This single morphism generates Yoneda equivalence of `G` and `E`.
No projective or injective object is used in any step. -/
theorem pullback_splice_equivalent {A : Type u} [Category.{v} A] [Abelian A]
    {T F : A} (n : ℕ) (E : YonedaExtension A T F (n + 2))
    (e : E.sequence.obj' (n + 2) ⟶ F)
    (he : E.sequence.map' (n + 2) (n + 3) ≫ E.rightIso.hom = e)
    (P : A) (p : P ⟶ E.sequence.obj' (n + 2)) [Epi (p ≫ e)] :
    ∃ (d : E.sequence.obj' (n + 1) ⟶ kernel e)
      (a : kernel (p ≫ e) ⟶ kernel e)
      (B : YonedaExtension A T (kernel e) (n + 1))
      (t : B.sequence.δlast ≅ E.sequence.δlast.δlast)
      (H : YonedaExtension A T (kernel (p ≫ e)) (n + 1))
      (b : H.sequence ⟶ B.sequence)
      (G : YonedaExtension A T F (n + 2))
      (s : RightSplice
        (ShortComplex.mk (kernel.ι (p ≫ e)) (p ≫ e) (kernel.condition (p ≫ e))) H G)
      (φ : G.sequence ⟶ E.sequence),
      d ≫ kernel.ι e = E.sequence.map' (n + 1) (n + 2) ∧
      a ≫ kernel.ι e = kernel.ι (p ≫ e) ≫ p ∧
      t.hom.app 0 ≫ E.leftIso.hom = B.leftIso.hom ∧
      B.sequence.map' (n + 1) (n + 2) ≫ B.rightIso.hom =
        t.hom.app (Fin.last (n + 1)) ≫ d ∧
      (ShortComplex.mk (kernel.ι (p ≫ e)) (p ≫ e)
        (kernel.condition (p ≫ e))).ShortExact ∧
      H.leftMap B b = 𝟙 T ∧ H.rightMap B b = a ∧
      (∀ k : Fin (n + 3), k.val < n + 1 → IsIso (b.app k)) ∧
      IsPullback (b.app ⟨n + 1, by omega⟩)
        (H.sequence.map' (n + 1) (n + 2) ≫ H.rightIso.hom)
        (B.sequence.map' (n + 1) (n + 2) ≫ B.rightIso.hom) a ∧
      (∀ k : Fin (n + 2),
        s.prefixIso.hom.app k ≫ φ.app k.castSucc.castSucc =
          b.app k.castSucc ≫ t.hom.app k) ∧
      s.lastIso.hom ≫ ComposableArrows.app' φ (n + 2) = p ∧
      G.leftMap E φ = 𝟙 T ∧ G.rightMap E φ = 𝟙 F ∧ G.Equivalent E := by
  sorry

end CategoryTheory.YonedaExtension
