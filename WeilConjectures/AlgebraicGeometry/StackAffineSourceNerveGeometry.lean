/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StackQcqsMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.AlgebraicStackChangeBaseToIntegers
import WeilConjectures.AlgebraicGeometry.AlgebraicStackQcqsPermanence
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Geometry of affine-source nerve terms

Source: Stacks Project, stacks-cohomology.tex, Tag 076Z,
lemma-general-pushforward, proof paragraphs 2--5; stacks-morphisms.tex, Tag 075S
(blueprint: lem-sfb-stack-affine-source-nerve-geometry).

The terms are actual iterated 2-fibre products. The one-factor term is presented
as `V ×_A A`, with the second map the identity, hence is canonically equivalent
to `V`. This presentation keeps independent object and morphism universes for
`A` without restricting them to the universe of the scheme site.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t s

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory

/-- The term and augmentation of the iterated affine-source 2-fibre product.
The initial term is `V ×_A A` along the identity of `A`. Each subsequent term
adds one more factor `V` using the already constructed augmentation. All data
come from the existing iso-comma 2-fibre product, including its vertical
isomorphism condition; no representative or atlas is chosen.
Source: Stacks Project, Tag 076Z, displayed iterated fibre products
(blueprint: lem-sfb-stack-affine-source-nerve-geometry). -/
def stackAffineSourceNerve {S : Scheme.{u}}
    {A : BasedCategory.{v, w} (Over S)} {V : Over S}
    (a : BasedFunctor (discreteModuli (yoneda.obj V)) A) :
    ℕ → (N : BasedCategory.{max u v, max (u + 1) v w} (Over S)) × BasedFunctor N A
  | 0 => ⟨moduliTwoFiberProduct a (BasedFunctor.id A),
      (moduliTwoFiberFst a (BasedFunctor.id A)).comp a⟩
  | n + 1 => ⟨moduliTwoFiberProduct (stackAffineSourceNerve a n).2 a,
      (moduliTwoFiberFst (stackAffineSourceNerve a n).2 a).comp
        (stackAffineSourceNerve a n).2⟩

/-- Affine-source nerve terms over an affine target are qcqs algebraic spaces;
they are schemes for a space target, separated schemes for a scheme target,
and affine schemes if that scheme is separated over the affine target.
Source: Stacks Project, Tag 076Z, proof paragraphs 2--5; Tag 075S(2),(3)
(blueprint: lem-sfb-stack-affine-source-nerve-geometry).

Proof:
1. Use lem-sfb-algebraic-stack-change-base-to-integers to work absolutely.
By lem-weil-pbc-morphism-into-affine-scheme and
lem-weil-pbc-fibre-product-affine-spectra, Q = V ×_T V is affine.
By lem-weil-pbc-affine-scheme-qcqs, V, T and Q are qcqs; the projections
Q → V and V → T are separated by lem-weil-pbc-affine-source-morphism-separated.
2. R = V ×_A V is the base change of the relative diagonal of h along
Q → A ×_T A. The pair-and-isomorphism description of the existing 2-fibre
product identifies this square. By def-sfb-stack-qcqs-morphism, R → Q is
qcqs and R is an algebraic space. Thus R is quasi-compact and, by
lem-sfb-space-qcqs-source-products, absolutely quasi-separated.
3. Write the term in degree p as p copies of R fibred over V using consecutive
projections, with W_0 = V. Consecutive isomorphisms compose to identify this
with the iterated 2-product. This includes our identity-base-change
presentation in degree zero. By lem-trf-space-fibre-products-etale-covers
and lem-sfb-space-qcqs-source-products, induction makes each term a qcqs space.
4. By lem-sfb-algebraic-stack-qcqs-permanence each term maps qcqs to T.
The space and stack conventions agree: the diagonal of a sheaf is mono,
and its own diagonal is an isomorphism. An etale atlas is smooth by
lem-weil-pbc-etale-smooth-zero-dimensional-fibres. No smoothness or
surjectivity of a is used.
5. If A is a space, its diagonal is representable by schemes, so R is a
scheme. The recursion consists of scheme fibre products (def-pc-fibre-product),
and all terms are schemes.
6. If A is a scheme, R → Q is a base change of its diagonal, an immersion
by lem-weil-pbc-diagonal-immersion and lem-weil-pbc-immersion-base-change-lft.
Its composites to V are separated by lem-trf-immersion-over-separated-base.
Induction using lem-weil-pbc-separated-base-change and the separated
composition clause of lem-weil-pbc-proper-fp-permanence shows W_p → T
is separated, that is, its relative diagonal is a closed immersion.
7. If A → T is separated, its diagonal is closed, so R → Q is closed by
lem-weil-pbc-closed-immersion-base-change. By def-weil-closed-immersion,
R is affine. The affine fibre-product formula inductively makes all terms
affine. The degree-zero term represents V; empty schemes, including the
spectrum of the zero ring, satisfy the same arguments. -/
theorem stack_affine_source_nerve_geometry {S : Scheme.{u}}
    (T V : Over S) [IsAffine T.left] [IsAffine V.left]
    (A : BasedCategory.{v, w} (Over S)) (hA : IsAlgebraicModuliStack A)
    (h : BasedFunctor A (discreteModuli (yoneda.obj T)))
    (hhqc : IsQuasiCompactAlgebraicModuliMap.{u, v, w, u, u + 1, t, s} h)
    (hhqs : IsQuasiSeparatedAlgebraicModuliMap h)
    (a : BasedFunctor (discreteModuli (yoneda.obj V)) A) (p : ℕ) :
    (∃ (Z : AlgebraicSpace S)
        (e : BasedFunctor (discreteModuli Z.obj.obj) (stackAffineSourceNerve a p).1),
      e.toFunctor.IsEquivalence) ∧
    IsQuasiCompactAlgebraicModuliMap.{u, max u v, max (u + 1) v w, u, u + 1, t, s}
      ((stackAffineSourceNerve a p).2.comp h) ∧
    IsQuasiSeparatedAlgebraicModuliMap ((stackAffineSourceNerve a p).2.comp h) ∧
    ((∃ (Z : AlgebraicSpace S) (e : BasedFunctor (discreteModuli Z.obj.obj) A),
        e.toFunctor.IsEquivalence) →
      ∃ W : Over S, IsRepresentedByScheme (stackAffineSourceNerve a p).1 W) ∧
    (∀ (B : Over S) (e : BasedFunctor (discreteModuli (yoneda.obj B)) A),
      e.toFunctor.IsEquivalence → ∀ b : B ⟶ T,
      Nonempty (ModuliTwoIso (e.comp h) (discreteModuliMap (yoneda.map b))) →
      ∃ (W : Over S) (q : W ⟶ T)
          (f : BasedFunctor (discreteModuli (yoneda.obj W))
            (stackAffineSourceNerve a p).1),
        f.toFunctor.IsEquivalence ∧
        Nonempty (ModuliTwoIso (f.comp ((stackAffineSourceNerve a p).2.comp h))
          (discreteModuliMap (yoneda.map q))) ∧
        IsClosedImmersion (pullback.diagonal q.left) ∧
        (IsSeparated b.left → IsAffine W.left)) := by
  sorry

end CategoryTheory
