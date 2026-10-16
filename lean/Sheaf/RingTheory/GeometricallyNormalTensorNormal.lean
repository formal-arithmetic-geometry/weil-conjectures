/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.RingTheory.NormalRingIntegrallyClosedTotal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.CategoryTheory.Limits.HasLimits
import Sheaf.RingTheory.FilteredColimitNormalRing
import WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable
import WeilConjectures.FieldTheory.SeparableExtension
import Sheaf.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import Sheaf.RingTheory.SmoothNormalRing
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Sheaf.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Tensor products of geometrically normal and normal algebras

Source: Stacks Project, Algebra, Tag 06DF, lemma-geometrically-normal-tensor-normal
(blueprint: lem-weil-pbc-geometrically-normal-tensor-normal).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- If `A` is geometrically normal over a field `k` and `B` is normal, then
`A ⊗[k] B` is normal, with normality expressed at every prime localization.
Source: Stacks Project, Algebra, Tag 06DF, lemma-geometrically-normal-tensor-normal
(blueprint: lem-weil-pbc-geometrically-normal-tensor-normal).

Proof (the eleven steps of the DAG node):

1. We first record two elementary consequences of the normal-ring definition, to be used below. If
   R is normal and T is multiplicative, a prime Q of T^{-1}R contracts to a prime p of R disjoint
   from T, and (T^{-1}R)_Q = R_p: the mutually inverse fraction maps send (r/t)/(u/v) to rv/(tu),
   and r/s to (r/1)/(s/1). Thus T^{-1}R is normal. Also R is reduced: for a nonzero nilpotent x
   choose a maximal ideal p containing its proper annihilator. Then x/1 is nonzero in R_p
   (otherwise some s outside p annihilates x) and nilpotent, contradicting that R_p is a domain.
   These arguments include the zero ring, which has no primes.

2. Geometric normality is preserved by localization: for each extension E/k, the tensor product of
   a localization of A with E is the localization of A tensor E at the images of the same
   denominators, by [lem-weil-pbc-localization-base-change], applied with R=A, R'=T^{-1}A and D=A
   tensor_k E. The identification (A tensor_k E) tensor_A T^{-1}A = T^{-1}A tensor_k E sends (a
   tensor e) tensor(a'/t) to (aa'/t) tensor e; its inverse sends (a/t) tensor e to (1 tensor e)
   tensor(a/t). Bilinearity and the A-balancing relation verify that these maps are well-defined
   inverse ring maps. The swap sends a tensor e to e tensor a and is inverse to itself, by the
   tensor universal property. Step 1 gives normality of this localization. In particular A is
   normal by E=k, and every A_p is geometrically normal.

3. Fix a prime r of A tensor_k B, and let p and q be its contractions to A and B. The images of A
   minus p and B minus q avoid r. Apply the maps of Step 2 with E replaced by B, then interchange
   the factors and apply them with A replaced by B and E replaced by A_p. Twice applying [lem-
   weil-pbc-localization-base-change] therefore identifies A_p tensor_k B_q with the localization
   of A tensor_k B obtained by inverting these images. Localizing once more at the prime induced
   by r gives exactly (A tensor_k B)_r, by the fraction formulas in Step 1. A_p and B_q are normal
   domains by the hypotheses and Step 2, and A_p is geometrically normal. It therefore suffices to
   prove normality of A tensor_k B when A and B are normal domains and A is geometrically normal.
   If either original algebra is zero there is no r and the conclusion is vacuous. For the
   remainder of the proof A and B denote these domains; write K=Frac(A) and L=Frac(B).

4. For any finitely generated k-subalgebra D of B, apply [lem-fin-normalization-extension-finite]
   to X=Spec D and the degree-one extension Frac(D)/Frac(D). By [def-fin-normalization-extension]
   its source is Spec N, where N is the integral closure of D in Frac(D). The finite-morphism
   definition makes N finite as a D-module. By [lem-weil-pbc-integral-closure-algebraic-extension-
   normal], N is an integrally closed domain with fraction field Frac(D). Embed Frac(D) into L
   using D subset B. Every element of N is integral over D, hence over B by the same monic
   equation, and belongs to B by [lem-weil-pbc-normal-ring-integrally-closed-total] applied to the
   domain B. Thus N is a normal k-subalgebra of B containing D; normality of all its prime
   localizations follows from [lem-weil-pbc-localization-normal-domain]. It is finite type over k:
   if d_1,...,d_h generate D as a k-algebra and n_1,...,n_m generate N as a D-module, these
   elements together generate N as a k-algebra. Consequently the collection I of all normal
   finite-type k-subalgebras of B is nonempty, covers B, and is directed: for two members take D
   generated by the union of their finite generating sets and perform this construction. I is a
   set of subalgebras, hence a small directed poset after choosing the universe of k,A,B.

5. The inclusions A tensor_k B_i into A tensor_k B, for B_i in I, exhibit the latter as their
   filtered colimit of rings. Indeed tensoring an inclusion over k is injective by [lem-weil-pbc-
   module-over-field-flat] and the injectivity definition of flatness. Every tensor is a finite
   sum of pure tensors and all its B-coordinates lie in one B_i. For a compatible family of ring
   maps out of A tensor_k B_i, define its value on an element using any stage containing that
   element; a common upper stage proves independence, addition and multiplication, and uniqueness
   follows from the union. This proves the colimit universal property [def-weil-pbc-category-
   colimit]. By [lem-weil-pbc-filtered-colimit-normal-ring], it suffices to prove the domain case
   with B finite type over k. The rest of the proof establishes precisely that case; Step 11 then
   returns to the original algebras.

6. Assume henceforth that B is finite type. By Step 2, K is geometrically normal, so K tensor_k E
   is reduced for every field extension E/k by Step 1. If k has positive characteristic, apply
   [lem-weil-pbc-geometrically-reduced-extension-separable]; if k has characteristic zero, apply
   [lem-weil-pbc-char-zero-field-extension-separable]. In either case K/k is separable in the
   sense that every finitely generated intermediate field K_i/k is separably generated. These K_i
   form a small nonempty directed poset and their union is K: the subfield generated by the union
   of two finite sets contains the corresponding two intermediate fields.

7. For each K_i, [lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra] supplies a
   smooth k-subalgebra D_i of K_i with fraction field K_i. By [lem-weil-pbc-smooth-ring-map-base-
   change-composition], B tensor_k D_i is smooth over B. It is normal by [lem-weil-pbc-smooth-
   over-normal-ring-normal], since B is normal. The explicit maps of Step 2, with A=D_i and E=B,
   and the factor swap identify B tensor_k K_i with its localization at the nonzero elements of
   D_i, so Step 1 makes B tensor_k K_i normal. Swap factors to obtain normality of K_i tensor_k B.
   Field-flatness makes each K_i tensor_k B inject into K tensor_k B. Every element is a finite
   sum of pure tensors, whose finitely many K-coordinates lie in one K_i. Given compatible ring
   maps from these stages, evaluate an element at any stage containing it. A common larger
   intermediate field proves independence of the chosen stage and preservation of addition and
   multiplication; coverage proves uniqueness. This verifies that K tensor_k B is their filtered
   colimit. Thus [lem-weil-pbc-filtered-colimit-normal-ring] proves that K tensor_k B is normal.
   Independently, A tensor_k L is normal by the original geometric-normality hypothesis, since L/k
   is a field extension.

8. Put C=A tensor_k B, C_A=K tensor_k B and C_B=A tensor_k L. The maps C to C_A and C to C_B are
   injective: tensor the inclusions A subset K and B subset L over the field k, using the flatness
   statement and definition. They are localizations by [lem-weil-pbc-localization-base-change].
   Their inverted elements are nonzerodivisors of C: multiplication by any nonzero a in A, or b in
   B, is injective before tensoring and remains injective afterward. By Step 7, C_A and C_B are
   normal, hence reduced by Step 1; therefore their subring C is reduced. C_A is finite type over
   K, generated by the same finitely many B-generators, so it is Noetherian by [lem-weil-pbc-
   finite-type-algebra-noetherian] (a field has only two ideals). It has finitely many minimal
   primes by [lem-weil-pbc-noetherian-finitely-many-minimal-primes].

9. The map A to C is flat. For an injection of A-modules M to N, the identification M tensor_A C =
   M tensor_k B (m tensor(a tensor b) maps to am tensor b, with inverse m tensor b maps to m
   tensor(1 tensor b)) identifies the induced map with tensoring the underlying injection of
   k-vector spaces by B. This is injective by field-flatness. For a minimal prime r of C, going
   down [lem-sc-flat-going-down] applied to (0) subset r intersect A yields a prime r' subset r
   contracting to (0). Minimality forces r'=r. Hence every minimal prime of C avoids A minus zero.
   Such primes extend injectively to minimal primes of C_A: extension and contraction are inverse,
   since a fraction c/s belongs to the extended prime exactly when c belongs to the original
   prime; any prime strictly below the extended prime would contract to a strictly smaller prime
   of C. Thus C has finitely many minimal primes by Step 8.

10. Both C_A and C_B embed in Q(C), since their denominators are nonzerodivisors of C. Moreover
   Q(C_A)=Q(C)=Q(C_B): localizing at a subset of the nonzerodivisors preserves nonzerodivisors,
   and if c/s is a nonzerodivisor in this localization, c is already a nonzerodivisor in C, since
   localization at nonzerodivisors is injective. Also K tensor_k L embeds in Q(C), by inverting
   both sets of denominators. Inside this ring C_A intersect C_B=C. To check the equality, split
   K=A direct-sum U and L=B direct-sum V as k-vector spaces: choose a basis of K/A and lift it to
   K to obtain U, and do the same for L/B; vector-space bases exist by [lem-weil-pbc-module-over-
   field-flat]. Bilinearity gives K tensor L=(A tensor B) direct-sum (U tensor B) direct-sum (A
   tensor V) direct-sum (U tensor V); the projections to these four summands are induced by the
   projections of the split vector spaces. C_A comprises the first two summands and C_B the first
   and third, so their intersection is the first summand. Now let x in Q(C) be integral over C.
   Its monic equation is also a monic equation over C_A and C_B. By [lem-weil-pbc-normal-ring-
   integrally-closed-total] and Step 7, x belongs to both rings, hence to C. By [lem-weil-pbc-
   reduced-normal-iff-integrally-closed-total-fractions], reducedness and finiteness of the
   minimal primes from Steps 8 and 9 imply that C is normal.

11. Step 10 proves the normal-domain case for each finite-type normal B_i of Step 4, with the same
   geometrically normal A. Step 5 and the filtered-colimit normality theorem therefore prove the
   domain case for arbitrary B. Apply this domain case to A_p and B_q in Step 3 and then use the
   prime-localization calculation there: every (A tensor_k B)_r is an integrally closed domain.
   This is exactly normality of the original tensor product. No finite-type or Noetherian
   hypothesis survives the reductions, and no domain or nonzero hypothesis is imposed on the
   original A or B.
-/
theorem isNormal_tensorProduct_of_geometricallyNormal
    (k : Type u) (A : Type v) (B : Type w)
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (hA : ∀ (E : Type (max u v w)) [Field E] [Algebra k E],
      ∀ (p : Ideal (A ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hB : ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (r : Ideal (A ⊗[k] B)) [r.IsPrime],
      IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r) := by
  sorry

end Algebra
