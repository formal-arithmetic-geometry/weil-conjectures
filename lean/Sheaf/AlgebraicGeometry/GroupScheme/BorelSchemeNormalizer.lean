module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Mathlib.AlgebraicGeometry.Group.Affine
import Sheaf.AlgebraicGeometry.GroupScheme.TorusCentralizerBorelIntersection
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothGroupOrbitGeometry
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Sheaf.AlgebraicGeometry.PerfectSolvableUnipotentTorus
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.ProperReducedGlobalSectionsProduct
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # The scheme-theoretic normalizer of a Borel subgroup

Source: Milne, Algebraic Groups (2017), Theorem 17.48, printed p.367, with
Lemma 17.47, printed p.366. (blueprint: lem-sfb-borel-scheme-normalizer)

The normalizing condition is tested after every algebra extension. The conclusion
identifies its points with the image of the closed Borel embedding on every algebra.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped MonObj

namespace AlgebraicGeometry

/-- A Borel subgroup equals its scheme-theoretic normalizer, including on nonreduced
test algebras. The two ranges in the hypothesis are respectively the conjugate of
the Borel's points and the Borel's points after the indicated algebra extension.
Source: Milne, Theorem 17.48 and Lemma 17.47, printed pp.366--367.
(blueprint: lem-sfb-borel-scheme-normalizer)

Proof plan:
1. Use strong induction on dim G, simultaneously for all smooth connected affine
   groups and their Borels. The case B = G is immediate. Choose a maximal torus T
   in B, maximal in G by lem-sfb-borel-maximal-torus-conjugacy. By
   lem-sfb-maximal-torus-centralizer-borel its centralizer lies in B; hence
   lem-sfb-cartan-containing-normalizer-smooth represents the normalizer by a
   smooth closed finite-type subgroup N. It suffices first to prove N(F) ⊆ B(F).
2. For x in N(F), conjugate xTx⁻¹ back to T by an element of B(F), using
   lem-sfb-borel-maximal-torus-conjugacy inside B. Replacing x by bx preserves
   the desired membership. Now φ(t) = xtx⁻¹t⁻¹ is a homomorphism T → T,
   since both factors have values in the commutative torus after every extension.
3. By lem-sfb-torus-endomorphism-kernel-dichotomy, either φ is faithfully flat,
   or its kernel contains a positive-dimensional split torus S. In the latter case
   x centralizes S. The centralizer C is smooth connected by
   lem-sfb-torus-centralizer-smooth-connected; D = C ∩ B is a Borel of C by
   lem-sfb-torus-centralizer-borel-intersection. Conjugation by x preserves D.
4. If C ≠ G, G is integral by lem-sfb-borel-quotient-proper-geometry applied to
   its identity quotient. Smoothness makes C reduced by
   sbc-lem-smooth-geometrically-reduced, so C is a proper closed subset of G.
   By lem-wf-affine-dimension-drop it has smaller dimension. Induction for (C,D)
   gives x ∈ D(F) ⊆ B(F).
5. If C = G, S is central. Use lem-sfb-affine-normal-quotient-geometry to form
   J = G/S and lem-sfb-quotient-borel-torus-images to get its Borel E = q(B).
   The map B → E is faithfully flat and q⁻¹(E) = B: locally lift to B, then the
   ratio lies in S ⊆ B, and closed-subgroup membership descends faithfully flatly.
   Apply lem-sfb-smooth-group-orbit-geometry to the translation action on J:
   the stabilizer is S, so dim J = dim G - dim S < dim G. The image q(x)
   normalizes E, as checked after local lifts to B. Induction gives q(x) ∈ E(F),
   hence x ∈ B(F).
6. In the faithfully flat case, lem-sfb-chevalley-scheme-line-stabilizer gives a
   representation V with a line Fv whose stabilizer is N. Its character χ on N
   kills every commutator [x,t]. Faithful flatness of φ implies χ restricted to T
   is trivial, so T fixes v. This character is on N, not an assumed character of G.
7. By lem-sfb-perfect-solvable-unipotent-torus and
   lem-sfb-solvable-torus-complements write B = U ⋅ T on every test algebra:
   for b take t with the same image in B/U and put u = bt⁻¹. By
   lem-sfb-unipotent-to-multiplicative-trivial, χ kills U. Thus B fixes v.
8. Form the fpqc quotient Q = G/B by lem-sfb-algebraic-group-homogeneous-quotient.
   It is proper and geometrically integral by lem-sfb-borel-quotient-proper-geometry.
   The orbit map g ↦ gv agrees on the kernel pair since B fixes v, so descends
   to Q by lem-weil-pbc-fpqc-representable-descent. By
   lem-weil-pbc-proper-reduced-algclosed-global-sections-product, Γ(Q,O) = F.
   Each coordinate of Q → V is therefore constant with value at the identity coset.
   Hence G fixes v as a scheme, so stabilizes the line, giving G = N.
9. Thus B is normal. The quotient G/B is affine by
   lem-sfb-affine-normal-quotient-geometry, agreeing with Q by local lifts and
   fpqc representable descent. Since Γ(Q,O) = F, Q = Spec F, and the kernel
   identity gives G = B. This closes the faithfully flat branch, completing the
   strong induction, including dimension zero.
10. The ideal cutting out B in the affine finite-type N vanishes at all F-points.
    Smoothness makes N reduced by sbc-lem-smooth-geometrically-reduced; hence
    lem-wf-affine-nullstellensatz-vanishing makes that ideal zero. Thus N = B
    as schemes, giving the forward implication on every test algebra. Conversely,
    a B-point normalizes B after every extension by its group laws, proving the
    displayed equivalence. -/
theorem borelGroupScheme_normalizer_iff {F : Type u} [Field F] [IsAlgClosed F]
    (G B : Over (Spec (.of F))) [GrpObj G] [GrpObj B]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] [ConnectedSpace G.left]
    (i : B ⟶ G) (hB : IsBorelGroupScheme i)
    (A : CommAlgCat.{u} F) (g : (algSpec (.of F)).obj (op A) ⟶ G) :
    (∀ (A' : CommAlgCat.{u} F) (f : A ⟶ A'),
      Set.range (fun b : (algSpec (.of F)).obj (op A') ⟶ B ↦
        ((algSpec (.of F)).map f.op ≫ g) * (b ≫ i) *
          ((algSpec (.of F)).map f.op ≫ g)⁻¹) =
        Set.range (fun b : (algSpec (.of F)).obj (op A') ⟶ B ↦ b ≫ i)) ↔
      ∃ b : (algSpec (.of F)).obj (op A) ⟶ B, b ≫ i = g := by
  sorry

end AlgebraicGeometry
