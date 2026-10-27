module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import Sheaf.AlgebraicGeometry.GroupScheme.BorelConjugationCover
import Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousOrbitQuotientGeometry
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy

/-! # Borel stabilizers through a maximal torus

Source: Milne, Algebraic Groups (2017), Theorems 17.16 and 17.10, printed pp.354--356,
and the proof of Theorem 17.65, printed p.374.
(blueprint: lem-sfb-proper-homogeneous-torus-borel-stabilizer)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- A maximal torus fixing a point of a proper homogeneous space lies in a Borel
subgroup fixing that point on every commutative test algebra. The action is a
`ModObj`, so its unit and multiplication identities are part of its data. Over the
algebraically closed base the recorded torus predicate means a finite product of
the standard multiplicative group, including the rank-zero product.

Source: Milne, Theorems 17.16 and 17.10, printed pp.354--356, and the proof of
Theorem 17.65, printed p.374.
(blueprint: lem-sfb-proper-homogeneous-torus-borel-stabilizer)

Proof, following the five steps of the node:
1. Choose a Borel B by lem-sfb-borel-conjugation-cover. By
   lem-sfb-solvable-proper-fixed-point its restricted action on Y fixes z.
   Transitivity gives z = gy. The conjugate C = g⁻¹Bg is Borel and fixes y on
   every algebra: (g⁻¹bg)y = g⁻¹bz = y.
2. By lem-sfb-homogeneous-orbit-quotient-geometry the full stabilizer H of y is a
   closed subgroup, containing C and T. By
   lem-sfb-locally-algebraic-group-identity-component its reduced identity
   component K is smooth, connected and finite type. It is affine as a closed
   subgroup of G; H itself need not be smooth or reduced.
3. C is reduced by sbc-lem-smooth-geometrically-reduced. The coordinate ring of
   T is a domain by lem-trf-split-lattice-torus-projection, so T is reduced and
   connected. Their images contain the identity and factor through the open H⁰.
   Nilpotents pull back to zero on either reduced source; the nilradical quotient
   of def-weil-pbc-scheme-reduction gives closed subgroup factorizations into K.
4. By lem-sfb-borel-maximal-torus-conjugacy, C contains an ambient maximal torus
   S. Both S and T are maximal tori in K, since a larger torus there would be a
   larger torus in G. The same lemma applied to K supplies h in K(k) with
   hSh⁻¹ = T as subgroup schemes.
5. Put B₀ = hCh⁻¹. It is Borel and contains T. Since h and C fix y, on every
   algebra (hch⁻¹)y = hc(h⁻¹y) = hcy = hy = y. This proves both conclusions,
   including over nonreduced test algebras. -/
theorem exists_borel_stabilizer_containing_maximal_torus
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (Y : Over (Spec (.of k))) [ModObj G.X Y]
    [Smooth Y.hom] [ConnectedSpace Y.left] [IsProper Y.hom]
    (htrans : ∀ y₁ y₂ : 𝟙_ (Over (Spec (.of k))) ⟶ Y,
      ∃ g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X, g • y₁ = y₂)
    (T : Grp (Over (Spec (.of k)))) (iT : T ⟶ G)
    (hT : ReductiveTorusCentralizer.IsMaximalTorus iT)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (hy : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (t : StandardGroupSchemes.affine k A ⟶ T.X),
      (t ≫ iT.hom.hom) • (toUnit (StandardGroupSchemes.affine k A) ≫ y) =
        toUnit (StandardGroupSchemes.affine k A) ≫ y) :
    ∃ (B₀ : Grp (Over (Spec (.of k)))) (iB : B₀ ⟶ G),
      IsBorelGroupScheme iB.hom.hom ∧
      (∃ j : T ⟶ B₀, j ≫ iB = iT) ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (b : StandardGroupSchemes.affine k A ⟶ B₀.X),
        (b ≫ iB.hom.hom) • (toUnit (StandardGroupSchemes.affine k A) ≫ y) =
          toUnit (StandardGroupSchemes.affine k A) ≫ y := by
  sorry

end AlgebraicGeometry
