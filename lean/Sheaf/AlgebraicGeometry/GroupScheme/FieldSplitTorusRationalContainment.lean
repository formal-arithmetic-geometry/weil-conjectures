module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Rational containment of a split-torus homomorphism

Source: Milne, Algebraic Groups (2017), Theorem 25.10, p.546, Theorem 12.9(b),(c),
pp.233--234, and Definition 12.14, p.236
(blueprint: lem-sfb-field-split-torus-rational-containment).

Maximality is among closed split tori over the original field. The conclusion is an
identity of morphisms, using the group law on morphisms into a group object, and hence
holds after every commutative algebra extension, including nonreduced test algebras.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Every homomorphism from a split torus to a reductive group over an arbitrary field
is conjugate by a rational point into any prescribed maximal split torus. Neither the
homomorphism is assumed injective nor its kernel smooth.

Source: Milne, Algebraic Groups (2017), Theorem 25.10, p.546, Theorem 12.9(b),(c),
pp.233--234, and Definition 12.14, p.236
(blueprint: lem-sfb-field-split-torus-rational-containment).

Proof plan:
1. Choose the split presentation of D. Its affine finite-type coordinates are supplied
   by lem-trf-lattice-torus-coordinates-action. Apply
   lem-sfb-affine-homomorphism-flat-image to factor f as a faithfully flat map D -> I
   followed by a closed immersion I -> G. By lem-sfb-field-split-torus-flat-quotient,
   I is a split torus over k, with any inseparable kernel retained.
2. By lem-kun-dimension-finite-type, G has finite dimension. Every closed split torus
   R in G has domain coordinate ring k[Z^r], by lem-trf-lattice-torus-coordinates-action
   and lem-trf-split-lattice-torus-projection. Thus R is nonempty and irreducible, and
   its dimension is bounded above by that of G (def-kun-dimension).
3. Choose among the closed split tori containing I one, M, of greatest dimension.
   If M is strictly contained in a split torus R, the closed immersion M -> R is
   defined by an ideal J in the domain k[R] (def-weil-closed-immersion). Equality of
   their underlying spaces would force J into the zero prime, hence J = 0. Otherwise
   append R to a longest irreducible closed chain in M: dim R > dim M, a contradiction.
   Therefore M is maximal split and contains I.
4. Apply lem-sfb-field-maximal-split-tori-conjugacy to M and S. It gives g in G(k)
   whose conjugation restricts to a group-scheme isomorphism M -> S.
5. Compose D -> I -> M with that isomorphism to obtain v. The group-object identities
   of def-sc-group-scheme give the displayed morphism equality. Evaluation on any
   algebra B gives g_B*f_B(x)*g_B^(-1) = i_B(v_B(x)); surjectivity on B-points is
   unnecessary. For trivial f, including rank-zero D, take g = 1 and trivial v.
   The argument imposes no perfection, infinitude, or algebraic-closedness assumption. -/
theorem field_split_torus_rational_containment
    {k : Type u} [Field k] (G S D : Grp (Over (Spec (.of k))))
    (_hG : ReductiveTorusCentralizer.IsReductive G)
    (i : S ⟶ G) [IsClosedImmersion i.hom.hom.left]
    (_hS : ∃ r : ℕ, Nonempty (S ≅ MultiplicativeType.splitTorus k r))
    (_hmax : ∀ (T : Grp (Over (Spec (.of k)))) (j : T ⟶ G),
      IsClosedImmersion j.hom.hom.left →
        (∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)) →
          ∀ a : S ⟶ T, a ≫ j = i → IsIso a)
    (_hD : ∃ s : ℕ, Nonempty (D ≅ MultiplicativeType.splitTorus k s))
    (f : D ⟶ G) :
    ∃ (g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) (v : D ⟶ S),
      (toUnit D.X ≫ g) * f.hom.hom * (toUnit D.X ≫ g)⁻¹ = v.hom.hom ≫ i.hom.hom := by
  sorry

end AlgebraicGeometry
