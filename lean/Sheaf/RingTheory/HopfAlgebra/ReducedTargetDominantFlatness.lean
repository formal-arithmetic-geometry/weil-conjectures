module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import WeilConjectures.AlgebraicGeometry.GenericFlatness

/-! # Faithful flatness of a Hopf inclusion with reduced source algebra

Source: Milne, Algebraic Groups (2017), Corollary 1.69 and Proposition 1.70,
printed p. 28; Proposition 1.65(a), printed pp. 26--27; Theorem 3.31, printed p. 73.
(blueprint: lem-sfb-reduced-target-dominant-group-flatness)
-/

@[expose] public section

universe u v w

namespace HopfAlgebra

/-- An injective homomorphism between finite type commutative Hopf algebras over an
algebraically closed field is faithfully flat when its source algebra is reduced.
The source algebra is the coordinate ring of the target group scheme. The three
compatibility equations express precisely that `i` is a Hopf homomorphism.

Source: Milne, Algebraic Groups (2017), Corollary 1.69 and Proposition 1.70,
printed p. 28; Proposition 1.65(a), printed pp. 26--27; Theorem 3.31, printed p. 73.
(blueprint: lem-sfb-reduced-target-dominant-group-flatness)

Proof plan:
1. Form the group schemes G = Spec B and H = Spec A and their homomorphism f,
   using lem-sfb-hopf-spectrum-functor. Counits give nonempty schemes. Algebra
   generators make f finite type (def-weil-finite-type-morphism and
   lem-weil-pbc-affine-scheme-qcqs), and H is reduced by
   lem-weil-pbc-affine-scheme-reduced-iff.
2. Injectivity survives localization: if r/a^n maps to zero, some i(a)^m i(r)
   vanishes, so a^m r = 0 and r/a^n = 0. The sheaf kernel is therefore zero.
   Apply lemma-nagata-scheme-image-ideal-qc and def-weil-affine-spectrum to see
   that f has dense image. This does not require B reduced.
3. By lem-wf-affine-constructible-open the image is constructible and contains
   a nonempty open U of H. The Jacobson property
   (lem-sc-lft-over-field-jacobson-space) and the Nullstellensatz
   (lem-wf-affine-nullstellensatz-vanishing) detect nonempty locally closed
   subsets by k-points. Every k-point of the image lifts to G(k): extend a prime
   over its maximal ideal to a maximal ideal of B and use the Nullstellensatz;
   contraction is still the same maximal ideal. Thus U(k) lies in the subgroup
   S = f(G(k)) of H(k).
4. The union V of the translates sU for s in S is a nonempty open with V(k) = S:
   for u in U(k), write s = (s u^-1)u. A point in the constructible set f(G) minus V
   would yield a closed k-point and hence a lift, a contradiction. Thus V contains
   f(G) and is dense. If y is a k-point outside S, V meets yV in a nonempty open,
   hence in a k-point, contradicting disjointness of S and yS. Thus S = H(k).
   Translation and the subgroup laws are those of def-sc-group-scheme.
5. The constructible complement of f(G), if nonempty, contains a closed k-point,
   contrary to Step 4. Therefore f is surjective on all points.
6. By lem-wf-affine-noetherian-components there are finitely many components of H.
   Remove all but one to obtain a nonempty irreducible open W. It is reduced
   (def-pc-reduced-scheme), hence integral (def-pc-integral-scheme).
   Restriction preserves finite type by lem-sfb-finite-type-composition-base-change.
   Apply lem-sbc-generic-flatness over W to find a nonempty open U0 where f is flat.
7. Choose u in U0(k). For every h in H(k), choose g in G(k) with f(g) = h u^-1.
   Translation intertwines f and identifies its restriction over f(g)U0 with
   the flat restriction over U0. Conjugating local ring maps by ring isomorphisms
   preserves flatness (def-weil-flat-morphism). These opens cover H(k), hence H,
   since a nonempty closed complement would have a closed k-point. So f is flat,
   without reducedness of G.
8. By lem-weil-pbc-flat-morphism-affine-criterion, i is flat. Its spectrum map is
   surjective by Step 5, so lem-weil-pbc-flat-surjective-spectrum-faithfully-flat
   gives faithful flatness as in def-weil-pbc-faithfully-flat-ring-map. No
   connectedness, smoothness, characteristic, or reducedness of B was used.
-/
theorem faithfullyFlat_of_injective_of_isReduced
    (k : Type u) (A : Type v) (B : Type w)
    [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B]
    (hA : (algebraMap k A).FiniteType) (hB : (algebraMap k B).FiniteType)
    [IsReduced A] (i : A →ₐ[k] B)
    (hcomul : (Bialgebra.comulAlgHom k B).comp i =
      (Algebra.TensorProduct.map i i).comp (Bialgebra.comulAlgHom k A))
    (hcounit : (Bialgebra.counitAlgHom k B).comp i = Bialgebra.counitAlgHom k A)
    (hantipode : (antipodeAlgHom k B).comp i = i.comp (antipodeAlgHom k A))
    (hi : Function.Injective i) : i.toRingHom.FaithfullyFlat := by
  sorry

end HopfAlgebra
