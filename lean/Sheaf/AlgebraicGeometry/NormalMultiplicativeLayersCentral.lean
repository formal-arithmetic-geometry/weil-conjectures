module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.ConnectedPointGeometricallyConnected
import Sheaf.AlgebraicGeometry.CommutativeMultiplicativeTypeExtension

/-! # Normal multiplicative-type layers are central

Source: Milne, Algebraic Groups (2017), Lemma 16.43, printed p.340;
Corollaries 12.38 and 12.41, p.244, with the central-kernel Chapter 12 correction;
Corollary 12.22, p.239 (blueprint: lem-sfb-normal-multiplicative-layers-central).

The centre condition uses the recorded universal centralizer of the identity of G,
and therefore tests commutation after every algebra extension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If N and E are closed normal subgroups of a connected affine algebraic group G,
and N and the represented fppf quotient E/N are of multiplicative type, then E is
of multiplicative type and lies in the scheme-theoretic centre of G.

Source: Milne, Algebraic Groups (2017), Lemma 16.43, printed p.340; Corollaries
12.38 and 12.41, p.244, with the central-kernel Chapter 12 correction, and
Corollary 12.22, p.239 (blueprint: lem-sfb-normal-multiplicative-layers-central).

Proof plan (the eight steps of the node):
1. The quotient hypothesis makes q flat and surjective with kernel N. On affine
   coordinates, lem-weil-pbc-flat-ring-map-iff-flat-affine and
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat make k[Q] -> k[E]
   faithfully flat. The affine fibre-product formula and
   lem-weil-pbc-faithfully-flat-base-change, together with
   lem-weil-pbc-faithfully-flat-surjective-spectrum, show that every affine
   pullback of q is flat and surjective. Thus q is an fpqc cover in
   def-weil-pbc-fpqc-covering. The fpqc covering axioms give its products,
   pullbacks and composites, including the two-copy product cover.
2. Pass to F = algebraic closure of k using def-pc-base-change. The identity
   point of G has residue field k, so lem-trf-connected-point-geometrically-connected
   makes G_F connected. Affine coordinates become F tensor k[H]; the same
   generators give finite type and tensor preserves the surjections giving the
   closed inclusions. Group operations, normality and the kernel pull back.
   The quotient remains an fpqc cover. By the multiplicative-type hypotheses
   and lem-sfb-split-torus-subgroups-diagonalizable, N_F and Q_F are D(M) for
   finitely generated abelian character groups. Suppress F in steps 3--7.
3. Normality restricts conjugation to a morphism G times N -> N, a family of
   group homomorphisms equal to the identity at 1_G. Apply
   lem-sfb-diagonalizable-hom-family-rigidity with connected parameter G and
   source and target N. Hence N is central in G and in E. This establishes the
   central-kernel condition of the corrected Corollary 12.41 before using it.
4. Write a(g,e) = geg^{-1}. Normality of E and N allows q composed with a to
   descend along 1_G times q. The overlap has lifts e and en for n in N;
   q(a(g,en)) = q(a(g,e)), since a(g,n) is in N. By
   lem-weil-pbc-fpqc-representable-descent obtain b : G times Q -> Q.
   After the product cover, the multiplication, identity and b(1,t) = t
   identities are those of conjugation. Uniqueness in descent proves them
   before the cover. Family rigidity for Q -> Q then gives b(g,t) = t,
   hence q(a(g,e)) = q(e).
5. The difference c(g,e) = a(g,e)e^{-1} factors through the kernel N by step 4.
   Step 3 gives c(g,en) = c(g,e), so the same descent yields d : G times Q -> N.
   Centrality of N in E gives
   c(g,ee') = c(g,e)e c(g,e')e^{-1} = c(g,e)c(g,e').
   Also c(g,1) = 1. Pull back along the two-copy product cover and use uniqueness
   in descent to prove that d(g,-) is a homomorphism, with d(1,-) = 1.
6. Apply family rigidity for Q -> N at the identity parameter. It gives d = 1,
   hence a(g,e) = e. These equalities hold on every algebra, and so are morphism
   identities by evaluation at the affine source's coordinate algebra. Thus E
   is central over F, and in particular is commutative.
7. Apply lem-sfb-commutative-multiplicative-type-extension to q: its coordinate
   map is faithfully flat, its kernel and quotient are diagonalizable, and E
   is commutative. Obtain E = D(M), M finitely generated abelian. Choose r
   generators of M. Sending Laurent variables to their group-like elements
   gives a surjective Hopf map F[t_1^{±1},...,t_r^{±1}] -> F[M]. Its spectrum
   is the required closed group immersion into the rank-r split torus. This
   is precisely MultiplicativeType.IsMultiplicativeType over the original k.
8. The conjugation G times E -> G and inclusion after projection agree over F.
   On affine coordinates their pullback differences vanish after tensoring
   with F. By lem-sfb-field-extension-tensor-injective they vanish over k.
   Evaluating the resulting morphism equality on every k-algebra and every
   algebra extension shows that each E-point lies in centralizerPoints of
   the identity of G. By lem-sfb-affine-group-centre-base-change this is exactly
   inclusion in Z(G), with its universal, scheme-theoretic meaning. -/
theorem normal_multiplicativeType_layers_central
    {k : Type u} [Field k]
    (G N E Q : Grp (Over (Spec (.of k))))
    (hG : SolvableGroupStructure.IsAlgebraic G)
    (hN : SolvableGroupStructure.IsAlgebraic N)
    (hE : SolvableGroupStructure.IsAlgebraic E)
    (hQ : SolvableGroupStructure.IsAlgebraic Q)
    (hconnected : ConnectedSpace G.X.left)
    (i : N ⟶ E) (j : E ⟶ G) (q : E ⟶ Q)
    (hi : IsClosedSubgroupScheme i.hom.hom)
    (hj : IsClosedSubgroupScheme j.hom.hom)
    (hNnormal : IsNormalSubgroupScheme (i ≫ j).hom.hom)
    (hEnormal : IsNormalSubgroupScheme j.hom.hom)
    (hq : SolvableGroupStructure.IsFppfQuotient i.hom.hom q)
    (hNmult : MultiplicativeType.IsMultiplicativeType N)
    (hQmult : MultiplicativeType.IsMultiplicativeType Q) :
    MultiplicativeType.IsMultiplicativeType E ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (e : StandardGroupSchemes.affine k A ⟶ E.X),
        e ≫ j.hom.hom ∈ ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A := by
  sorry

end AlgebraicGeometry
