module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.AbelianAffineReducedCoproduct

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality

/-! # Injectivity of the degree-two reduced coproduct

Source: the agent-stated coherent analogue of Milne, Abelian Varieties, I, calculation (3)
before Lemma 12.2, printed p.55; arbitrary-module argument in the DAG proof
(blueprint: lem-sfb-abelian-h2-reduced-coproduct-injective).

The relative coherent exterior-algebra and coefficient Kunneth prerequisites in the DAG
supply the reduction to the split antisymmetrization map. This is not a quotation of an
unread proposition of Mumford--Fogarty--Kirwan.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- For every affine base change and every base module, the reduced coproduct in H2 is
injective. The map uses actual addition, the two projections, and canonical coefficient
identifications, on the underlying additive sheaf on the small etale site.

Source: Milne, Abelian Varieties, I, calculation (3) before Lemma 12.2, printed p.55,
adapted to coherent cohomology by the following explicit prerequisites and argument
(blueprint: lem-sfb-abelian-h2-reduced-coproduct-injective).

Proof:
1. Smoothness gives flatness on charts by lem-pc-smooth-flat. By
lem-sfb-space-flat-proper-fp-locality, B=A times_S T is flat, proper and finitely presented.
Apply lem-sfb-abelian-coherent-exterior-base-change: H0(B,O)=R, V=H1(B,O) is finite projective,
and cup product gives H^i(B,O)=exterior^i V. These modules are finite projective and vanish
in sufficiently high degrees. Thus lem-sfb-projective-cohomology-coefficient-kunneth applies.
2. Its coefficient-R case identifies H1(C,O)=V direct-sum V and
H2(C,O)=H2(B,O) direct-sum (V tensor_R V) direct-sum H2(B,O), by the external cup maps.
Pullback along b to (b,0) and b to (0,b) gives the two H1 coordinates: the cross terms
factor through affine T, whose H1(O) vanishes by lem-sc-etale-affine-qcoherent.
The group identities imply m-star(v)=p1-star(v)+p2-star(v).
3. Multiplicativity and the signed Kunneth multiplication show that the mixed component
of D(u cup v) is u tensor v minus v tensor u. The exterior-cohomology identification and
the coefficient comparisons commute with all three pullbacks. For arbitrary N the mixed
component is therefore delta_N:(exterior^2 V) tensor_R N to (V tensor_R V) tensor_R N,
sending (u wedge v) tensor n to (u tensor v minus v tensor u) tensor n. N occurs once.
4. Localize on a finite principal-open cover where V has an ordered basis e_i. The elements
(e_i wedge e_j) tensor n_ij with i<j give unique coordinates. In delta_N's image the
coefficient at e_i tensor e_j is n_ij, so delta_N is injective over each such open,
including characteristic two and nonflat N. If an element vanishes on this finite cover,
some powers of the covering elements annihilate it; those powers generate the unit ideal,
so it is zero globally. A class killed by D has zero mixed component, hence is zero by
the coefficient comparison. The cases rank(V)<2, N=0 and R=0 are included.
-/
theorem abelian_h2_reduced_coproduct_injective
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (A : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (hA : Poincare.IsAbelianFamily (groupSpaceProjection A))
    (R : Type u) [CommRing R] (t : Spec (.of R) ⟶ S) (N : ModuleCat.{u} R) :
    Function.Injective
      (ReducedCoproduct.map A g (Over.mk t) hA R (Iso.refl _) N) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
