module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.AbelianSpacePoincareData

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus

/-! # Relative dual abelian spaces and normalized Poincare calculus

Source: Milne, Abelian Varieties, I Sections 8--9; Deligne, Le lemme de Gabber,
Section 4.1, pp.141--142 (blueprint: lem-sfb-abelian-space-poincare-calculus).

The relative algebraic-space theorem is a statement-only prerequisite. Milne's
field theorem supplies the geometric fibres, not the relative assertion by itself.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

open Poincare

/-- A relative abelian space has a normalized universal dual, the two Poincare
identities, normalized difference homomorphisms, pullback dual homomorphisms,
and the canonical compatible comparisons after every locally Noetherian base change.
All scheme parameters in the representing property and the automorphism assertion
are allowed, including nonreduced parameters and lines outside the neutral component.

Source: Milne, Abelian Varieties, I Sections 8--9; Deligne, Le lemme de Gabber,
Section 4.1, pp.141--142 (blueprint: lem-sfb-abelian-space-poincare-calculus).

Proof plan:

1. On etale scheme charts smoothness gives flatness by [lem-pc-smooth-flat]. Each geometric
fibre is geometrically integral by [lem-sc-abelian-variety-characterization], applied to the
abelian variety in the hypothesis. Thus [lem-sfb-rigidified-space-picard] applies to A\to S with
section e_A, producing the separated locally finitely presented group space P of all rigidified
line modules, its universal module U, and \mathcal O_T\simeq(f_T)_*\mathcal O_{A_T} for every T.
It also proves the asserted automorphism statement for every rigidified line module, without
imposing algebraic triviality.

2. For an algebraically closed geometric residue field K, the fibre A_K is projective by
[lem-sc-abelian-variety-projective] and geometrically integral by
[lem-sc-abelian-variety-characterization]. The full Picard representation in
[lem-sfb-projective-picard-identity-representability] therefore identifies (P_K)^0 with the
functor of rigidified algebraically trivial families. The same functor is represented by the
smooth proper connected dual abelian variety in [lem-sfb-abelian-polarization-calculus]; hence
(P_K)^0 is smooth and proper. Given a square-zero lifting problem into P whose geometric images
are in these components, the universal module converts it into exactly the lifting problem of
[lem-sfb-abelian-picard-infinitesimal-lift]. Its etale-local lifts give lifts into P by
[lem-sfb-rigidified-space-picard]. Apply [lem-sfb-smooth-group-proper-neutral] to obtain D=P^0,
proper smooth and finitely presented over S, with geometric fibres the field duals. Its functor
is precisely the fibrewise algebraically trivial rigidified families. Set A^\vee=D and \mathcal
P_A=U|_{A\times D}.

3. The universal rigidification trivializes \mathcal P_A on e_A\times D. The zero of D
represents the trivial rigidified module, so representability gives the trivialization on
A\times e_D whose value at (e_A,e_D) is the prescribed one. Any two rigidification-preserving
isomorphisms of a family differ by an automorphism, which is the identity by
[lem-sfb-rigidified-space-picard]. On a product of copies of A and D, every global unit comes
from the base. The space D\to S of step 2 is flat on etale scheme charts by
[lem-pc-smooth-flat], and its geometric fibres, being abelian varieties, are geometrically
integral by [lem-sc-abelian-variety-characterization]; with its zero section,
[lem-sfb-rigidified-space-picard] therefore applies to D as well as to A. Apply its universal
structure-sheaf pushforward assertion successively to the projections, which are base changes of
A or D along a product of the others; when that product is an algebraic space, apply it on an
etale scheme chart and glue, since global units form an etale sheaf. Thus an automorphism of the
trivial line on an identity axis is fixed by its value on the remaining identity section.
Consequently an isomorphism normalized on one axis, if it exists and respects the other at their
intersection, respects that whole axis. Its restriction there is such a unit, and its identity
value makes it 1.

4. For L on A form N_L exactly as in the statement. Pulling to either identity axis cancels L
with L^{-1} and e^*L with its dual, giving the two canonical trivializations. On a geometric
fibre, the family parameterized by the connected smooth variety A_K connects the fibre at any
point to its trivial fibre at the identity. Thus every parameter fibre is algebraically trivial,
by the stated definition. The representing property of [lem-sfb-rigidified-space-picard] and the
subfunctor description in [lem-sfb-smooth-group-proper-neutral] give \phi_L:A\to D and the
normalized isomorphism N_L\simeq(1\times\phi_L)^*\mathcal P_A. The zero parameter gives
\phi_L(0)=0. Now [lem-sfb-relative-abelian-pointed-rigidity] makes \phi_L a group homomorphism.
The fibre description is the class of t_x^*L\otimes L^{-1} with the identity-line normalization
in N_L; the displayed shorthand does not omit that normalization.

5. Apply the difference construction of step 4 to the universal module in the A variable. It
defines F:A\times D\to D: its value at (y,z) is the rigidified translated difference of \mathcal
P_{A,z}. Existence as a morphism follows from [lem-sfb-rigidified-space-picard] and
[lem-sfb-smooth-group-proper-neutral], since on every geometric fibre the translation parameter
in the connected smooth variety A_K connects this difference to zero. Both F(0,z) and F(y,0) are
zero, by the normalizations. The product assertion of
[lem-sfb-relative-abelian-pointed-rigidity] gives F=0 as a morphism, including over a nonreduced
base. The representing property now identifies its rigidified family with the trivial family.
Undoing the definition of the difference gives (m_A,1)^*\mathcal P_A\simeq p_{13}^*\mathcal
P_A\otimes p_{23}^*\mathcal P_A. For the second identity, addition in D\subset P is tensor
product, so (1,m_D)^*\mathcal P_A and p_{12}^*\mathcal P_A\otimes p_{13}^*\mathcal P_A represent
the same family. The uniqueness from step 3 makes both isomorphisms preserve all identity axes.

6. For a:A\to B, pull a rigidified family on B back by a\times1. Since a(0)=0, rigidification
pulls back. Pulling back every family in a chain defining algebraic equivalence preserves that
chain, and tensor products are preserved. Thus the representing property of
[lem-sfb-rigidified-space-picard], with the neutral subfunctor of
[lem-sfb-smooth-group-proper-neutral], yields the homomorphism a^\vee:B^\vee\to A^\vee. The two
pullbacks of universal modules in the statement classify this same rigidified family, so their
unique normalized isomorphism gives the desired comparison. Finally for S'\to S, a rigidified
family on A_{S'}\times_{S'}T is exactly one on A\times_ST; algebraic triviality is tested on the
same geometric fibres. Base change for the Picard representation and the neutral subfunctor
therefore identifies D_{S'} with the dual for A_{S'}. Universal modules, their axes and the
difference construction pull back by their explicit formulas. Each comparison is characterized
by the rigidified family it represents. Identity and either composite comparison represent the
same family, and uniqueness in [lem-sfb-rigidified-space-picard] makes them equal, proving all
the asserted coherences.
-/
theorem abelianSpace_poincare_calculus
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (A : AlgebraicSpace S) (g : CommutativeSpaceGroup A)
    (hA : IsAbelianFamily (groupSpaceProjection A)) :
    ∃ (D : AlgebraicSpace S) (h : CommutativeSpaceGroup D)
      (P : (product (groupSpaceProjection A) (groupSpaceProjection D)).SmallModules)
      (r : Axes (pointedGroup A g) (pointedGroup D h) P),
      IsAbelianFamily (groupSpaceProjection D) ∧
      Represents (pointedGroup A g) (pointedGroup D h) P r ∧
      RigidAutomorphisms (pointedGroup A g) ∧
      Biadditive A D g h P ∧ DifferenceHomomorphisms A D g h P ∧
      DualHomomorphisms A D g h P ∧
      UniversalBaseChange (pointedGroup A g) (pointedGroup D h) P r ∧
      ComparisonCoherence (pointedGroup A g) (pointedGroup D h) P r := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
