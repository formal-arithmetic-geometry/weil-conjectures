module

public import Sheaf.AlgebraicGeometry.GroupScheme.RelativeReductiveQuotientTerminology
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.Connected.Basic

import Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Relative quotients by central subgroups of multiplicative type

Source: Conrad, Reductive group schemes, Lemmas 3.3.1(2), 3.3.2 and Corollary 3.3.5,
pp.96--101 (blueprint: lem-sfb-relative-central-multiplicative-quotient).

The conclusion uses the represented fppf quotient with its kernel and torsor formula.
The same centre maps and quotient map are pulled back along every base morphism.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.RelativeReductive

/-- Quotient by a closed central subgroup of multiplicative type, retaining the centres,
the torus correspondence, and arbitrary scheme base change, including nonreduced bases.
No smoothness assumption on C and no residue-characteristic condition is made.

Source: Conrad, Lemmas 3.3.1(2), 3.3.2 and Corollary 3.3.5, pp.96--101
(blueprint: lem-sfb-relative-central-multiplicative-quotient).

Proof plan, following the eleven steps of the DAG node:
1. Centrality implies normality. Apply lem-sfb-relative-affine-multiplicative-quotient
   to represent G/C by a smooth affine finitely presented group with connected fibres.
   Apply lem-sfb-field-reductive-quotient on geometric fibres to obtain reductivity.
2. The torsor map is (g,c) ↦ (g,gc), with inverse (g,h) ↦ (g,g⁻¹h). The kernel condition
   puts g⁻¹h in C on all test schemes. The relative affine quotient input also supplies
   its compatibility with arbitrary base change.
3. By lem-sfb-relative-reductive-centre-weight-kernel, both centres are closed of
   multiplicative type and commute with base change. Apply
   lem-sfb-relative-central-multiplicative-preimage to p⁻¹Z(Q) to make it central.
   Conversely central points map to central points, since points of Q lift fppf locally.
   Thus p⁻¹Z(Q)=Z(G), and local lifts with kernel C identify Z(Q)=Z(G)/C.
4. Use lem-sfb-relative-torus-automorphism-fixed-group and the field theorem
   lem-sfb-reductive-torus-self-centralizer to identify C_G(T)=T on geometric fibres.
   By lem-a1-map-over-base-finite-presentation and
   lem-sfb-flat-geometric-fibre-open-criterion this is an equality over the base.
   Consequently Z(G), and hence C, lies in each maximal torus T; likewise for Q.
5. Split T and C fppf locally. The inclusion is dual to a character surjection M → N.
   By lem-sfb-relative-diagonalizable-character-duality its kernel L gives T/C=D(L).
   The input lem-weil-subgroup-finite-free-abelian-group-free makes L finite free.
   The quotient is a torus, its map to Q is monic by local lifts, and
   lem-sfb-affine-multiplicative-type-monomorphism-closed makes it closed.
   The same local lifts identify p⁻¹(T/C)=T scheme-theoretically.
6. The T/C-action on G has fixed group T, since T centralizes precisely itself.
   Apply lem-sfb-torus-equivariant-quotient-fixed-surjectivity to see that the
   centralizer of T/C in Q is T/C, hence T/C is maximal on every geometric fibre.
7. For a maximal torus U of Q, its conjugation action on G is well defined because
   ker p is central. The input lem-sfb-relative-torus-automorphism-fixed-group gives
   a smooth affine fixed group H with connected geometric fibres and reductive fibres.
8. Fixed-group surjectivity gives H/C → U surjective on geometric fibres; its kernel
   is trivial, so it is an isomorphism on fibres. The finite-presentation and flat
   geometric-fibre criteria of step 4 make it an isomorphism over S. Thus H=p⁻¹U.
9. Apply lem-sfb-relative-central-multiplicative-preimage to the map H → U and
   multiplicative subgroup U of itself: H is central in itself, hence commutative.
   It is of multiplicative type, smooth, with connected geometric fibres;
   lem-sfb-smooth-connected-multiplicative-torus therefore makes H a torus over S.
10. A torus containing H maps to a torus containing U and therefore has the same
    image U by maximality; taking inverse images gives that it equals H. The quotient
    and inverse-image constructions are consequently inverse on maximal tori.
11. Use the base-change clauses of the relative affine quotient, reductive centre,
    character-duality and torus fixed-group inputs. Quotient maps and their kernels,
    torsor formulas, centre maps and cartesian torus squares all pull back. Maximality
    is geometric and persists under arbitrary base change, without a Noetherian or
    reducedness requirement on the new base. -/
theorem relative_central_multiplicative_quotient
    (A : Type u) [CommRing A] [Nontrivial A] [IsNoetherianRing A]
    (G C : Grp (Over (Spec (.of A)))) (c : C ⟶ G)
    (hG : IsReductive G) (hc : IsClosedImmersion c.hom.hom.left)
    (hcentral : IsCentral c) (hC : IsMultiplicativeType C) :
    ∃ (Q : Grp (Over (Spec (.of A)))) (p : G ⟶ Q)
      (ZG ZQ : Grp (Over (Spec (.of A)))) (zG : ZG ⟶ G) (zQ : ZQ ⟶ Q)
      (cZ : C ⟶ ZG) (pZ : ZG ⟶ ZQ),
      cZ ≫ zG = c ∧ pZ ≫ zQ = zG ≫ p ∧
      IsReductive Q ∧ IsFppfGroupQuotient c p ∧
      Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      LocallyOfFinitePresentation p.hom.hom.left ∧ QuasiCompact p.hom.hom.left ∧
      IsCentre zG ∧ IsCentre zQ ∧ IsFppfGroupQuotient cZ pZ ∧
      HasMaximalTorusCorrespondence c p ∧
      ∀ (S' : Scheme.{u}) (f : S' ⟶ Spec (.of A)),
        IsReductive ((Over.pullback f).mapGrp.obj Q) ∧
        IsFppfGroupQuotient ((Over.pullback f).mapGrp.map c)
          ((Over.pullback f).mapGrp.map p) ∧
        Flat (((Over.pullback f).mapGrp.map p).hom.hom.left) ∧
        Surjective (((Over.pullback f).mapGrp.map p).hom.hom.left) ∧
        LocallyOfFinitePresentation (((Over.pullback f).mapGrp.map p).hom.hom.left) ∧
        QuasiCompact (((Over.pullback f).mapGrp.map p).hom.hom.left) ∧
        IsCentre ((Over.pullback f).mapGrp.map zG) ∧
        IsCentre ((Over.pullback f).mapGrp.map zQ) ∧
        IsFppfGroupQuotient ((Over.pullback f).mapGrp.map cZ)
          ((Over.pullback f).mapGrp.map pZ) ∧
        HasMaximalTorusCorrespondence ((Over.pullback f).mapGrp.map c)
          ((Over.pullback f).mapGrp.map p) := by
  sorry

end AlgebraicGeometry.RelativeReductive
