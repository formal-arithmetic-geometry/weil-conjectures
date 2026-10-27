module

public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Artinian.Module

/-! # Reductivity of the neutral component under a finite group cover

Source: Prasad--Yu, On quasi-reductive group schemes, Proposition 4.3, first
paragraph of proof, printed p.8; the finite-kernel specialization and the elementary
component restriction argument (blueprint: lem-sfb-finite-group-cover-reductive-neutral).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite surjective homomorphism from a smooth affine finite-type group restricts
on its neutral component to a finite surjective homomorphism onto the reductive reduced
neutral component of its target, and its neutral component is reductive.

The isomorphism e identifies H with the reduction of the canonical open identity
component of V; hi fixes its inclusion in V. Reduction commutes with restriction to
an open subscheme, so this is precisely (V_red)^0, with its induced subgroup structure.
There is no restriction on the finite kernel, including in positive characteristic.

Source: Prasad--Yu, On quasi-reductive group schemes, Proposition 4.3, first paragraph
of proof, printed p.8 (blueprint: lem-sfb-finite-group-cover-reductive-neutral).

Proof plan:
1. Apply lem-sfb-locally-algebraic-group-identity-component to U and V. Their neutral
   components are clopen, geometrically irreducible and finite type. Their closed
   immersions into affine schemes make them affine (def-weil-closed-immersion).
   Reduction commutes with open restriction. Smoothness of U restricts to U^0 by
   lem-weil-pbc-smooth-restrict-open-subschemes, and U^0 is reduced by
   sbc-lem-smooth-geometrically-reduced.
2. The connected image of U^0 contains the identity and lies in V^0. The reduced-source
   factorization lem-weil-pbc-reduced-source-factors-through-closed-subscheme gives its
   unique factor f through H. The group identities descend along the closed immersion.
   On coordinate rings, the finite module F[U] descends to its quotient F[U^0] over
   the quotient F[H] of F[V], proving finiteness of f.
3. By lem-sfb-group-neutral-component-translates there are finitely many component
   translates of U^0. Their images are closed by lem-weil-pbc-finite-closed-map-finite-fibres
   and cover V. Those meeting H lie in H; their translating rational points factor
   through H by reduced-source factorization. Irreducibility of H makes one image
   translate all of H. Translating back proves surjectivity of f.
4. Affine groups are separated by lem-weil-pbc-affine-source-morphism-separated.
   Apply lem-sfb-algebraic-group-homomorphism-factorization to f. Its closed image is
   surjective onto reduced H, hence an isomorphism by reduced-source factorization and
   the monomorphism property of a closed immersion. Thus f is faithfully flat.
   The affine criterion lem-weil-pbc-flat-morphism-affine-criterion and
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat give coordinate faithful flatness.
5. For every smooth connected normal unipotent closed subgroup N of U^0, factor its
   map to H using lem-sfb-algebraic-group-homomorphism-factorization. Apply
   lem-sfb-unipotent-normal-quotient-image: its closed image is smooth connected normal
   unipotent in H. Reductivity of H makes that image trivial scheme-theoretically.
6. F[N] is a quotient of F[U^0], finite over F[H]. The latter action factors through
   its identity evaluation into F, so F[N] is finite dimensional over F and Artinian.
   Smoothness makes N reduced by sbc-lem-smooth-geometrically-reduced, and
   def-pc-reduced-scheme makes its coordinate ring reduced.
7. By lem-sfb-reduced-artinian-residue-product this ring is a finite product of fields.
   Connectedness permits only one factor; the identity point identifies it with F.
   Hence N is trivial. Together with step 1 this proves reductivity of U^0. Steps 2
   and 3 give the finite surjective restriction, without assuming a reduced kernel. -/
theorem finiteGroupCover_reductive_neutral
    (F : Type u) [Field F] [IsAlgClosed F]
    (U V : Grp (Over (Spec (.of F))))
    [IsAffine U.X.left] [LocallyOfFiniteType U.X.hom] [QuasiCompact U.X.hom]
    [IsAffine V.X.left] [LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]
    (q : U ⟶ V) [IsFinite q.hom.hom.left] [Surjective q.hom.hom.left]
    [Smooth U.X.hom]
    (H : Grp (Over (Spec (.of F)))) (i : H ⟶ V)
    (e : H.X.left ≅ (GrpObj.identityComponent V.X).left.nilradical.subscheme)
    (hi : i.hom.hom.left = e.hom ≫
      (GrpObj.identityComponent V.X).left.nilradical.subschemeι ≫
        (GrpObj.identityComponentι V.X).left)
    (hH : ReductiveTorusCentralizer.IsReductive H) :
    (∃ f : Grp.mk (GrpObj.identityComponent U.X) ⟶ H,
      f.hom.hom ≫ i.hom.hom = GrpObj.identityComponentι U.X ≫ q.hom.hom ∧
        IsFinite f.hom.hom.left ∧ Surjective f.hom.hom.left) ∧
      ReductiveTorusCentralizer.IsReductive (Grp.mk (GrpObj.identityComponent U.X)) := by
  sorry

end AlgebraicGeometry
