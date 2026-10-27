module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.SmoothAmbientNormalityGeometric
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomRationalPoints
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup
import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry

/-! # Lifting solvable normal subgroups through a central isogeny

Source: Milne, Algebraic Groups (2017), Proposition 6.27, p.131;
Propositions 1.34, 1.38, 1.90 and Theorem 5.39
(blueprint: lem-sfb-central-isogeny-solvable-normal-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- The reduced identity component of the inverse image of a smooth connected solvable
normal subgroup under a faithfully flat homomorphism with finite central kernel is a
smooth connected solvable normal closed subgroup and maps faithfully flatly to that subgroup.

The square defining P is its actual inverse image. The open C is its identity component;
its reduction is canonically (P_red)^0, since reduction preserves the underlying space and
restricts on opens. The isomorphism e and its inclusion equation specify precisely this
subgroup V. The last cartesian square identifies ker(h) with V intersect ker(f), as schemes.

Source: Milne, Algebraic Groups (2017), Proposition 6.27, p.131; Propositions 1.34 and 1.38,
pp.16--18; Proposition 1.90, p.33; Theorem 5.39, p.108; Proposition 1.63, p.25
(blueprint: lem-sfb-central-isogeny-solvable-normal-lift).

Proof plan:
1. Form P = E x_B U. On every algebra its points are the inverse image of U, so it is
   normal. Closed immersion base change makes P closed in E; its coordinate algebra is
   F[E]/JF[E] if F[U] = F[B]/J. Thus it is affine and of finite type.
2. Apply lem-sfb-locally-algebraic-group-identity-component to P. Its clopen identity
   component C has smooth connected reduction. Reduction commutes with restriction to
   an open (def-weil-pbc-scheme-reduction), so C_red = (P_red)^0. Its inclusion in E is closed.
3. Conjugation by every F-point of E preserves P, hence its identity component and the
   reduction of that component. Apply lem-sfb-smooth-ambient-normality-geometric in the
   smooth ambient group E to obtain scheme-theoretic normality of V.
4. By lem-sfb-affine-group-homomorphism-image, P(F) maps onto U(F). The finitely many
   translates of P's identity component (lem-sfb-group-neutral-component-translates)
   give a finite coset cover of U(F) by translates of h(V(F)). Factor h through its closed
   faithfully flat image by lem-sfb-affine-homomorphism-flat-image.
5. U is irreducible by the identity-component lemma and reduced by
   sbc-lem-smooth-geometrically-reduced. The product of the ideals of the finitely many
   closed image translates vanishes on U(F), hence is zero by
   lem-wf-affine-nullstellensatz-vanishing. Irreducibility makes one translate all of U;
   reducedness makes it all of U as a scheme. Thus h is faithfully flat.
6. For a solvable series U_i of U, construct successive smooth connected derived
   subgroups D_i of V by lem-sfb-smooth-connected-derived-subgroup. Inductively D_i maps
   into U_i: the map to the commutative affine quotient U_i/U_{i+1}, supplied by
   lem-sfb-affine-normal-quotient-geometry, kills D_{i+1}. The last D_r lies in the
   central kernel of f, so is commutative, and D_{r+1} is trivial, including when r = 0.
7. The affine quotients D_i/D_{i+1} are commutative: two sections lift fppf locally,
   their commutator is killed, and the represented quotient is a sheaf. This gives
   the finite closed subnormal series required by SolvableGroupStructure.IsSolvable.
8. The kernel square identifies ker(h) with V x_E ker(f). It is closed in the finite
   kernel of f, so its coordinate algebra is a quotient of a finite dimensional
   F-algebra and is finite dimensional. No smoothness of either kernel is used. -/
theorem centralIsogeny_solvableNormalLift {F : Type u} [Field F] [IsAlgClosed F]
    (E B : Grp (Over (Spec (.of F))))
    [IsAffine E.X.left] [LocallyOfFiniteType E.X.hom] [QuasiCompact E.X.hom]
    [Smooth E.X.hom] [ConnectedSpace E.X.left]
    [IsAffine B.X.left] [LocallyOfFiniteType B.X.hom] [QuasiCompact B.X.hom]
    [Smooth B.X.hom] [ConnectedSpace B.X.left]
    (f : E ⟶ B) (hff : f.hom.hom.left.appTop.hom.FaithfullyFlat)
    [IsFinite (CategoryTheory.GrpObj.ker f.hom.hom).hom]
    (hcentral : ∀ (R : Type u) [CommRing R] [Algebra F R]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F R))) ⟶
        CategoryTheory.GrpObj.ker f.hom.hom)
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F R))) ⟶ E.X),
      (x ≫ CategoryTheory.GrpObj.kerι f.hom.hom) * g =
        g * (x ≫ CategoryTheory.GrpObj.kerι f.hom.hom))
    (U : Grp (Over (Spec (.of F)))) (i : U ⟶ B)
    [IsClosedSubgroupScheme i.hom.hom] [IsNormalSubgroupScheme i.hom.hom]
    [Smooth U.X.hom] [ConnectedSpace U.X.left]
    (hsolv : SolvableGroupStructure.IsSolvable U) :
    ∃ (P : Grp (Over (Spec (.of F)))) (p : P ⟶ E) (q : P ⟶ U),
      IsPullback p.hom.hom q.hom.hom f.hom.hom i.hom.hom ∧
      ∃ C : P.X.left.Opens,
        (C : Set P.X.left) = connectedComponent (GrpObj.onePoint P.X) ∧
        ∃ (V : Grp (Over (Spec (.of F)))) (v : V ⟶ E) (h : V ⟶ U)
          (e : V.X.left ≅ C.toScheme.nilradical.subscheme),
          v.hom.hom.left = e.hom ≫ C.toScheme.nilradical.subschemeι ≫ C.ι ≫
            p.hom.hom.left ∧
          v ≫ f = h ≫ i ∧
          Smooth V.X.hom ∧ ConnectedSpace V.X.left ∧
          SolvableGroupStructure.IsSolvable V ∧
          IsClosedSubgroupScheme v.hom.hom ∧ IsNormalSubgroupScheme v.hom.hom ∧
          h.hom.hom.left.appTop.hom.FaithfullyFlat ∧
          IsFinite (CategoryTheory.GrpObj.ker h.hom.hom).hom ∧
          ∃ a : CategoryTheory.GrpObj.ker h.hom.hom ⟶
              CategoryTheory.GrpObj.ker f.hom.hom,
            IsPullback (CategoryTheory.GrpObj.kerι h.hom.hom) a v.hom.hom
              (CategoryTheory.GrpObj.kerι f.hom.hom) := by
  sorry

end AlgebraicGeometry
