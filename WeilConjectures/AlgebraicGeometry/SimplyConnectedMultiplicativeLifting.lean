/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiagonalizableGroupScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Unique lifting from a multiplicatively simply connected group

Source: Milne, Algebraic Groups (2017), Definition 18.5, Proposition 18.6(a),
Definition 18.7 and Proposition 18.8, printed pp.388--389
(blueprint: lem-sfb-simply-connected-multiplicative-lifting).
-/

@[expose] public section

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

set_option autoImplicit false

/-- A multiplicative universal covering lifts uniquely through a multiplicative isogeny.

Source: Milne, Algebraic Groups (2017), Definition 18.5, Proposition 18.6(a),
Definition 18.7 and Proposition 18.8, printed pp.388--389
(blueprint: lem-sfb-simply-connected-multiplicative-lifting).

Proof plan:
1. Form P = H ×_G E with projections a and b. Its coordinate algebra is
   F[H] ⊗_{F[G]} F[E] (lem-weil-pbc-fibre-product-affine-spectra), so P is affine
   of finite type. Faithfully flat base change makes a faithfully flat
   (lem-weil-pbc-faithfully-flat-base-change). Its kernel is ker p, central in P.
2. By lem-sfb-group-neutral-component-translates, P is covered by finitely many
   translates of its clopen identity component C. By
   lem-sfb-locally-algebraic-group-identity-component, R = C_red is a smooth
   connected group of finite type with the same underlying space as C. The
   inclusion j : R → P is closed; hence R is affine. Put r = a ∘ j.
3. The homomorphism factorization theorem
   (lem-sfb-algebraic-group-homomorphism-factorization) gives a closed image I of r.
   Faithful flatness makes a surjective
   (lem-weil-pbc-faithfully-flat-surjective-spectrum). The finitely many translates
   of I cover H. The smooth connected H is irreducible by the identity-component
   result, so one translate is H and I = H. Thus r is surjective.
4. Smoothness makes H reduced (sbc-lem-smooth-geometrically-reduced). The kernel
   of r* lies in every prime by surjectivity of r; it is zero by reducedness and
   lem-weil-pbc-zero-locus-eq-iff-radical-eq. Apply
   lem-sfb-reduced-target-dominant-group-flatness to obtain faithful flatness of r*.
5. The kernel of r is a closed subgroup of ker p, hence finite and central.
   A finite set of generators of the character group embeds ker p in a split
   torus. By lem-sfb-split-torus-subgroups-diagonalizable, ker r is diagonalizable.
   Thus r is a multiplicative isogeny from a smooth connected affine group.
6. The simple-connectedness hypothesis makes r an isomorphism. Its inverse is
   a group homomorphism. Set u = b ∘ j ∘ r⁻¹; the pullback identity gives p ∘ u = q.
7. If v is another lift, δ(h) = u(h)v(h)⁻¹ factors through ker p. This kernel has
   finite discrete underlying space by
   lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum. Connectedness of H
   makes its image the identity point. The unit Spec F → ker p is closed and H
   is reduced, so lem-weil-pbc-reduced-source-factors-through-closed-subscheme
   makes δ the identity morphism. Hence u = v on every algebra, also when the
   finite diagonalizable kernel is nonreduced. -/
theorem simplyConnected_multiplicative_lifting {F : Type u} [Field F] [IsAlgClosed F]
    (H G E : Over (Spec (.of F))) [GrpObj H] [GrpObj G] [GrpObj E]
    [IsAffine H.left] [IsAffine G.left] [IsAffine E.left]
    [Smooth H.hom] [Smooth G.hom] [Smooth E.hom]
    [ConnectedSpace H.left] [ConnectedSpace G.left] [ConnectedSpace E.left]
    [LocallyOfFiniteType H.hom] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType E.hom]
    [QuasiCompact H.hom] [QuasiCompact G.hom] [QuasiCompact E.hom]
    (hH : ∀ (H1 : Over (Spec (.of F))) [GrpObj H1] [IsAffine H1.left]
      [Smooth H1.hom] [ConnectedSpace H1.left] [LocallyOfFiniteType H1.hom]
      [QuasiCompact H1.hom] (r : H1 ⟶ H) [IsMonHom r],
      r.left.appTop.hom.FaithfullyFlat → IsFinite (GrpObj.ker r).hom →
      IsFiniteDiagonalizableGroupScheme (GrpObj.ker r) →
      (∀ (T : Over (Spec (.of F))) (x : T ⟶ GrpObj.ker r) (h : T ⟶ H1),
        (x ≫ GrpObj.kerι r) * h = h * (x ≫ GrpObj.kerι r)) → IsIso r)
    (q : H ⟶ G) (p : E ⟶ G) [IsMonHom q] [IsMonHom p]
    (hq : q.left.appTop.hom.FaithfullyFlat) (hp : p.left.appTop.hom.FaithfullyFlat)
    [IsFinite (GrpObj.ker q).hom] [IsFinite (GrpObj.ker p).hom]
    (hqdiag : IsFiniteDiagonalizableGroupScheme (GrpObj.ker q))
    (hpdiag : IsFiniteDiagonalizableGroupScheme (GrpObj.ker p))
    (hqcentral : ∀ (T : Over (Spec (.of F))) (x : T ⟶ GrpObj.ker q) (h : T ⟶ H),
      (x ≫ GrpObj.kerι q) * h = h * (x ≫ GrpObj.kerι q))
    (hpcentral : ∀ (T : Over (Spec (.of F))) (x : T ⟶ GrpObj.ker p) (e : T ⟶ E),
      (x ≫ GrpObj.kerι p) * e = e * (x ≫ GrpObj.kerι p)) :
    ∃! u : H ⟶ E, IsMonHom u ∧ u ≫ p = q := by
  sorry

end AlgebraicGeometry
