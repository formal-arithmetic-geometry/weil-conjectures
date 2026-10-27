module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Universal property of a faithfully flat affine group quotient

Source: Milne, Algebraic Groups (2017), Theorem 5.13, printed p.101, with
Definition 5.5, printed p.99 (blueprint: lem-sfb-faithfully-flat-group-quotient-universal).

The kernel and its inclusion are the existing fibre-product construction. Triviality
on the kernel is an equality of morphisms over the base field, including infinitesimal
points; no smoothness, connectedness or commutativity is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A homomorphism killing the scheme-theoretic kernel of a faithfully flat affine
finite-type group quotient factors uniquely through that quotient.

Source: Milne, Algebraic Groups (2017), Theorem 5.13, printed p.101, and
Definition 5.5, printed p.99 (blueprint: lem-sfb-faithfully-flat-group-quotient-universal).

Proof plan (the five steps of the DAG node):
1. For A = F[Q] and B = F[G], faithful flatness of q* makes q flat and surjective
   by lem-weil-pbc-flat-ring-map-iff-flat-affine and
   lem-weil-pbc-faithfully-flat-surjective-spectrum, using def-weil-affine-spectrum.
2. The singleton q is an fpqc covering (def-weil-pbc-fpqc-covering): cover any affine
   open V of Q by finitely many principal opens. Their inverse images are principal
   affine opens in G and their images cover V. Use
   lem-weil-pbc-spec-localization-away-basic-open,
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact,
   lem-weil-pbc-basic-open-pullback and lem-weil-pbc-affine-ideals-closed-subscheme.
3. On P = G ×_Q G, put d = p1⁻¹ p2. The group-object identities and q p1 = q p2
   show q d = e, so the kernel fibre-product property gives a : P → ker q with
   i a = d. The assumption on u gives u d = e, whence u p2 = u p1.
   Use def-sc-group-scheme and def-pc-fibre-product.
4. By lem-weil-pbc-fpqc-representable-descent, u descends uniquely to a scheme map
   v : Q → H. It is over F since its structure-map equation holds after q and
   uniqueness of descent applies with target Spec F.
5. The product q ×_F q is fpqc: factor it into two base changes of q, using
   lem-weil-pbc-fpqc-covering-axioms. The two maps expressing multiplication
   preservation by v agree after this cover because u is a homomorphism. Descent
   uniqueness makes them equal, so v is a homomorphism (def-sc-group-scheme).
   Any other homomorphism factoring u is the same scheme map by step 4. -/
theorem existsUnique_hom_of_faithfullyFlat_of_trivial_on_kernel
    {F : Type u} [Field F]
    (G Q H : Over (Spec (.of F))) [GrpObj G] [GrpObj Q] [GrpObj H]
    [IsAffine G.left] [IsAffine Q.left] [IsAffine H.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (q : G ⟶ Q) [IsMonHom q]
    (hq : q.left.appTop.hom.FaithfullyFlat)
    (u : G ⟶ H) [IsMonHom u]
    (hu : GrpObj.kerι q ≫ u = toUnit (GrpObj.ker q) ≫ η[H]) :
    ∃! v : Q ⟶ H, IsMonHom v ∧ q ≫ v = u := by
  sorry

end AlgebraicGeometry
