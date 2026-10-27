module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Sheaf.AlgebraicGeometry.CommutativeMultiplicativeTypeExtension

/-! # A central extension of tori is a torus

Source: Milne, Algebraic Groups (2017), Lemma 16.43, printed p.340,
Theorem 12.23, printed p.240, and the inverse-image argument in Theorem 17.82,
printed p.379 (blueprint: lem-sfb-central-extension-of-tori).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A smooth connected affine central extension of two tori is a torus over any field.
The kernel identification respects the specified closed subgroup inclusion, and centrality
is tested on all commutative algebras, including nonreduced ones.

Source: Milne, Algebraic Groups (2017), Lemma 16.43, p.340, Theorem 12.23, p.240,
and Theorem 17.82, p.379 (blueprint: lem-sfb-central-extension-of-tori).

Proof plan:
1. Extend to the algebraic closure F of k. The identity section and connectedness imply
   geometric connectedness by lem-sbc-connected-rational-point-geometrically-connected.
   Smoothness survives by lem-pc-proper-base-change. The affine tensor-product description
   of lem-weil-pbc-fibre-product-affine-spectra preserves affineness and finite type.
2. By lem-weil-pbc-flat-ring-map-iff-flat-affine and
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat, the coordinate map of q is
   faithfully flat. By lem-weil-pbc-faithfully-flat-base-change it stays so over F.
   The fibre-product universal property preserves its kernel T, and centrality persists
   because every F-algebra is also a k-algebra.
3. The split tori T_F and S_F are diagonalizable by
   lem-sfb-diagonalizable-group-geometric-criteria. Apply
   lem-sfb-multiplicative-extension-action-rigidity to the conjugation action of E_F
   on itself. Its triviality says that E_F is commutative on all algebras of points.
4. Apply lem-sfb-commutative-multiplicative-type-extension to obtain E_F isomorphic to
   D_F(M) for a finitely generated abelian group M.
5. By lem-sfb-diagonalizable-group-geometric-criteria, smoothness and geometric
   connectedness force M to be torsion-free: in positive characteristic connectedness
   makes torsion p-primary and smoothness excludes it; in characteristic zero
   connectedness already excludes torsion. The structure theorem
   lem-sbc-finitely-generated-abelian-group-structure gives M isomorphic to Z^r.
   The product formula identifies D_F(M) with G_m^r, including r = 0. This is
   MultiplicativeType.IsTorus of E. -/
theorem isTorus_of_central_extension {k : Type u} [Field k]
    (E T S : Over (Spec (.of k))) [GrpObj E] [GrpObj T] [GrpObj S]
    [IsAffine E.left] [IsAffine T.left] [IsAffine S.left]
    [LocallyOfFiniteType E.hom] [QuasiCompact E.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom]
    [Smooth E.hom] [ConnectedSpace E.left]
    (i : T ⟶ E) [IsClosedSubgroupScheme i]
    (q : E ⟶ S) [IsMonHom q]
    [Flat q.left] [Surjective q.left]
    [LocallyOfFinitePresentation q.left] [QuasiCompact q.left] [QuasiSeparated q.left]
    (hT : MultiplicativeType.IsTorus (Grp.mk T))
    (hS : MultiplicativeType.IsTorus (Grp.mk S))
    (hcentral : ∀ (A : Type u) [CommRing A] [Algebra k A]
      (t : StandardGroupSchemes.affine k A ⟶ T)
      (e : StandardGroupSchemes.affine k A ⟶ E), (t ≫ i) * e = e * (t ≫ i))
    (hker : ∃ f : Grp.mk T ≅ Grp.mk (GrpObj.ker q),
      f.hom.hom.hom ≫ GrpObj.kerι q = i) :
    MultiplicativeType.IsTorus (Grp.mk E) := by
  sorry

end AlgebraicGeometry
