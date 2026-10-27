/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.Connected.Basic

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Sheaf.AlgebraicGeometry.CentralTorusFaithfulWeightBlocks

/-! # Normal unipotent images under quotient homomorphisms

Source: Milne, Algebraic Groups (2017), Corollary 14.7, p.282;
Proposition 1.62(b), pp.24--25; Proposition 5.59(b), p.114;
proof of Lemma 19.14, p.400
(blueprint: lem-sfb-unipotent-normal-quotient-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.SolvableGroupStructure

/-- A specified closed image of a smooth connected normal unipotent subgroup under
an affine faithfully flat group homomorphism is smooth, connected, unipotent and normal.
The closed immersion j is initially only a scheme morphism; its homomorphism property
is included in the normal-subgroup conclusion. Neither kernel has extra hypotheses.

Source: Milne, Algebraic Groups (2017), Corollary 14.7, p.282;
Proposition 1.62(b), pp.24--25; Proposition 5.59(b), p.114;
proof of Lemma 19.14, p.400
(blueprint: lem-sfb-unipotent-normal-quotient-image).

Proof plan, following all six steps of the node:
1. Write C=F[I], B=F[N], E=F[D], P=F[A]. Faithful flatness makes C to B and
   E to P injective (lem-weil-pbc-faithfully-flat-universally-injective).
   Split these injections as F-linear maps. Tensor their splittings to detect
   equality and closed-subscheme factorization after u times u, f times u and
   field extension, using lem-weil-pbc-fibre-product-affine-spectra and the
   quotient-ring criterion. The equation iN followed by f = u followed by j
   then implies that j respects multiplication, identity and inverse.
2. Smooth N is geometrically reduced (sbc-lem-smooth-geometrically-reduced).
   For every field extension L, C tensor L injects into the reduced ring
   B tensor L, so is reduced. Apply lem-sfb-geometrically-reduced-group-smooth
   to the finite-type group I. This does not require u or its kernel smooth.
3. The map u is surjective on underlying spaces by
   lem-weil-pbc-faithfully-flat-surjective-spectrum. A nonempty clopen partition
   of I pulls back to one of N, contradicting connectedness. The identity of I
   ensures nonemptiness.
4. For an algebraically closed extension K, faithful flatness survives base change
   (lem-weil-pbc-faithfully-flat-base-change). The fibre of K[I] to K[N] over
   x in I(K) is a nonzero finitely generated K-algebra, by
   lem-weil-pbc-faithfully-flat-maximal-ideal-nonzero and
   lem-weil-pbc-lft-affine-pairs. Choose a maximal ideal
   (lem-weil-common-extension-fields-maximal-ideal); its residue field is K
   (lem-weil-pbc-closed-point-residue-field-base), giving a lift n in N(K).
5. Apply lem-sfb-central-torus-faithful-weight-blocks with the trivial torus to
   choose a faithful positive-dimensional closed matrix representation of I.
   For each geometric point x lift n as in step 4. Apply
   lem-sfb-rational-representation-unipotent-point to the given faithful
   representation of N and the composite representation N to I to GL.
   Its matrix at x is unipotent. Thus the same faithful representation proves
   geometric matrix unipotence of I.
6. Let J be the ideal defining j(I) in D and c:D times I to D conjugation.
   Normality of N on every test algebra makes c after f times u factor through I:
   evaluate at the universal pair over P tensor B and use the quotient criterion.
   The tensor injection in step 1 implies c*(J)=0, so c itself factors through I.
   On every algebra, conjugation by d preserves j(I); applying this to d inverse
   gives equality. This proves normality including nonreduced test algebras.
-/
theorem unipotent_normal_quotient_image
    {F : Type u} [Field F] [IsAlgClosed F]
    (A D N I : Grp (Over (Spec (.of F))))
    [IsAffine A.X.left] [LocallyOfFiniteType A.X.hom] [QuasiCompact A.X.hom]
    [IsAffine D.X.left] [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    [IsAffine N.X.left] [LocallyOfFiniteType N.X.hom] [QuasiCompact N.X.hom]
    [IsAffine I.X.left] [LocallyOfFiniteType I.X.hom] [QuasiCompact I.X.hom]
    (f : A ⟶ D) (iN : N ⟶ A)
    [IsClosedSubgroupScheme iN.hom.hom] [IsNormalSubgroupScheme iN.hom.hom]
    [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (hN : IsUnipotent N)
    (hf : f.hom.hom.left.appTop.hom.FaithfullyFlat)
    (uN : N ⟶ I) (j : I.X ⟶ D.X) [IsClosedImmersion j.left]
    (hu : uN.hom.hom.left.appTop.hom.FaithfullyFlat)
    (hfactor : iN.hom.hom ≫ f.hom.hom = uN.hom.hom ≫ j) :
    Smooth I.X.hom ∧ ConnectedSpace I.X.left ∧ IsUnipotent I ∧
      IsNormalSubgroupScheme j := by
  sorry

end AlgebraicGeometry.SolvableGroupStructure
