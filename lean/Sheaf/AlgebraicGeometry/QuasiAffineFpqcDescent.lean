/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.FpqcDescendingTypesMorphisms
import Sheaf.AlgebraicGeometry.QuasiAffineBaseChange

/-!
# Effective fpqc descent of quasi-affine morphisms

Source: Stacks Project, Descent, Tag 0247, lemma-quasi-affine, specialized to a singleton
fpqc covering (blueprint: lem-trf-quasi-affine-fpqc-effective-descent).
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace CategoryTheory.Over.DescentDatum

/-- A descent datum on a quasi-affine scheme morphism along a singleton fpqc covering is
 effective. There is no local finite-presentation assumption.

Source: Stacks Project, Descent, Tag 0247, lemma-quasi-affine.
(blueprint: lem-trf-quasi-affine-fpqc-effective-descent)

Proof:
1. Quasi-affineness is invariant under isomorphism and stable under base change, by
   lem-trf-quasi-affine-base-change. This is condition (1) of the fpqc reduction, Tag 02W3.
2. For a finite disjoint union of quasi-affine morphisms, intersect an affine target open
   with each clopen component. Each intersection is a principal affine open defined by an
   idempotent (lem-weil-pbc-spec-clopen-idempotent and
   lem-weil-pbc-principal-localization-open-immersion). Its inverse image is a quasi-compact
   open in an affine scheme. The finite disjoint union of these ambient affine schemes is
   affine (lem-weil-pbc-affine-morphism-permanence), and the union of their opens is
   quasi-compact. The empty family is handled by Spec of the zero ring. This proves
   condition (2), using lem-weil-pbc-scheme-coproduct-family.
3. For condition (3), let p be flat and surjective between affine schemes. It is
   quasi-compact by lem-weil-pbc-affine-scheme-qcqs and
   lem-weil-pbc-qcqs-morphism-permanence, hence a singleton fpqc covering. V is quasi-affine
   and qcqs. Put C = Gamma(V, O) and W = Spec C. The canonical map j : V -> W is an open
   immersion by lem-trf-quasi-affine-canonical-affine-embedding. The map W -> A induced by
   the structure map on sections is affine, and j is over A, by
   lem-weil-pbc-morphism-into-affine-scheme and lem-weil-pbc-morphism-affine-schemes-affine.
4. On A_2 = A x_B A, flat base change of global sections of V identifies each pullback W_i
   with Spec Gamma(V_i, O). The tensor formula c tensor t maps to the product of the two
   pulled-back sections. It also identifies j_i with the canonical map to this spectrum.
   Use lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-flat-base-change-global-sections-qcqs and the affine mapping property.
5. Apply the contravariant spectrum functor to the ring isomorphism on sections induced
   by the given descent isomorphism. The result psi : W_0 -> W_1 extends that isomorphism,
   since both composites from V_0 induce the same ring map on sections.
6. On A_3 all required projections are flat and the pulled-back V's are qcqs. The tensor
   formula commutes with the given isomorphism and with successive base change: both
   orders multiply the same pulled-back sections. Thus psi satisfies the cocycle and j
   is a morphism of descent data (def-pd-descent-datum).
7. Apply lem-galois-fpqc-affine-descent-effective to W -> A, obtaining W' -> B and a
   compatible identification W = W' x_B A. Its projection q : W -> W' is flat,
   quasi-compact and surjective by the base-change permanence results.
8. The open O = j(V) is invariant: its inverse images along the two projections from
   W x_{W'} W agree, since psi extends the datum on V. Pullbacks of open immersions are
   open immersions, by lem-weil-pbc-open-immersion-base-change, and their images are the
   inverse images of O (def-pc-fibre-product and def-weil-open-immersion).
9. O is a union of fibres of q. Indeed two points over z admit a common lift to the
   fibre product: Spec of their residue-field tensor product over kappa(z) is nonempty,
   by lem-weil-pbc-surjective-base-change and lem-weil-pbc-fibre-product-affine-spectra;
   lem-weil-pbc-fibre-product-points gives the lift. Invariance proves membership in O
   equivalent for the two points. Hence q^{-1}(q(O)) = O. The set U = q(O) is open by
   lem-weil-pbc-flat-qc-surjective-quotient-map.
10. The open subscheme U of W', mapped to B, pulls back to O and hence to V. Its canonical
    descent datum is the restriction of psi, which is precisely the original datum by
    step 5. This proves condition (3). Apply lem-galois-fpqc-descending-types-morphisms
    with conditions (1), (2), (3) to obtain the result for the original singleton fpqc
    covering. No step assumes local finite presentation. -/
theorem isEffective_of_isQuasiAffineHom_fpqc {A B : Scheme.{u}} (p : A ⟶ B)
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage B) {V : Over A}
    [IsQuasiAffineHom V.hom] (D : Over.DescentDatum p V) : D.IsEffective := by
  sorry

end CategoryTheory.Over.DescentDatum
