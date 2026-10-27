/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.FinitePresentation

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Products and dimensions of affine normal subgroup schemes

Source: Milne, Algebraic Groups (2017), Section 5(f), pp.111--112;
Proposition 8.1, p.149; Lemma 6.41 and Proposition 6.42, p.134;
Corollary 1.35 and the dimension discussion, p.17
(blueprint: lem-sfb-affine-normal-subgroup-products).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- Products of smooth connected affine closed normal subgroup schemes exist with
an fppf-local product criterion. Closed subgroup dimensions are finite nonnegative
integers bounded by the ambient dimension, and strict closed inclusions of smooth
connected subgroup schemes strictly increase dimension.

Source: Milne, Algebraic Groups (2017), Section 5(f), pp.111--112;
Proposition 8.1, p.149; Lemma 6.41 and Proposition 6.42, p.134;
Corollary 1.35 and dimension discussion, p.17
(blueprint: lem-sfb-affine-normal-subgroup-products).

Proof plan, following the eight steps of the DAG node:
1. Normality gives the conjugation action of N on M. Form the semidirect product
   D = M ⋊ N with multiplication (m,n)(m',n') = (m(nm'n⁻¹),nn') and inverse
   (n⁻¹m⁻¹n,n⁻¹). Multiplication f(m,n)=mn is a homomorphism to G. The affine
   tensor-product description (lem-weil-pbc-fibre-product-affine-spectra) and
   lem-sfb-finite-type-composition-base-change make D affine, separated and finite type.
2. Projection D → N is split surjective with kernel M. A k-basis of the coordinate
   ring of M proves flatness via lem-weil-pbc-flat-ring-map-iff-flat-affine.
   Apply lem-sfb-exact-algebraic-group-property-permanence to obtain smoothness
   and connectedness of D.
3. Apply lem-sfb-algebraic-group-homomorphism-factorization to f. Its image P is
   closed in G and D → P is flat and surjective. Apply the quotient clauses of
   lem-sfb-exact-algebraic-group-property-permanence to obtain that P is affine,
   smooth and connected. The maps m ↦ q(m,1) and n ↦ q(1,n) give both containments.
4. Write P = Spec C and D = Spec E. By lem-pc-affine-finite-type-algebra and
   lem-weil-pbc-finite-type-algebra-noetherian, C is Noetherian. The map C → E is
   finitely presented by lem-weil-pbc-finite-type-noetherian-finite-presentation
   and faithfully flat by lem-weil-pbc-flat-surjective-spectrum-faithfully-flat.
   For p in P(R), R' = R ⊗[C] E is faithfully flat by
   lem-weil-pbc-faithfully-flat-base-change and finitely presented by tensoring
   a finite presentation. The canonical E-point supplies the local factors m,n.
5. Conversely, local factors give a P(R')-point. On R' ⊗[R] R' its two pullbacks
   agree because the closed immersion P → G is injective on points. This affine
   cover is fpqc by lem-weil-pbc-flat-ring-map-iff-flat-affine and
   lem-weil-pbc-faithfully-flat-surjective-spectrum. Apply
   lem-weil-pbc-fpqc-representable-descent to P and G to descend the point and equality.
6. Conjugation by h sends mn to (hmh⁻¹)(hnh⁻¹). Normality of M,N and the local
   criterion prove normality of P on every test algebra, as required by
   def-sc-group-scheme-subgroup. No global pointwise product equality is asserted.
7. By lem-kun-dimension-finite-type the ambient dimension is finite. Closed subgroup
   inclusions preserve irreducible closed chains and hence bound their dimensions.
   Each subgroup is nonempty because of its identity section, giving nonnegativity.
8. For J strictly closed in K, lem-sfb-locally-algebraic-group-identity-component
   makes connected K irreducible. Smoothness implies reducedness by
   sbc-lem-smooth-geometrically-reduced. By lem-weil-pbc-reduced-induced-closed-subscheme,
   equal supports would make J → K an isomorphism. Its support is therefore proper.
   Append K to any irreducible closed chain in J. The finite nonempty set of possible
   lengths has a maximum, proving dim J + 1 ≤ dim K and thus the strict inequality. -/
theorem affineNormalSubgroup_products
    {k : Type u} [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k))))
    [IsSeparated G.X.hom] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] :
    (∀ (M N : Grp (Over (Spec (.of k)))) (iM : M ⟶ G) (iN : N ⟶ G)
      [IsClosedSubgroupScheme iM.hom.hom] [IsNormalSubgroupScheme iM.hom.hom]
      [IsClosedSubgroupScheme iN.hom.hom] [IsNormalSubgroupScheme iN.hom.hom]
      [Smooth M.X.hom] [ConnectedSpace M.X.left] [IsAffine M.X.left]
      [Smooth N.X.hom] [ConnectedSpace N.X.left] [IsAffine N.X.left],
      ∃ (P : Grp (Over (Spec (.of k)))) (iP : P ⟶ G),
        IsClosedSubgroupScheme iP.hom.hom ∧ IsNormalSubgroupScheme iP.hom.hom ∧
        Smooth P.X.hom ∧ ConnectedSpace P.X.left ∧ IsAffine P.X.left ∧
        (∃ a : M ⟶ P, a ≫ iP = iM) ∧ (∃ b : N ⟶ P, b ≫ iP = iN) ∧
        ∀ (R : Type u) [CommRing R] [Algebra k R]
          (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G.X),
          (∃ p : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ P.X,
            p ≫ iP.hom.hom = g) ↔
          ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra k R') (φ : R →ₐ[k] R'),
            φ.toRingHom.FaithfullyFlat ∧ φ.toRingHom.FinitePresentation ∧
            ∃ (m : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R'))) ⟶ M.X)
              (n : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R'))) ⟶ N.X),
              Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g.left =
                ((m ≫ iM.hom.hom) * (n ≫ iN.hom.hom)).left) ∧
    (∀ (H : Grp (Over (Spec (.of k)))) (i : H ⟶ G) [IsClosedSubgroupScheme i.hom.hom],
      ∃ d : ℕ, topologicalKrullDim H.X.left = (d : WithBot ℕ∞) ∧
        (d : WithBot ℕ∞) ≤ topologicalKrullDim G.X.left) ∧
    (∀ (J K : Grp (Over (Spec (.of k)))) (iK : K ⟶ G) (j : J ⟶ K)
      [IsClosedSubgroupScheme iK.hom.hom] [IsClosedSubgroupScheme j.hom.hom]
      [Smooth J.X.hom] [ConnectedSpace J.X.left]
      [Smooth K.X.hom] [ConnectedSpace K.X.left],
      ¬ IsIso j.hom.hom.left → topologicalKrullDim J.X.left < topologicalKrullDim K.X.left) := by
  sorry

end AlgebraicGeometry
