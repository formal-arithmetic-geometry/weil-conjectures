/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.ProductTangentSpaceDirectSum
import Sheaf.AlgebraicGeometry.GroupAdditionTangentDifferential

/-!
# Open multiplication for transverse smooth closed subgroups

Source: Milne, Algebraic Groups (2017), Theorem 13.33(d), proof on printed p.266
(blueprint: lem-sfb-transverse-subgroup-product-open).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- Multiplication of transverse smooth closed subgroups with trivial functorial intersection
is an open immersion. No connectedness hypothesis is imposed.

The two images in the identity tangent space are expressed by factorization of dual-number
morphisms through the inclusions. Since the inclusions are monomorphisms, such a factorization
of an identity tangent vector is automatically over k and based at the subgroup identity.
Consequently these are precisely the images of Lie(H) and Lie(K), with residue fields
identified through their k-rational identity sections. The hypothesis `hLie` says that every
ambient tangent vector has a unique decomposition as a sum from those two images. Addition
is canonically linear, so this is exactly the stipulated vector-space isomorphism.

Source: Milne, Algebraic Groups (2017), Theorem 13.33(d), printed p.266
(blueprint: lem-sfb-transverse-subgroup-product-open).

Proof for stage 3:
1. By def-weil-closed-immersion, the closed subgroups of the affine G are affine. Their
   structure maps are smooth, so lem-weil-pbc-smooth-ring-map-iff-smooth-affine gives smooth
   coordinate algebras A and B over k, hence finite presentation and finite generation.
   The affine product is Spec(A tensor[k] B) by lem-weil-pbc-fibre-product-affine-spectra.
   Its finite generators come from those of A and B (def-weil-finite-type-morphism).
   Base change and composition of smooth maps
   (lem-weil-pbc-smooth-ring-map-base-change-composition), followed by the affine comparison
   again, show that H times K is smooth of finite type over k.
2. On every k-algebra R, hk = h'k' gives h' inverse times h = k' times k inverse in the
   intersection, hence the identity by `hinter`. Thus both factors agree. This calculation
   uses def-sc-group-scheme-subgroup on all R, including nonreduced R. Restrict arbitrary
   scheme tests to affine opens and glue the equalities to obtain a monomorphism.
3. Apply lem-sc-product-tangent-space-direct-sum to the product at the identities.
   Functoriality of def-sc-scheme-tangent-space and
   lem-sc-group-addition-tangent-differential identify the differential of multiplication
   with addition of the two subgroup tangent images. By `hLie` it is an isomorphism.
4. For each rational (h,k), the automorphisms a(u,v)=(hu,vk) and b(g)=hgk satisfy m a = b m
   by def-sc-group-scheme. Their inverse maps use h inverse and k inverse. Differentiate
   this identity using def-sc-scheme-tangent-space to transport the identity differential
   to (h,k). The product universal property (def-pc-fibre-product) covers every rational
   product point, without any connectedness assumption.
5. Apply lem-sfb-smooth-tangent-isomorphism-etale: the algebraically closed base, smooth
   finite-type source and target, and all rational tangent isomorphisms have been checked.
   Multiplication is therefore etale, hence flat and locally of finite presentation
   (def-weil-etale-morphism). Together with step 2,
   lem-pe-flat-lfp-monomorphism-open proves the conclusion.
-/
theorem isOpenImmersion_transverse_subgroup_product
    (k : Type u) [Field k] [IsAlgClosed k]
    (G H K : Over (Spec (.of k))) [GrpObj G] [GrpObj H] [GrpObj K]
    [IsAffine G.left] [Smooth G.hom] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (i : H ⟶ G) (j : K ⟶ G) [IsClosedSubgroupScheme i] [IsClosedSubgroupScheme j]
    [Smooth H.hom] [Smooth K.hom]
    (hinter : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ H)
      (t : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ K),
      h ≫ i = t ≫ j → h ≫ i = 1)
    (hLie : ∀ v : schemeTangentSpace k G.left G.hom (GrpObj.onePoint G),
      ∃! w : schemeTangentSpace k G.left G.hom (GrpObj.onePoint G) ×
          schemeTangentSpace k G.left G.hom (GrpObj.onePoint G),
        (∃ a : Spec (.of (DualNumber (G.left.residueField (GrpObj.onePoint G)))) ⟶ H.left,
          a ≫ i.left = w.1.val) ∧
        (∃ b : Spec (.of (DualNumber (G.left.residueField (GrpObj.onePoint G)))) ⟶ K.left,
          b ≫ j.left = w.2.val) ∧
        w.1 + w.2 = v) :
    IsOpenImmersion ((i ⊗ₘ j) ≫ μ[G]).left := sorry

end AlgebraicGeometry
