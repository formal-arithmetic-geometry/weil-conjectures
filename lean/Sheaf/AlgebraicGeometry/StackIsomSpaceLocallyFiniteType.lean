/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover

/-! # Isomorphism spaces of objects of algebraic stacks

Source: Stacks Project, Morphisms of Stacks, Tag 04XR and the following lemma
`lemma-isom-pseudo-torsor-aut` (blueprint: lem-sfb-stack-isom-space-locally-finite-type).

A representing space is identified with isomorphisms on every test scheme, naturally
under restriction. Automorphism-space operations are normalized by this identification.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A representation of the Isom sheaf of two objects over `T`. Objects over `T` are
written as maps `h_T → F`; the fibred Yoneda lemma identifies their vertical natural
isomorphisms with isomorphisms in the fibre groupoid. The bijections are required to
commute with every restriction, including those from nonreduced schemes.
Source: Stacks Project, Tag 04XR, and Algebraic Stacks, Tag 04SI
(blueprint: lem-sfb-stack-isom-space-locally-finite-type). -/
structure ModuliIsomSpace {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    (T : Over S) (a b : BasedFunctor (discreteModuli (yoneda.obj T)) F) where
  /-- The representing algebraic space over the original base. -/
  space : AlgebraicSpace S
  /-- Its specified projection to `T`. -/
  projection : space.obj.obj ⟶ yoneda.obj T
  /-- Isomorphisms of the two pulled-back objects, without quotienting automorphisms. -/
  comparison : ∀ (V : Over S) (t : yoneda.obj V ⟶ yoneda.obj T),
    {g : yoneda.obj V ⟶ space.obj.obj // g ≫ projection = t} ≃
      ModuliTwoIso ((discreteModuliMap t).comp a) ((discreteModuliMap t).comp b)
  /-- Restriction is precomposition on sections and restriction of natural isomorphisms. -/
  naturality : ∀ (V W : Over S) (f : W ⟶ V) (t : yoneda.obj V ⟶ yoneda.obj T)
    (g : {g : yoneda.obj V ⟶ space.obj.obj // g ≫ projection = t})
    (g' : {g : yoneda.obj W ⟶ space.obj.obj // g ≫ projection = yoneda.map f ≫ t}),
    g'.val = yoneda.map f ≫ g.val →
      ∀ z : (discreteModuli (yoneda.obj W)).obj,
        (comparison W (yoneda.map f ≫ t) g').val.hom.app z =
          (comparison V t g).val.hom.app ((discreteModuliMap (yoneda.map f)).toFunctor.obj z)

/-- The automorphism group space with its actual identity, inverse and multiplication
maps. The existing presheaf groupoid laws, with both source and target equal to the
projection to `T`, are precisely the group-object laws over `T`. Multiplication is
composition: `multiply(f,g)` means `f` after `g`. The comparison specifies all operations.
Source: Stacks Project, lemma-isom-pseudo-torsor-aut(1), immediately after Tag 04XR
(blueprint: lem-sfb-stack-isom-space-locally-finite-type). -/
structure ModuliAutomorphismGroupSpace {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)}
    (T : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj T)) F)
    extends ModuliIsomSpace T a a where
  /-- The identity section over `T`. -/
  unit : yoneda.obj T ⟶ space.obj.obj
  /-- The inverse morphism over `T`. -/
  inverse : space.obj.obj ⟶ space.obj.obj
  /-- Composition on the actual fibre product over `T`. -/
  multiply : pullback projection projection ⟶ space.obj.obj
  /-- The group laws and compatibility with the structural projection. -/
  laws : AlgebraicSpace.IsPresheafGroupoid projection projection unit inverse multiply
  /-- The unit is the identity isomorphism of the pulled-back object. -/
  unit_comparison : ∀ (V : Over S) (t : yoneda.obj V ⟶ yoneda.obj T)
    (g : {g : yoneda.obj V ⟶ space.obj.obj // g ≫ projection = t}),
    t ≫ unit = g.val → ∀ z : (discreteModuli (yoneda.obj V)).obj,
      (comparison V t g).val.hom.app z = 𝟙 _
  /-- Inversion is inversion of the same isomorphism, on every test object. -/
  inverse_comparison : ∀ (V : Over S) (t : yoneda.obj V ⟶ yoneda.obj T)
    (g h : {g : yoneda.obj V ⟶ space.obj.obj // g ≫ projection = t}),
    g.val ≫ inverse = h.val → ∀ z : (discreteModuli (yoneda.obj V)).obj,
      (comparison V t h).val.hom.app z = (comparison V t g).val.inv.app z
  /-- Multiplication corresponds to composition, in the stated order. -/
  multiply_comparison : ∀ (V : Over S) (t : yoneda.obj V ⟶ yoneda.obj T)
    (g h k : {g : yoneda.obj V ⟶ space.obj.obj // g ≫ projection = t})
    (q : yoneda.obj V ⟶ pullback projection projection),
    q ≫ pullback.fst projection projection = g.val →
    q ≫ pullback.snd projection projection = h.val →
    q ≫ multiply = k.val → ∀ z : (discreteModuli (yoneda.obj V)).obj,
      (comparison V t k).val.hom.app z =
        (comparison V t h).val.hom.app z ≫ (comparison V t g).val.hom.app z

/-- Isomorphism spaces of objects of an algebraic stack are algebraic spaces locally
of finite type over their test scheme. The automorphism space is a group space with
multiplication given by composition, and is locally of finite type over the same scheme.
Source: Stacks Project, Tag 04XR and lemma-isom-pseudo-torsor-aut(1)
(blueprint: lem-sfb-stack-isom-space-locally-finite-type).

Proof:
1. The Isom sheaf is the base change of the representable diagonal along `(a,b)`.
   On test objects send `(c,alpha:c≅a,beta:c≅b)` to `beta alpha⁻¹`; its inverse
   sends `gamma` to `(a,1,gamma)`. These inverse equivalences commute with pullback.
2. Choose a smooth surjective atlas U. The relation R = U ×_F U is an algebraic
   space by the diagonal condition. Both projections R → U are smooth by base change
   of the atlas. This is the atlas relation of Stacks Tags 04T4 and 04T5.
3. On an étale scheme chart V → R the composite V → U is smooth, hence locally
   finitely presented and locally of finite type. Cancellation for the composite
   V → U ×_S U → U gives local finite type of V → U ×_S U. Thus the relation map
   R → U ×_S U is locally of finite type; no separation assumption on U/S is needed.
4. Lift a and then b through the atlas using successive surjective étale scheme
   charts of T ×_F U and of its second pullback. Their projections q₁:T₁→T and
   q₂:T₂→T₁ are smooth and surjective, hence flat and locally finitely presented.
5. Each qᵢ is an fpqc singleton covering: it is open by flatness and local finite
   presentation. Over an affine target, finitely many images from an affine open
   cover of its inverse image cover the target, by quasi-compactness of the affine.
   This is the finite-affine-image criterion in def-weil-pbc-fpqc-covering; it does
   not require qᵢ itself to be quasi-compact (Stacks Tag 022C).
6. With lift isomorphisms alpha:p(u)≅a and beta:p(v)≅b over T₂, identify the
   pulled-back Isom space with T₂ ×_(U ×_S U) R by delta ↦ beta⁻¹ delta alpha.
   The inverse is gamma ↦ beta gamma alpha⁻¹. Both commute with restriction.
7. The relation map is locally of finite type, so its base change, the Isom space
   over T₂, is locally of finite type (lem-sfb-stack-finite-type-calculus, in its
   algebraic-space case). Fibre products exist by lem-trf-space-fibre-products-etale-covers.
8. For any étale chart Z → Isom, its pullback Z₂ over T₂ is the corresponding
   étale chart of the pulled-back Isom space, by lem-trf-space-chartwise-etale-permanence.
   Hence Z₂ → T₂ is locally of finite type. Descend first along q₂ and then q₁,
   using lem-weil-pbc-fpqc-descend-locally-finite-type on scheme morphisms. The
   comparison of the two chart pullbacks preserves both projections, so the
   pullback universal property gives its inverse. This proves the chartwise claim
   (Stacks Tag 041S reducing to Tag 02KX).
9. Set b=a. Composition, identity and inversion in the fibre groupoids give natural
   transformations of the represented sheaf, hence morphisms of algebraic spaces.
   Their laws hold on every test scheme by the groupoid axioms, giving the specified
   group space, with the same local-finite-type conclusion. -/
theorem moduli_isom_space_locallyOfFiniteType {S : Scheme.{u}}
    (F : BasedCategory.{v, w} (Over S)) (hF : IsAlgebraicModuliStack F)
    (T : Over S) (a b : BasedFunctor (discreteModuli (yoneda.obj T)) F) :
    (∃ I : ModuliIsomSpace T a b,
      ∀ (V : Over S) (c : yoneda.obj V ⟶ I.space.obj.obj), AlgebraicSpace.IsEtale c →
        LocallyOfFiniteType ((yoneda.preimage (c ≫ I.projection)).left)) ∧
    (∃ G : ModuliAutomorphismGroupSpace T a,
      ∀ (V : Over S) (c : yoneda.obj V ⟶ G.space.obj.obj), AlgebraicSpace.IsEtale c →
        LocallyOfFiniteType ((yoneda.preimage (c ≫ G.projection)).left)) := by
  sorry

end CategoryTheory
