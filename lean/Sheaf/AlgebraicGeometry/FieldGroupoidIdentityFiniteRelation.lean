/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid
public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.HopkinsLevitzki
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import Sheaf.AlgebraicGeometry.FieldGroupoidStabilizerDimension
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite

/-!
# The identity component of an unramified field groupoid

Source: Stacks Project, stacks-morphisms.tex, Tag 06N0, first proof paragraph and the
verification that the relation map is separated and locally quasi-finite; spaces-over-fields,
Tag 06LZ; varieties, Tag 06LH
(blueprint: lem-sfb-field-groupoid-identity-finite-relation).

The product of presheaves on schemes over `S` is the relative product over `S`.
The decomposition is expressed by a singleton clopen affine neighbourhood of every point;
these neighbourhoods are pairwise disjoint and cover the representing scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The arrow space is a separated scheme with finite local Artinian components for both
field structures. Its identity component is a finite locally free monomorphic subgroupoid.
The equations for the restricted operations retain the originally supplied operations.
The augmentation `epsilon` identifies the residue field with `K`: it is surjective, its
kernel consists exactly of the nonunits, and its composites with both field maps are identity.
Source: Stacks Project, Tag 06N0, first proof paragraph and the parenthetical verification
in the following paragraph, with Tags 06FF, 06LZ and 06LH
(blueprint: lem-sfb-field-groupoid-identity-finite-relation).

Proof:
1. Form the stabilizer as the pullback of the diagonal along `(s,t)` using
   lem-trf-space-fibre-products-etale-covers. It is unramified over `Spec K` by
   lem-sfb-space-unramified-permanence. Its etale scheme charts are unramified over `K`,
   so lem-trf-unramified-field-fibre-decomposition makes them zero-dimensional.
   The unit makes the stabilizer nonempty. By lem-sfb-field-groupoid-stabilizer-dimension,
   the arrow space also has dimension zero.
2. Apply lem-sfb-zero-dimensional-field-space-components separately to the two projections.
   They give the same singleton clopen components of a separated scheme `Z`, with each
   coordinate ring local Artinian and finite-dimensional for either field structure.
   The unit factors through its component `P`. Its augmentation to `K` splits both
   structural field maps; it is surjective and its kernel is the unique maximal ideal.
3. Choose a finite vector-space basis of the coordinate ring of `P` beginning with `1`,
   for each field structure. This gives finite free modules. The finitely many
   multiplication-table relations give a finite algebra presentation, so both maps are
   finite, flat and locally finitely presented, as in def-pc-finite-locally-free.
4. By lem-weil-pbc-artinian-local-noetherian-nilpotent the maximal ideal has a nilpotent
   power. In every tensor product of two copies of this ring over either field structure,
   the sum of the two maximal ideals is nilpotent and its quotient is `K`. Its spectrum
   therefore has one point, represented by the pair of units. Composition and inversion
   preserve the identity point and factor through the open component. Their laws restrict,
   as in def-a1-groupoid-scheme, by cancellation of the open inclusion.
5. Choose an affine neighbourhood of the image of `P` in `U ×_S U`. The self-product of
   `P` over that affine is a closed subscheme of its self-product over `K`, hence has
   exactly one point. By lem-weil-pbc-unramified-base-change-open its diagonal is open;
   it is surjective on this one-point space and hence an isomorphism. Thus the relation
   map on `P` is monic on every test-scheme Hom set.
6. By lem-weil-pbc-unramified-quasi-finite-at-points the relation map is locally
   quasi-finite. Its diagonal is a base change of the absolute closed diagonal of `Z`,
   hence closed by the affine quotient description of def-weil-closed-immersion.
   Finally the restricted unit, inverse and composition give reflexivity, symmetry and
   transitivity on every test scheme; monicity identifies `P` with this relation. -/
theorem fieldGroupoid_identity_finite_relation {S : Scheme.{u}} (K : Type u) [Field K]
    (b : Spec (CommRingCat.of K) ⟶ S) (R : AlgebraicSpace S)
    (s t : R.obj.obj ⟶ yoneda.obj (Over.mk b))
    (e : yoneda.obj (Over.mk b) ⟶ R.obj.obj) (i : R.obj.obj ⟶ R.obj.obj)
    (c : Limits.pullback s t ⟶ R.obj.obj) (_hgroupoid : IsPresheafGroupoid s t e i c)
    (_hs : ∀ (V : Over S) (a : yoneda.obj V ⟶ R.obj.obj), IsEtale a →
      LocallyOfFiniteType (yoneda.preimage (a ≫ s)).left)
    (_ht : ∀ (V : Over S) (a : yoneda.obj V ⟶ R.obj.obj), IsEtale a →
      LocallyOfFiniteType (yoneda.preimage (a ≫ t)).left)
    (_hj : ∀ (V W : Over S) (a : yoneda.obj V ⟶ R.obj.obj)
      (d : yoneda.obj W ⟶ yoneda.obj (Over.mk b) ⨯ yoneda.obj (Over.mk b))
      (f : V ⟶ W), IsEtale a → IsEtale d →
      a ≫ prod.lift s t = yoneda.map f ≫ d → IsUnramified f.left) :
    (IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (Limits.pullback.diagonal (prod.lift s t))) ∧
    (∀ (V W : Over S) (a : yoneda.obj V ⟶ R.obj.obj)
      (d : yoneda.obj W ⟶ yoneda.obj (Over.mk b) ⨯ yoneda.obj (Over.mk b))
      (f : V ⟶ W), IsEtale a → IsEtale d →
      a ≫ prod.lift s t = yoneda.map f ≫ d →
      LocallyOfFiniteType f.left ∧ LocallyQuasiFinite f.left) ∧
    ∃ (Z : Over S) (E : yoneda.obj Z ≅ R.obj.obj)
      (sz tz : Z ⟶ Over.mk b),
      Z.left.IsSeparated ∧ E.hom ≫ s = yoneda.map sz ∧ E.hom ≫ t = yoneda.map tz ∧
      (∀ z : Z.left, ∃ (V : Z.left.Opens) (A : CommRingCat.{u})
        (a : V.toScheme ≅ Spec A),
        (V : Set Z.left) = {z} ∧ IsClosed (V : Set Z.left) ∧
        IsLocalRing A ∧ IsArtinianRing A ∧
        (Spec.homEquiv (a.inv ≫ V.ι ≫ sz.left)).hom.Finite ∧
        (Spec.homEquiv (a.inv ≫ V.ι ≫ tz.left)).hom.Finite) ∧
      ∃ (P : Over S) (p : P ⟶ Z) (sp tp : P ⟶ Over.mk b)
        (ep : Over.mk b ⟶ P) (ip : P ⟶ P)
        (cp : Limits.pullback (yoneda.map sp) (yoneda.map tp) ⟶ yoneda.obj P)
        (B : CommRingCat.{u}) (a : P.left ≅ Spec B)
        (sigma tau : K →+* B) (epsilon : B →+* K),
        IsOpenImmersion p.left ∧ IsClosed (Set.range p.left) ∧ Subsingleton P.left ∧
        IsLocalRing B ∧ IsArtinianRing B ∧ sigma.Finite ∧ tau.Finite ∧
        a.inv ≫ sp.left = Spec.map (CommRingCat.ofHom sigma) ∧
        a.inv ≫ tp.left = Spec.map (CommRingCat.ofHom tau) ∧
        ep.left ≫ a.hom = Spec.map (CommRingCat.ofHom epsilon) ∧
        Function.Surjective epsilon ∧ (∀ x : B, epsilon x = 0 ↔ ¬ IsUnit x) ∧
        epsilon.comp sigma = RingHom.id K ∧ epsilon.comp tau = RingHom.id K ∧
        sp.left.IsFiniteLocallyFree ∧ tp.left.IsFiniteLocallyFree ∧
        IsPresheafGroupoid (yoneda.map sp) (yoneda.map tp) (yoneda.map ep)
          (yoneda.map ip) cp ∧
        yoneda.map p ≫ E.hom ≫ s = yoneda.map sp ∧
        yoneda.map p ≫ E.hom ≫ t = yoneda.map tp ∧
        yoneda.map ep ≫ yoneda.map p ≫ E.hom = e ∧
        yoneda.map ip ≫ yoneda.map p ≫ E.hom = yoneda.map p ≫ E.hom ≫ i ∧
        (∀ (H : Over S)
          (v : yoneda.obj H ⟶ Limits.pullback (yoneda.map sp) (yoneda.map tp))
          (w : yoneda.obj H ⟶ Limits.pullback s t),
          v ≫ Limits.pullback.fst (yoneda.map sp) (yoneda.map tp) ≫ yoneda.map p ≫ E.hom =
            w ≫ Limits.pullback.fst s t →
          v ≫ Limits.pullback.snd (yoneda.map sp) (yoneda.map tp) ≫ yoneda.map p ≫ E.hom =
            w ≫ Limits.pullback.snd s t →
          v ≫ cp ≫ yoneda.map p ≫ E.hom = w ≫ c) ∧
        (∀ (H : Over S) (v w : H ⟶ P),
          v ≫ sp = w ≫ sp → v ≫ tp = w ≫ tp → v = w) ∧
        (∀ H : Over S, Equivalence (fun v w : H ⟶ Over.mk b ↦
          ∃ r : H ⟶ P, r ≫ sp = v ∧ r ≫ tp = w)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
