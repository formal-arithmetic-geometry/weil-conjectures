/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids

/-! # Faithful relative sheaves over a stack

Source: Stacks Project, stacks.tex, Tag 0CKJ, lemma-relative-sheaf-over-stack-is-stack
(blueprint: lem-sfb-relative-sheaf-fibred-descent).

The relative sheaf condition is written in representatives, with compatibility and
uniqueness up to vertical isomorphism. No coherent choice of transition arrows is
required. All covering sieves and all objects of the slice are tested.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

namespace CategoryTheory

open AlgebraicGeometry

/-- A representative of a relative class over `h : V → T`. The arrow `comparison`
is the composite `q(x) → h*y → y`, where the first arrow is the inverse of the
isomorphism in the node. In a fibred groupoid the strongly cartesian property gives
this correspondence without choosing a cleavage. Thus these are precisely the
node's pairs `(x, φ : h*y ≅ q(x))`, with the comparison orientation inverted.
Source: Stacks 0CKJ, assumption (3)
(blueprint: lem-sfb-relative-sheaf-fibred-descent). -/
structure FibredRelativeSection
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (q : BasedFunctor F G) (y : G.obj) {V : Over S} (h : V ⟶ G.p.obj y) where
  obj : F.obj
  base : F.p.obj obj = V
  comparison : q.obj obj ⟶ y
  comparison_lift : G.p.IsHomLift h comparison

/-- Equality after restriction, expressed on representatives: an arrow over `a`
commuting with the two comparisons. For `a = 𝟙 V` this is exactly isomorphism of
relative pairs, since vertical arrows in a category fibred in groupoids are invertible.
For general `a`, the cartesian property identifies this with equality of the restricted
class and the source class. The existential quantifier deliberately forgets the arrow.
Source: Stacks 0CKJ, the isomorphisms and restrictions in assumption (3)
(blueprint: lem-sfb-relative-sheaf-fibred-descent). -/
def FibredRelativeSection.Restricts
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    {q : BasedFunctor F G} {y : G.obj} {V W : Over S}
    {h : V ⟶ G.p.obj y} {k : W ⟶ G.p.obj y} (a : V ⟶ W)
    (r : FibredRelativeSection q y h) (s : FibredRelativeSection q y k) : Prop :=
  ∃ c : r.obj ⟶ s.obj, F.p.IsHomLift a c ∧ q.map c ≫ s.comparison = r.comparison

/-- The relative isomorphism-class presheaves are étale sheaves. This is the usual
covering-sieve sheaf condition written on representatives: local classes match if
there exists a comparison arrow for every arrow of the sieve category; they glue to
a global representative, unique up to a vertical isomorphism commuting with the
comparison. Neither matching nor gluing chooses coherent comparison arrows.

Every object `h : V → T` of the slice is tested. Under the fibred-groupoid hypotheses,
vertical arrows are isomorphisms and any zigzag collapses to one such arrow, so this
is exactly unique gluing of classes, including for the empty covering sieve.
Source: Stacks 0CKJ, assumption (3), on the big étale site of S-schemes
(blueprint: lem-sfb-relative-sheaf-fibred-descent). -/
def HasEtaleSheafRelativeClasses
    {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (q : BasedFunctor F G) : Prop :=
  ∀ (y : G.obj) (V : Over S) (h : V ⟶ G.p.obj y)
    (R : Sieve V), R ∈ (Scheme.etaleTopology.over S) V →
    ∀ r : ∀ i : R.arrows.category, FibredRelativeSection q y (i.obj.hom ≫ h),
      (∀ (i j : R.arrows.category) (a : i ⟶ j),
        FibredRelativeSection.Restricts a.hom.left (r i) (r j)) →
      ∃ s : FibredRelativeSection q y h,
        (∀ i : R.arrows.category, FibredRelativeSection.Restricts i.obj.hom (r i) s) ∧
        ∀ t : FibredRelativeSection q y h,
          (∀ i : R.arrows.category, FibredRelativeSection.Restricts i.obj.hom (r i) t) →
          FibredRelativeSection.Restricts (𝟙 V) s t

/-- A faithful morphism to an étale stack with sheaves of relative classes has stack
source, without any representability or atlas hypothesis.
Source: Stacks Project, Tag 0CKJ, lemma-relative-sheaf-over-stack-is-stack
(blueprint: lem-sfb-relative-sheaf-fibred-descent).

Proof (the four steps of the node, using def-sfb-stable-pointed-moduli-groupoids):
1. If two isomorphisms of F agree locally, their images agree globally because G
   has isomorphism sheaves. Faithfulness of the fibre functor makes them equal.
   This proves separatedness over every scheme over the base.
2. Glue the images of a matching family a_i : x|i ≅ x'|i to b : q(x) ≅ q(x').
   The pairs (x,b⁻¹) and (x',id) in P_{q(x')} agree locally. Separatedness of that
   relative sheaf gives an isomorphism a of the representatives with q(a)=b.
   Fibrewise faithfulness identifies its restrictions with a_i; step 1 gives uniqueness.
3. For an object descent datum (x_i,d_ij), descent in G gives y and isomorphisms
   e_i : y|i ≅ q(x_i), with q(d_ij)e_j=e_i. These pairs give matching relative
   classes. All pullback comparisons are those of the recorded fibred-groupoid convention.
4. Glue those classes and choose a representative (x,e). Equality of its restricted
   classes with the local classes gives c_i : x|i ≅ x_i with q(c_i)e=e_i.
   On overlaps q(d_ij c_j)e=q(d_ij)e_j=e_i=q(c_i)e. Cancel e and use fibrewise
   faithfulness to get d_ij c_j=c_i. Thus the object datum is effective, and step 2
   supplies the isomorphism sheaf condition. No representability is used. -/
theorem isModuliStack_of_faithful_relative_sheaf
    {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S))
    (q : BasedFunctor F G)
    (hF : IsFibredInGroupoids F) (hG : IsModuliStack G)
    (hq : ∀ T : Over S, (moduliFiberMap q T).Faithful)
    (hrelative : HasEtaleSheafRelativeClasses q) : IsModuliStack F := by
  sorry

end CategoryTheory
