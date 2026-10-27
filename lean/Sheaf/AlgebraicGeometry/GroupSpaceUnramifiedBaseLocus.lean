/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-!
# The maximal unramified base locus of a group algebraic space

Source: Stacks Project, `spaces-groupoids.tex`, Tag 0DSJ, part (1)
(blueprint: lem-sfb-group-space-unramified-base-locus).

The group structure is Mathlib's `GrpObj` structure on the object of `Over B`; it
therefore supplies multiplication, identity, inverse, and the group identities.
Open subspaces are expressed by the existing scheme-test predicate
`AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)`.
The universal containment clauses express the largest open subspace and its
compatibility with arbitrary base change.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite type group algebraic space has a largest unramified base open,
compatible with arbitrary base change.

Source: Stacks, Tag 0DSJ(1)
(blueprint: lem-sfb-group-space-unramified-base-locus).

Proof:
1. Fibre products give the base-changed space, with the pulled-back group structure.
   The chartwise calculus gives local finite type after arbitrary base change
   [lem-trf-space-fibre-products-etale-covers,
   lem-sfb-stack-chartwise-smooth-etale-calculus].
2. Pull the maximal source unramified open back along the identity section. This
   is open by its scheme tests [lem-sfb-space-unramified-locus-base-change,
   def-weil-open-immersion].
3. The identity on this restriction lies in its source unramified locus. The group
   identity test makes the entire restriction unramified
   [lem-sfb-group-space-unramified-identity-test].
4. Any admissible base open has its entire restricted source in the source locus.
   Composing with its identity gives its factorization through the constructed base
   open [lem-sfb-space-unramified-locus-base-change].
5. The source locus commutes with arbitrary base change. Pullback of the identity
   section commutes with it too, so the same construction is the pullback of the
   original base open [lem-sfb-space-unramified-locus-base-change,
   lem-trf-space-fibre-products-etale-covers].
The fibre-product and scheme-test assertions use
`lem-trf-space-fibre-products-etale-covers`; local finite type and unramifiedness
are the chartwise notions from `AlgebraicSpace.MapIsLocally` and
`AlgebraicGeometry.IsUnramified`. -/
theorem groupSpace_unramified_base_locus {S : Scheme.{u}} (B G : AlgebraicSpace S)
    (q : G ⟶ B)
    [@GrpObj (Over B.obj) _ (Over.cartesianMonoidalCategory B.obj) (Over.mk q.hom)]
    (hlft : MapIsLocally (@LocallyOfFiniteType) q) :
    ∃ (V : AlgebraicSpace S) (v : V ⟶ B),
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) v.hom.hom ∧
      MapIsLocally (@IsUnramified) (enlargedFibreProductFst v q) ∧
      (∀ (W : AlgebraicSpace S) (w : W ⟶ B),
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) w.hom.hom →
        MapIsLocally (@IsUnramified) (enlargedFibreProductFst w q) →
        ∃ i : W ⟶ V, i ≫ v = w) ∧
      (∀ (B' : AlgebraicSpace S) (h : B' ⟶ B),
        MapIsLocally (@LocallyOfFiniteType) (enlargedFibreProductFst h q) ∧
        MapIsLocally (@IsUnramified)
          (enlargedFibreProductFst (enlargedFibreProductFst h v)
            (enlargedFibreProductFst h q)) ∧
        (∀ (W : AlgebraicSpace S) (w : W ⟶ B'),
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) w.hom.hom →
          (MapIsLocally (@IsUnramified)
              (enlargedFibreProductFst w (enlargedFibreProductFst h q)) ↔
            ∃ i : W ⟶ enlargedFibreProduct h v,
              i ≫ enlargedFibreProductFst h v = w))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
