/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence

/-! # The unramified open locus of an algebraic-space morphism

Source: Stacks Project, Morphisms of Spaces, Tag 05W2 (lemma-where-unramified),
specialized to Z = Y (blueprint: lem-sfb-space-unramified-locus-base-change).

An open subspace is displayed by its algebraic space and its representable open inclusion.
Its subfunctor is `Subfunctor.range` of that inclusion. Equality after base change is
literal equality of these subfunctors, for any sheaf pullback square.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The largest unramified source open exists and commutes with arbitrary base change.
Unramifiedness at a point means membership in an unramified open neighbourhood, expanded
in the point clause. The final clause uses an arbitrary pullback presentation, so includes
the chosen fibre product and all its canonically isomorphic presentations.

Source: Stacks Project, Morphisms of Spaces, Tag 05W2, specialized to Z = Y;
Definition 03ZH (blueprint: lem-sfb-space-unramified-locus-base-change).

Proof:
1. Choose a surjective etale scheme atlas V of Y. By
   lem-sfb-unramified-etale-compatible-charts choose a compatible surjective etale
   scheme chart A of X with g : A → V. The locally finite type hypothesis makes g
   locally of finite type. Take T to be its unramified open, as in
   lem-trf-unramified-locus-base-change.
2. The restriction to T is unramified: its defining unramified opens cover T, local
   finite type is source local, and their open diagonals glue to the diagonal over T.
   This includes the empty open (def-weil-unramified-morphism).
3. Restriction of the atlas to T is representable etale by
   lem-weil-pbc-etale-composition-cancellation. By lem-a1-space-etale-open-image its
   image is an open subspace I of X and T → I is surjective etale. Compatible chart
   locality (lem-sfb-unramified-etale-compatible-charts) makes I → Y unramified.
4. Every unramified open N pulls back to an open A_N of A, by
   lem-a1-space-open-factor-scheme-tests. Chart locality puts A_N inside T. Atlas
   surjectivity and lem-a1-space-point-open-calculus give N ⊆ I as subfunctors.
   Thus I is largest and its points are precisely those with an unramified neighbourhood.
   The same argument gives the saturation identity a⁻¹(I) = T.
5. For an arbitrary Y' → Y, local finite type persists by
   lem-sfb-stack-chartwise-smooth-etale-calculus. Choose a scheme atlas V' of V ×_Y Y'
   and put A' = A ×_V V'. The fibre-product and chartwise-etale permanence lemmas
   lem-trf-space-fibre-products-etale-covers and lem-trf-space-chartwise-etale-permanence
   make A' and V' compatible surjective etale charts of the base change.
6. The scheme equality of lem-trf-unramified-locus-base-change identifies T' with the
   inverse image of T. Apply steps 1–4 upstairs and use both saturation identities.
   Surjectivity of A' on points makes I' the inverse image of I on points.
   lem-a1-space-open-factor-scheme-tests identifies the pullback open point set, and
   lem-a1-space-point-open-calculus upgrades this to equality of open subfunctors. -/
theorem exists_unramified_open_baseChange {S : Scheme.{u}} (X Y : AlgebraicSpace S)
    (f : X ⟶ Y) (hf : MapIsLocally (@LocallyOfFiniteType) f) :
    ∃ (U : AlgebraicSpace S) (j : U ⟶ X),
      IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) j.hom.hom ∧
      MapIsLocally (@AlgebraicGeometry.IsUnramified) (j ≫ f) ∧
      (∀ (V : AlgebraicSpace S) (i : V ⟶ X),
        IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) i.hom.hom →
        MapIsLocally (@AlgebraicGeometry.IsUnramified) (i ≫ f) →
        Subfunctor.range i.hom.hom ≤ Subfunctor.range j.hom.hom) ∧
      (∀ x : Point X.obj.obj, x ∈ pointImage j.hom.hom ↔
        ∃ (V : AlgebraicSpace S) (i : V ⟶ X),
          IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) i.hom.hom ∧
          MapIsLocally (@AlgebraicGeometry.IsUnramified) (i ≫ f) ∧
          x ∈ pointImage i.hom.hom) ∧
      (∀ (Y' : AlgebraicSpace S) (h : Y' ⟶ Y) (X' : AlgebraicSpace S)
        (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p.hom f'.hom f.hom h.hom →
        ∃ (U' : AlgebraicSpace S) (j' : U' ⟶ X'),
          IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) j'.hom.hom ∧
          MapIsLocally (@AlgebraicGeometry.IsUnramified) (j' ≫ f') ∧
          (∀ (V : AlgebraicSpace S) (i : V ⟶ X'),
            IsRepresentableWith (fun _ _ q ↦ IsOpenImmersion q.left) i.hom.hom →
            MapIsLocally (@AlgebraicGeometry.IsUnramified) (i ≫ f') →
            Subfunctor.range i.hom.hom ≤ Subfunctor.range j'.hom.hom) ∧
          Subfunctor.range j'.hom.hom =
            (Subfunctor.range j.hom.hom).preimage p.hom.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
