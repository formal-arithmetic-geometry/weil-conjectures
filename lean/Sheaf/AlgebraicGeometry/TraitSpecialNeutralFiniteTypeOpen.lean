/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Connected.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.DensePoints
import Sheaf.RingTheory.HenselianSmoothAlgebraLifting
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# The special-neutral open subgroup over a trait

Source: Raynaud, Specialisation du foncteur de Picard, printed pp.40-42,
(3.2)(d), (3.3.4), and the smooth sketch of (3.3.1); Stacks Project, Tag 0B7R
(blueprint: lem-sfb-trait-special-neutral-finite-type-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped MonObj CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The complement of the nonneutral special components is a finite-type open subgroup.
Its special neutral component commutes with field extension, it is invariant under
group-compatible faithfully flat trait descent, and over a strictly henselian trait
its translates by sections cover the group.

Source: Raynaud, Specialisation du foncteur de Picard, printed pp.40-42,
(3.2)(d), (3.3.4), and the smooth sketch of (3.3.1)
(blueprint: lem-sfb-trait-special-neutral-finite-type-open).

Proof:
1. Apply lem-sfb-lft-field-group-neutral-component to the special fibre. Its identity
component is clopen, finite type, a subgroup, and stable under every field extension.
Smoothness of the fibre follows from sbc-lem-smooth-criterion and lft base change.
2. The special fibre is closed, and its nonneutral components form a closed subset.
Their complement U is open and has exactly the stated generic and special fibres.
Multiplication, inverse and unit factor through U by checking the two fibres and
lem-weil-pbc-morphism-factors-through-open-subscheme. The group diagrams descend along
the monomorphic inclusion. Smooth open restriction and closed-immersion base change
for the diagonal give smoothness and separatedness.
3. Given an open cover, finite subfamilies cover the generic fibre and the special
neutral component. Together they cover U, since a DVR spectrum has just two points
(lem-weil-pbc-dvr-unit-times-uniformizer-power). Thus U is quasi-compact; smoothness
gives local finite presentation and hence local finite type. The only nonempty base
opens are the trait and its generic point, so the structure morphism is quasi-compact.
4. A faithfully flat DVR map is injective and sends a uniformizer to a unit times a
positive power of a uniformizer. On the overlap A tensor B A, either both projections
are generic or both are special at every point.
5. At a generic overlap point U is the whole fibre. At a special overlap point its
fibre is the identity component, by Step 1 for each of the two residue-field maps.
The group-compatible descent isomorphism preserves it. Equality on all residue-field
fibres gives equality of the underlying opens, hence of their open scheme structures.
The displayed equality uses the universal transport D.toHom of def-pd-descent-datum.
6. If A is strictly henselian, lem-sbc-fibre-component-neighbourhood and
lem-pc-rational-points-dense give a rational point in each special component. Choose
an affine smooth neighbourhood; lem-weil-pbc-smooth-ring-map-iff-smooth-affine and
lem-trf-henselian-smooth-algebra-lifting lift that point to an A-section. The affine
morphism correspondence and open factorization turn the lifted algebra map into a
section of J. No quasi-compactness of the whole group is needed.
7. Left translation by a section is an automorphism, with inverse translation by its
inverse. On the special fibre it sends the neutral component to the component of the
specialization of the section. Thus these open translates cover all special points;
the identity translate already contains every generic point. -/
theorem exists_trait_specialNeutral_finiteType_open
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
    (J : Over (Spec (.of A))) [GrpObj J] [Smooth J.hom] [IsSeparated J.hom]
    [LocallyOfFiniteType J.hom]
    [LocallyOfFiniteType
      (pullback.snd J.hom (Spec.map (CommRingCat.ofHom (algebraMap A L))))]
    [QuasiCompact
      (pullback.snd J.hom (Spec.map (CommRingCat.ofHom (algebraMap A L))))] :
    ∃ (C : ((Over.pullback (Spec.map
        (CommRingCat.ofHom (IsLocalRing.residue A)))).obj J).left.Opens)
      (U : J.left.Opens),
      (SetLike.coe C) = connectedComponent (GrpObj.onePoint
        ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).obj J)) ∧
      (U : Set J.left) =
        (pullback.fst J.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ''
          (SetLike.coe C)ᶜ)ᶜ ∧
      (∃ gU : GrpObj (Over.mk (U.ι ≫ J.hom)),
        @IsMonHom _ _ _ _ _ gU.toMonObj _ (Over.homMk (V := J) U.ι)) ∧
      Smooth (U.ι ≫ J.hom) ∧ IsSeparated (U.ι ≫ J.hom) ∧
      LocallyOfFiniteType (U.ι ≫ J.hom) ∧ QuasiCompact (U.ι ≫ J.hom) ∧
      (pullback.fst J.hom (Spec.map (CommRingCat.ofHom (algebraMap A L)))) ⁻¹'
        (U : Set J.left) = Set.univ ∧
      (pullback.fst J.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) ⁻¹'
        (U : Set J.left) = (SetLike.coe C) ∧
      (∀ (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField A) K],
        (pullback.fst
          ((Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).obj J).hom
          (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField A) K)))) ⁻¹'
          (SetLike.coe C) = connectedComponent (GrpObj.onePoint
            ((Over.pullback (Spec.map (CommRingCat.ofHom
              (algebraMap (IsLocalRing.ResidueField A) K)))).obj
              ((Over.pullback
                (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).obj J)))) ∧
      (∀ (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
        (φ : B →+* A), φ.FaithfullyFlat →
        ∀ D : Over.DescentDatum (Spec.map (CommRingCat.ofHom φ)) J,
        (∀ (Z : Scheme.{u}) (f₀ f₁ : Z ⟶ Spec (.of A))
          (h : f₀ ≫ Spec.map (CommRingCat.ofHom φ) =
            f₁ ≫ Spec.map (CommRingCat.ofHom φ)) (a b : Over.mk f₀ ⟶ J),
          D.transport f₀ f₁ h (lift a b ≫ μ[J]) =
            lift (D.transport f₀ f₁ h a) (D.transport f₀ f₁ h b) ≫ μ[J]) →
        (∀ (Z : Scheme.{u}) (f₀ f₁ : Z ⟶ Spec (.of A))
          (h : f₀ ≫ Spec.map (CommRingCat.ofHom φ) =
            f₁ ≫ Spec.map (CommRingCat.ofHom φ)),
          D.transport f₀ f₁ h (toUnit _ ≫ η[J]) = toUnit _ ≫ η[J]) →
        D.toHom ⁻¹' (U : Set J.left) =
          (pullback.fst (J.hom ≫ Spec.map (CommRingCat.ofHom φ))
            (Spec.map (CommRingCat.ofHom φ))) ⁻¹' (U : Set J.left)) ∧
      (IsStrictlyHenselianLocalRing A →
        (∀ l : 𝟙_ (Over (Spec (.of A))) ⟶ J,
          IsOpenImmersion
            (U.ι ≫ (lift (toUnit J ≫ l) (𝟙 J) ≫ μ[J]).left)) ∧
        ∀ x : J.left, ∃ l : 𝟙_ (Over (Spec (.of A))) ⟶ J,
          x ∈ (lift (toUnit J ≫ l) (𝟙 J) ≫ μ[J]).left '' (U : Set J.left)) := by
  sorry

end AlgebraicGeometry
