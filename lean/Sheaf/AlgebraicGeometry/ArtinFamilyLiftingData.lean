/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Artinian lifting for a family over an arbitrary affine base

Source: Stacks Project, artin.tex, Tags 07WP (definition-RS), 07XF
(definition-versal), and equation-smooth
(blueprint: def-sfb-artin-family-lifting-data).

We retain objects and arrows in the existing total category. For a category fibred
in groupoids an arrow over a base map is precisely a pullback identification.
A pushout of these arrows is the total-category formulation of the canonical
restriction equivalence, including full faithfulness on all isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory.ArtinFamily

/-- Rim--Schlessinger gluing over the given affine base. All four spectra are
Artinian local and of finite type over that base. The object on the overlap and
its two arrows encode an arbitrary specified gluing isomorphism. The total-category
pushout asserts unique gluing of arrows as well as existence of the glued object.
For a target over any base, first glue its base maps by the base pushout and then
pull back the target; full faithfulness of the fibre restriction is exactly the
remaining universal property. Thus this is the canonical restriction equivalence.
Source: Stacks Project, Tag 07WP (definition-RS)
(blueprint: def-sfb-artin-family-lifting-data). -/
def IsRimSchlessinger (R : CommRingCat.{u})
    (F : BasedCategory.{v, w} (Over (Spec R))) : Prop :=
  ∀ (A B C D : CommRingCat.{u})
    [IsLocalRing A] [IsArtinianRing A] [IsLocalRing B] [IsArtinianRing B]
    [IsLocalRing C] [IsArtinianRing C] [IsLocalRing D] [IsArtinianRing D]
    (sA : Spec A ⟶ Spec R) (sB : Spec B ⟶ Spec R)
    (sC : Spec C ⟶ Spec R) (sD : Spec D ⟶ Spec R),
    LocallyOfFiniteType sA → QuasiCompact sA →
    LocallyOfFiniteType sB → QuasiCompact sB →
    LocallyOfFiniteType sC → QuasiCompact sC →
    LocallyOfFiniteType sD → QuasiCompact sD →
    ∀ (q : C ⟶ A), Function.Surjective q.hom → IsNilpotent (RingHom.ker q.hom) →
    ∀ (i : Over.mk sA ⟶ Over.mk sB) (j : Over.mk sA ⟶ Over.mk sC),
    j.left = Spec.map q →
    ∀ (k : Over.mk sB ⟶ Over.mk sD) (l : Over.mk sC ⟶ Over.mk sD),
    IsPushout i j k l →
    ∀ (x : Functor.Fiber F.p (Over.mk sA)) (y : Functor.Fiber F.p (Over.mk sB))
      (z : Functor.Fiber F.p (Over.mk sC)) (a : x.val ⟶ y.val) (b : x.val ⟶ z.val),
    F.p.IsHomLift i a → F.p.IsHomLift j b →
    ∃ (t : Functor.Fiber F.p (Over.mk sD)) (c : y.val ⟶ t.val) (d : z.val ⟶ t.val),
      F.p.IsHomLift k c ∧ F.p.IsHomLift l d ∧ IsPushout a b c d

/-- Artinian lifting at the specified field-valued point of a family. The surjection
`r` identifies the residue field of `B` with the field `K` (a type with Mathlib's
`Field` structure, so that its ring structure is the field's own), and `q ≫ r` gives
the identification for `B'`; no embedding of the residue field into either ring is required. The map
`s'` gives the R-algebra structure, and all family maps are over `Spec R`.
The two arrows from `y` encode a deformation and its prescribed identification
with the family over `B`. The final equation requires that exact identification
to extend. Surjections of Artinian local rings automatically have nilpotent kernel.
Source: Stacks Project, Tag 07XF (definition-versal), equation-hat-x,
and equation-smooth (blueprint: def-sfb-artin-family-lifting-data). -/
def HasLiftingAt (R : CommRingCat.{u}) (F : BasedCategory.{v, w} (Over (Spec R)))
    (U : Over (Spec R)) (x : Functor.Fiber F.p U)
    (K : Type u) [Field K] (α : Spec (.of K) ⟶ U.left) : Prop :=
  ∀ (B' B : CommRingCat.{u}) [IsArtinianRing B'] [IsLocalRing B']
    [IsArtinianRing B] [IsLocalRing B] (q : B' ⟶ B),
    Function.Surjective q.hom →
    ∀ (r : B ⟶ .of K), Function.Surjective r.hom →
    ∀ (s' : Spec B' ⟶ Spec R) (a : Over.mk (Spec.map q ≫ s') ⟶ U),
    Spec.map r ≫ a.left = α →
    ∀ (y' : Functor.Fiber F.p (Over.mk s'))
      (y : Functor.Fiber F.p (Over.mk (Spec.map q ≫ s')))
      (b : y.val ⟶ y'.val) (c : y.val ⟶ x.val),
    F.p.IsHomLift
      (Over.homMk (Spec.map q) rfl : Over.mk (Spec.map q ≫ s') ⟶ Over.mk s') b →
    F.p.IsHomLift a c →
    ∃ (a' : Over.mk s' ⟶ U) (d : y'.val ⟶ x.val),
      Spec.map q ≫ a'.left = a.left ∧ F.p.IsHomLift a' d ∧ b ≫ d = c

/-- Versality at a scheme point is Artinian lifting with its actual residue field
and canonical residue-field map. Finite-type-ness of the point is a separate
hypothesis on uses of this predicate.
Source: Stacks Project, Tag 07XF (definition-versal)
(blueprint: def-sfb-artin-family-lifting-data). -/
def IsVersalAt (R : CommRingCat.{u}) (F : BasedCategory.{v, w} (Over (Spec R)))
    (U : Over (Spec R)) (x : Functor.Fiber F.p U) (p : U.left) : Prop :=
  HasLiftingAt R F U x (U.left.residueField p) (U.left.fromSpecResidueField p)

end CategoryTheory.ArtinFamily
