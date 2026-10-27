/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.KrullDimension

/-! # The category of proper families of curves

Source: Stacks Project, moduli-curves.tex, section-stack-curves, and quot.tex,
situation-curves; spaces-morphisms.tex, definitions of flatness, properness, finite
presentation and relative dimension (blueprint: def-sfb-proper-curve-moduli).

Families retain algebraic-space sources. Morphisms are cartesian squares of sheaves,
rather than maps of sets of isomorphism classes. Global properties use the existing
field-valued point classes and their topology; local properties use etale scheme charts.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace AlgebraicSpace

/-- The induced map on the already defined point classes.
Source: Stacks, Properties of Spaces, Tag 03BU
(blueprint: def-sfb-proper-curve-moduli). -/
def mapPoint {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    Point F → Point G :=
  Quot.map (fun p ↦ p.map f) (by
    rintro p q ⟨L, hL, s, a, b, h⟩
    refine ⟨L, hL, s, a, b, ?_⟩
    change G.map a.op (f.app _ p.value) = G.map b.op (f.app _ q.value)
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, h])

/-- Quasi-compactness tested over affine schemes. The fibre products are actual
presheaf fibre products, with the existing algebraic-space topology on their points.
Source: Stacks, Morphisms of Spaces, definition of quasi-compact
(blueprint: def-sfb-proper-curve-moduli). -/
def MapIsQuasiCompact {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) : Prop :=
  ∀ (T : Over S) (a : yoneda.obj T ⟶ G), IsAffine T.left →
    CompactSpace (Point (Limits.pullback f a))

/-- Local properties of a map to a scheme, tested on every representable etale chart.
Source: Stacks, Morphisms of Spaces, etale-local properties
(blueprint: def-sfb-proper-curve-moduli). -/
def MapToSchemeIsLocally {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    (X : AlgebraicSpace S) (T : Over S) (f : X.obj.obj ⟶ yoneda.obj T) : Prop :=
  ∀ (U : Over S) (a : yoneda.obj U ⟶ X.obj.obj), IsEtale a →
    P ((yoneda.preimage (a ≫ f)).left)

/-- Separatedness is representability of the relative diagonal by closed immersions.
Source: Stacks, Morphisms of Spaces, definition of separated
(blueprint: def-sfb-proper-curve-moduli). -/
def MapToSchemeIsSeparated {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T) : Prop :=
  IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal f)

/-- Universal closedness uses the induced maps on points after every scheme base change.
Source: Stacks, Morphisms of Spaces, definition of universally closed
(blueprint: def-sfb-proper-curve-moduli). -/
def MapToSchemeIsUniversallyClosed {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T) : Prop :=
  ∀ (U : Over S) (a : U ⟶ T),
    IsClosedMap (mapPoint (pullback.snd f (yoneda.map a)))

/-- Flat, proper, finitely presented morphisms to a scheme, with all geometric fibres
of dimension at most one. Proper means separated, finite type and universally closed;
finite presentation means quasi-compact, quasi-separated and locally finitely presented.
Source: Stacks, moduli-curves.tex, section-stack-curves; quot.tex, situation-curves
(blueprint: def-sfb-proper-curve-moduli). -/
def IsProperCurveFamily {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Over S)
    (f : X.obj.obj ⟶ yoneda.obj T) : Prop :=
  MapToSchemeIsLocally (@Flat) X T f ∧
  MapToSchemeIsSeparated X T f ∧
  MapIsQuasiCompact f ∧
  MapToSchemeIsLocally (@LocallyOfFiniteType) X T f ∧
  MapToSchemeIsUniversallyClosed X T f ∧
  MapIsQuasiCompact (pullback.diagonal f) ∧
  MapToSchemeIsLocally (@LocallyOfFinitePresentation) X T f ∧
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (a : Spec (.of Ω) ⟶ T.left),
    topologicalKrullDim (Point (Limits.pullback f (yoneda.map (Over.homMk
      (U := Over.mk (a ≫ T.hom)) (V := T) a rfl)))) ≤ 1

end AlgebraicSpace

/-- An actual algebraic-space family of proper curves over the specified base scheme.
No reducedness, connectedness, purity, nonemptiness or stability condition is imposed.
Source: Stacks, moduli-curves.tex, section-stack-curves
(blueprint: def-sfb-proper-curve-moduli). -/
structure ProperCurveFamily {S : Scheme.{u}} (T : Over S) where
  space : AlgebraicSpace S
  projection : space.obj.obj ⟶ yoneda.obj T
  isCurve : AlgebraicSpace.IsProperCurveFamily space T projection

/-- The total objects of the moduli category, retaining their base schemes.
Source: Stacks, moduli-curves.tex, section-stack-curves
(blueprint: def-sfb-proper-curve-moduli). -/
structure ProperCurveModuli (S : Scheme.{u}) where
  base : Over S
  family : ProperCurveFamily base

namespace ProperCurveModuli

/-- A cartesian arrow is the usual isomorphism to the base-changed family.
Source: Stacks, moduli-curves.tex, section-stack-curves, and Stacks 003T
(blueprint: def-sfb-proper-curve-moduli). -/
@[ext]
structure Hom {S : Scheme.{u}} (X Y : ProperCurveModuli S) where
  base : X.base ⟶ Y.base
  map : X.family.space.obj.obj ⟶ Y.family.space.obj.obj
  square : IsPullback map X.family.projection Y.family.projection (yoneda.map base)

/-- Identities and pasting preserve cartesian arrows.
Source: Stacks 003T, uniqueness and pasting of fibre products
(blueprint: def-sfb-proper-curve-moduli).
Proof: the identity square is a pullback. Pasting two pullback squares produces the
pullback square for the composite; Yoneda preserves composition. These proof fields
uniquely determine the cartesian-arrow structure and do not choose mathematical data. -/
theorem hom_operations {S : Scheme.{u}} :
    (∀ X : ProperCurveModuli S,
      IsPullback (𝟙 X.family.space.obj.obj) X.family.projection X.family.projection
        (yoneda.map (𝟙 X.base))) ∧
    (∀ {X Y Z : ProperCurveModuli S} (a : Hom X Y) (b : Hom Y Z),
      IsPullback (a.map ≫ b.map) X.family.projection Z.family.projection
        (yoneda.map (a.base ≫ b.base))) := by
  constructor
  · intro X
    simpa only [CategoryTheory.Functor.map_id] using IsPullback.id_horiz X.family.projection
  · intro X Y Z a b
    simpa only [Functor.map_comp] using a.square.paste_horiz b.square

/-- The category with the specified actual identity and composite arrows.
Source: Stacks 003T (blueprint: def-sfb-proper-curve-moduli). -/
instance {S : Scheme.{u}} : Category (ProperCurveModuli S) where
  Hom := Hom
  id X := ⟨𝟙 X.base, 𝟙 _, hom_operations.1 X⟩
  comp a b := ⟨a.base ≫ b.base, a.map ≫ b.map, hom_operations.2 a b⟩
  id_comp _a := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _a := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _a _b _c := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Projection to schemes over the base.
Source: Stacks 003T (blueprint: def-sfb-proper-curve-moduli). -/
def forget (S : Scheme.{u}) : ProperCurveModuli S ⥤ Over S where
  obj X := X.base
  map a := a.base

/-- The concrete category over schemes whose fibres are the groupoids of proper curves.
Source: Stacks, moduli-curves.tex, section-stack-curves
(blueprint: def-sfb-proper-curve-moduli). -/
def category (S : Scheme.{u}) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (forget S)

end ProperCurveModuli

namespace ProperCurveFamily

/-- The dual-number test scheme, with its specified base morphism.
Source: Stacks, moduli-curves.tex, proof of Tag 0E6G
(blueprint: def-sfb-proper-curve-moduli). -/
def dualBase {S : Scheme.{u}} (Ω : Type u) [Field Ω] (a : Spec (.of Ω) ⟶ S) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω)) ≫ a)

/-- The projection of the dual-number test scheme to its reduced base.
Source: Stacks, moduli-curves.tex, proof of Tag 0E6G
(blueprint: def-sfb-proper-curve-moduli). -/
def dualProjection {S : Scheme.{u}} (Ω : Type u) [Field Ω] (a : Spec (.of Ω) ⟶ S) :
    dualBase Ω a ⟶ Over.mk a :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω))) rfl

/-- Identity reduction into the dual-number base, setting epsilon equal to zero.
Source: Stacks, moduli-curves.tex, proof of Tag 0E6G
(blueprint: def-sfb-proper-curve-moduli). -/
def dualReduction {S : Scheme.{u}} (Ω : Type u) [Field Ω] (a : Spec (.of Ω) ⟶ S) :
    Over.mk a ⟶ dualBase Ω a :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom)) (by
    have h : CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω) ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom = 𝟙 (CommRingCat.of Ω) := by
      ext x
      rfl
    change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω)) ≫ a) = a
    rw [← Category.assoc, ← Spec.map_comp, h]
    simp)

/-- The canonical map from a presheaf to its constant dual-number thickening.
Source: Stacks, moduli-curves.tex, proof of Tag 0E6G
(blueprint: def-sfb-proper-curve-moduli). -/
def infinitesimalReduction {S : Scheme.{u}} (Ω : Type u) [Field Ω]
    (a : Spec (.of Ω) ⟶ S) {F : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ yoneda.obj (Over.mk a)) :
    F ⟶ pullback f (yoneda.map (dualProjection Ω a)) :=
  pullback.lift (𝟙 F) (f ≫ yoneda.map (dualReduction Ω a)) (by
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp]
    have h : dualReduction Ω a ≫ dualProjection Ω a = 𝟙 (Over.mk a) := by
      apply Over.OverMorphism.ext
      have hring : CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom = 𝟙 (CommRingCat.of Ω) := by
        ext x
        rfl
      change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom Ω Ω)) = 𝟙 _
      rw [← Spec.map_comp, hring]
      simp
    rw [h, CategoryTheory.Functor.map_id, Category.comp_id])

/-- Every automorphism over the dual numbers which reduces to the identity is the
identity. The second equation fixes the dual-number base, not the projection to the
original curve; the first is exactly reduction to the identity on that curve.
Source: Stacks, moduli-curves.tex, first proof paragraph of Tag 0E6G
(blueprint: def-sfb-proper-curve-moduli). -/
def HasTrivialInfinitesimalAutomorphisms {S : Scheme.{u}} (Ω : Type u) [Field Ω]
    (a : Spec (.of Ω) ⟶ S) {F : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ yoneda.obj (Over.mk a)) : Prop :=
  ∀ α : Aut (pullback f (yoneda.map (dualProjection Ω a))),
    infinitesimalReduction Ω a f ≫ α.hom = infinitesimalReduction Ω a f →
    α.hom ≫ pullback.snd f (yoneda.map (dualProjection Ω a)) =
      pullback.snd f (yoneda.map (dualProjection Ω a)) → α = Iso.refl _

end ProperCurveFamily

end AlgebraicGeometry
