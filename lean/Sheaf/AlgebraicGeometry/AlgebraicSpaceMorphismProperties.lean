/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Morphism properties of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, definitions separated, locally-finite-type,
flat, locally-finite-presentation, open, closed and proper; Tags 03MM and 0410
(blueprint: def-sfb-space-morphism-properties).

Local properties are tested on every compatible pair of representable étale scheme charts.
Global properties use the existing point topology and canonical map on point classes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A scheme morphism property tested in all compatible étale scheme charts.
Source: Stacks, Morphisms of Spaces, lemma-local-source-target, Tag 03MM(7), Tag 0410(7)
(blueprint: def-sfb-space-morphism-properties). -/
def MapIsLocally {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj) (b : yoneda.obj V ⟶ Y.obj.obj)
    (h : U ⟶ V), IsEtale a → IsEtale b →
      a ≫ f.hom.hom = yoneda.map h ≫ b → P h.left

/-- Flatness on étale scheme charts, with the existing scheme flatness predicate.
Source: Stacks, Morphisms of Spaces, definition-flat and Tag 03MM(7)
(blueprint: def-sfb-space-morphism-properties). -/
def MapIsFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  MapIsLocally (@Flat) f

/-- Local finite presentation on étale scheme charts.
Source: Stacks, Morphisms of Spaces, definition-locally-finite-presentation and Tag 0410(7)
(blueprint: def-sfb-space-morphism-properties). -/
def MapIsLocallyOfFinitePresentation {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  MapIsLocally (@LocallyOfFinitePresentation) f

/-- Separated means that the relative diagonal is representable by closed immersions.
Source: Stacks, Morphisms of Spaces, definition-separated
(blueprint: def-sfb-space-morphism-properties). -/
def MapIsSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal f.hom.hom)

/-- Finite type means quasi-compact and locally of finite type on étale scheme charts.
Source: Stacks, Morphisms of Spaces, definition-locally-finite-type
(blueprint: def-sfb-space-morphism-properties). -/
def MapIsFiniteType {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  MapIsQuasiCompact f.hom.hom ∧ MapIsLocally (@LocallyOfFiniteType) f

/-- Universal closedness is closedness on points after every algebraic-space base change.
The sheaf fibre product is an algebraic space by `fibreProduct_isAlgebraicSpace`.
Source: Stacks, Morphisms of Spaces, definition-closed
(blueprint: def-sfb-space-morphism-properties). -/
def MapIsUniversallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
    IsClosedMap (mapPoint (Limits.pullback.snd f.hom g.hom).hom)

/-- Proper means separated, of finite type and universally closed.
Source: Stacks, Morphisms of Spaces, definition-proper
(blueprint: def-sfb-space-morphism-properties). -/
def MapIsProper {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  MapIsSeparated f ∧ MapIsFiniteType f ∧ MapIsUniversallyClosed f

/-- Universal openness is openness on points after every algebraic-space base change.
The sheaf fibre product is an algebraic space by `fibreProduct_isAlgebraicSpace`.
Source: Stacks, Morphisms of Spaces, definition-open
(blueprint: def-sfb-space-morphism-properties). -/
def MapIsUniversallyOpen {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
    IsOpenMap (mapPoint (Limits.pullback.snd f.hom g.hom).hom)

end AlgebraicGeometry.AlgebraicSpace
