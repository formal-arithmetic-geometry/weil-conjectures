/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Group.Hom.Basic

/-! # Smooth separated commutative group algebraic spaces

Source: Deligne, Le lemme de Gabber, Sections 1.1 and 4.2, printed pp.131 and 142;
Stacks, Morphisms of Spaces, smoothness and geometric fibres
(blueprint: def-sfb-smooth-integral-group-space).

A group law is a natural commutative group structure on the functor of points. This
includes its actual multiplication, inverse and identity. Integral geometric fibres
are reduced on every étale chart and irreducible on the existing point topology.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The represented base of the category of spaces over `S`.
Source: Stacks, Tag 025Y (blueprint: def-sfb-smooth-integral-group-space). -/
abbrev groupSpaceBase (S : Scheme.{u}) : AlgebraicSpace S := schemeSpace (Over.mk (𝟙 S))

/-- Yoneda sends an actual morphism of schemes over the base to its space morphism.
Source: Stacks, Tag 025Y (blueprint: def-sfb-smooth-integral-group-space). -/
def groupSchemeMap {S : Scheme.{u}} {T U : Over S} (f : T ⟶ U) :
    schemeSpace T ⟶ schemeSpace U :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over S).yoneda.map f)

/-- The unique structural morphism to the base, obtained from the terminal property.
Source: Stacks, Tag 025Y (blueprint: def-sfb-smooth-integral-group-space). -/
def groupSpaceProjection {S : Scheme.{u}} (G : AlgebraicSpace S) :
    G ⟶ groupSpaceBase S :=
  ObjectProperty.homMk ⟨{
    app := fun T ↦ ↾fun _ ↦ Over.homMk T.unop.hom (by simp)
    naturality := by
      intro T U a
      ext x
      apply Over.OverMorphism.ext
      exact a.unop.w.symm }⟩

/-- A natural commutative group law on a space's functor of points.
Source: Deligne 1.1 (blueprint: def-sfb-smooth-integral-group-space). -/
structure CommutativeSpaceGroup {S : Scheme.{u}} (G : AlgebraicSpace S) where
  /-- Multiplication, inverse, identity and all commutative group identities. -/
  group (T : (Over S)ᵒᵖ) : CommGroup (G.obj.obj.obj T)
  /-- Restriction respects multiplication. -/
  map_mul {T U : (Over S)ᵒᵖ} (f : T ⟶ U) (x y : G.obj.obj.obj T) :
    G.obj.obj.map f (@Mul.mul _ (group T).toMul x y) =
      @Mul.mul _ (group U).toMul (G.obj.obj.map f x) (G.obj.obj.map f y)
  /-- Restriction respects the identity. -/
  map_one {T U : (Over S)ᵒᵖ} (f : T ⟶ U) :
    G.obj.obj.map f (@One.one _ (group T).toOne) = @One.one _ (group U).toOne

/-- The identity section is the identity element on every test scheme.
Source: Deligne 1.1 (blueprint: def-sfb-smooth-integral-group-space). -/
def CommutativeSpaceGroup.identity {S : Scheme.{u}} {G : AlgebraicSpace S}
    (H : CommutativeSpaceGroup G) : groupSpaceBase S ⟶ G :=
  ObjectProperty.homMk ⟨{
    app := fun T ↦ ↾fun _ ↦ @One.one _ (H.group T).toOne
    naturality := by
      intro T U f
      ext x
      exact (H.map_one f).symm }⟩

/-- A geometric fibre is reduced on all étale charts and irreducible on its point space.
Smoothness is imposed separately, so reducedness could also be deduced there.
Source: Stacks, Properties of Spaces, geometric integrality; Deligne 4.2
(blueprint: def-sfb-smooth-integral-group-space). -/
def GroupSpaceIntegralFibres {S : Scheme.{u}} (G : AlgebraicSpace S) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
    IrreducibleSpace (Point (Limits.pullback (groupSpaceProjection G).hom.hom
      (yoneda.map (Over.homMk (U := Over.mk s) (V := Over.mk (𝟙 S)) s
        (by simp))))) ∧
    ∀ (T : Over S)
      (a : yoneda.obj T ⟶ Limits.pullback (groupSpaceProjection G).hom.hom
        (yoneda.map (Over.homMk (U := Over.mk s) (V := Over.mk (𝟙 S)) s
          (by simp)))),
      IsEtale a → IsReduced T.left

/-- The geometric hypotheses on the group map: smoothness on étale charts, separated
relative diagonal, finite presentation (local finite presentation, quasi-compactness,
quasi-separatedness) and geometrically integral fibres.
Source: Deligne 1.1 and 4.2 (blueprint: def-sfb-smooth-integral-group-space). -/
def IsSmoothIntegralGroupSpace {S : Scheme.{u}} (G : AlgebraicSpace S) : Prop :=
  MapIsLocally (@Smooth) (groupSpaceProjection G) ∧
  MapIsSeparated (groupSpaceProjection G) ∧
  MapIsLocallyOfFinitePresentation (groupSpaceProjection G) ∧
  MapIsQuasiCompact (groupSpaceProjection G).hom.hom ∧
  MapIsQuasiCompact (pullback.diagonal (groupSpaceProjection G).hom.hom) ∧
  GroupSpaceIntegralFibres G

end AlgebraicGeometry.AlgebraicSpace
