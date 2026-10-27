/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalSingularityPair
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Rational smooth model systems of principal pairs

Source: Temkin, Non-embedded Desingularization, proof of Proposition 3.3.5, printed p.25
(blueprint: def-per-rational-smooth-pair-system).
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A directed system of rational principal singularity pairs with regular limit
projections, including the specified inverse limits of every positive thick fibre.
The fibre diagrams are identified with the actual closed subschemes cut out by powers
of the model ideals. Their inclusions form a natural transformation. The commuting
projection squares determine the fibre projections uniquely, since closed immersions
are monomorphisms; no arbitrary comparison map is substituted for quotient base change.
Source: Temkin proof of Proposition 3.3.5, p.25
(blueprint: def-per-rational-smooth-pair-system). -/
structure RationalSmoothPairSystem (X : Scheme.{u}) (I : X.IdealSheafData) where
  Index : Type u
  [partialOrder : PartialOrder Index]
  [nonempty : Nonempty Index]
  [directed : IsDirected Index (· ≤ ·)]
  diagram : Indexᵒᵖ ⥤ Scheme.{u}
  ideal : ∀ a : Indexᵒᵖ, (diagram.obj a).IdealSheafData
  pair : ∀ a, IsPrincipalSingularityPair (diagram.obj a) (ideal a)
  rationalMap : diagram ⟶ (Functor.const Indexᵒᵖ).obj (Spec (.of (ULift.{u} ℚ)))
  finiteType : ∀ a, LocallyOfFiniteType (rationalMap.app a)
  quasiCompact : ∀ a, QuasiCompact (rationalMap.app a)
  transitionAffine : ∀ {a b : Indexᵒᵖ} (f : a ⟶ b), IsAffineHom (diagram.map f)
  transitionSmooth : ∀ {a b : Indexᵒᵖ} (f : a ⟶ b), Smooth (diagram.map f)
  transitionIdeal : ∀ {a b : Indexᵒᵖ} (f : a ⟶ b),
    (ideal b).comap (diagram.map f) = ideal a
  projection : (Functor.const Indexᵒᵖ).obj X ⟶ diagram
  projectionIdeal : ∀ a, (ideal a).comap (projection.app a) = I
  projectionRegular : ∀ a, IsRegularSchemeMorphism (projection.app a)
  isLimit : IsLimit (Cone.mk X projection)
  thickDiagram : ℕ → Indexᵒᵖ ⥤ Scheme.{u}
  thickIso : ∀ (m : ℕ) (a : Indexᵒᵖ),
    (thickDiagram m).obj a ≅ (ideal a ^ m).subscheme
  thickInclusion : ∀ m, thickDiagram m ⟶ diagram
  thickInclusion_eq : ∀ m a,
    (thickInclusion m).app a = (thickIso m a).hom ≫ (ideal a ^ m).subschemeι
  thickProjection : ∀ m,
    (Functor.const Indexᵒᵖ).obj (I ^ m).subscheme ⟶ thickDiagram m
  thickProjection_comm : ∀ m a,
    (thickProjection m).app a ≫ (thickInclusion m).app a =
      (I ^ m).subschemeι ≫ projection.app a
  thickIsLimit : ∀ m, 1 ≤ m → IsLimit (Cone.mk (I ^ m).subscheme (thickProjection m))
  thickProjectionRegular : ∀ m, 1 ≤ m → ∀ a,
    IsRegularSchemeMorphism ((thickProjection m).app a)

attribute [instance] RationalSmoothPairSystem.partialOrder
attribute [instance] RationalSmoothPairSystem.nonempty RationalSmoothPairSystem.directed

namespace RationalSmoothPairSystem

/-- The distinguished ideal on a thick fibre, by extension of the model ideal.
Source: Temkin Proposition 3.3.5 (blueprint: def-per-rational-smooth-pair-system). -/
def thickIdeal {X : Scheme.{u}} {I : X.IdealSheafData}
    (S : RationalSmoothPairSystem X I) (m : ℕ) (a : S.Indexᵒᵖ) :
    ((S.thickDiagram m).obj a).IdealSheafData :=
  (S.ideal a).comap ((S.thickInclusion m).app a)

/-- The intersection of an ambient model open with its thick fibre.
Source: Temkin Proposition 3.3.5 (blueprint: def-per-rational-smooth-pair-system). -/
def fibreOpen {X : Scheme.{u}} {I : X.IdealSheafData}
    (S : RationalSmoothPairSystem X I) (m : ℕ) (a : S.Indexᵒᵖ)
    (U : (S.diagram.obj a).Opens) : ((S.thickDiagram m).obj a).Opens :=
  (S.thickInclusion m).app a ⁻¹ᵁ U

end RationalSmoothPairSystem

end AlgebraicGeometry
