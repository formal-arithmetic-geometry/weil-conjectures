/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.AlgebraicGeometry.SmoothTraitModel
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-! # Fibrewise dense rational maps of trait models

Source: BLR, Néron Models, 2.5 and 4.3 Lemma 1
(blueprint: def-sfb-trait-rational-map).

## Main definitions

- `IsBaseDense`, `IsTraitRationalMap`: fibrewise density and rational maps.
- `IsMaximalTraitRepresentative`: the entire domain of definition.
- `HasGenericModelIso`, `IsTraitBirational`: generic isomorphisms and birationality.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- An open is base-dense when its inverse image in every scheme-theoretic fibre is dense.
Source: BLR 2.5 (blueprint: def-sfb-trait-rational-map). -/
def IsBaseDense {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) : Prop :=
  ∀ s : S, Dense ((f.fiberι s) ⁻¹' (U : Set X))

/-- An ordinary rational map is fibrewise rational if it has a base-dense representative
which is a morphism over the base. On the smooth separated models in BLR this embeds
exactly the equivalence classes defined using base-dense common opens: equality of
ordinary rational maps implies equality of the representatives on their intersection.
Source: BLR 2.5 (blueprint: def-sfb-trait-rational-map). -/
def IsTraitRationalMap {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (v : X.RationalMap Y) : Prop :=
  ∃ p : X.PartialMap Y, p.toRationalMap = v ∧ IsBaseDense f p.domain ∧
    p.hom ≫ g = p.domain.ι ≫ f

/-- A representative defined on the union of all representative domains.
Source: BLR 2.5 and 4.3 Lemma 1 (blueprint: def-sfb-trait-rational-map). -/
def IsMaximalTraitRepresentative {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (v : X.RationalMap Y) (p : X.PartialMap Y) : Prop :=
  p.toRationalMap = v ∧ p.domain = v.domain ∧ p.hom ≫ g = p.domain.ι ≫ f

/-- The generic fibre of a rational map is the specified isomorphism of G with itself.
Both commutative triangles use the given model identifications.
Source: BLR 4.3 Lemma 1 (blueprint: def-sfb-trait-rational-map). -/
def HasGenericModelIso {R E : Type u} [CommRing R] [Field E] [Algebra R E]
    {G : Over (Spec (.of E))} (M N : SmoothTraitModel (R := R) G)
    (v : M.scheme.RationalMap N.scheme) (e : G ≅ G) : Prop :=
  ∃ (p : M.scheme.PartialMap N.scheme) (l : G.left ⟶ p.domain.toScheme),
    p.toRationalMap = v ∧ l ≫ p.domain.ι = M.genericInclusion ∧
      l ≫ p.hom = e.hom.left ≫ N.genericInclusion

/-- Birational over the base means an isomorphism of base-dense open subschemes.
Source: BLR 2.5 (blueprint: def-sfb-trait-rational-map). -/
def IsTraitBirational {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (v : X.RationalMap Y) : Prop :=
  ∃ (U : X.Opens) (V : Y.Opens) (e : U.toScheme ≅ V.toScheme)
    (hU : Dense (U : Set X)),
    IsBaseDense f U ∧ IsBaseDense g V ∧
      e.hom ≫ V.ι ≫ g = U.ι ≫ f ∧
      (Scheme.PartialMap.mk U hU (e.hom ≫ V.ι)).toRationalMap = v

end AlgebraicGeometry
