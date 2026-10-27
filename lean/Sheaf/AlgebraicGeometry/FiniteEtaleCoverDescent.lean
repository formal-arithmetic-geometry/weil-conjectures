/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCoverDescentDatum
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Finite étale descent data for a family

Source: Stacks Project, Examples of Stacks, Tag 0BLZ; Descent, Tags 023V and 02W5
(blueprint: def-sfb-finite-etale-cover-descent).

## Main definitions

* `FiniteEtaleCoverDescent`: the full subcategory of finite étale local scheme data.
* `FiniteEtaleCoverDescent.localMap`: the local scheme map represented by a datum morphism.
* `FiniteEtaleCoverDescentCompatible`: the Cartesian-square, transport, and morphism equations
  characterizing the canonical pullback functor, without choosing a quasi-inverse.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The category of family scheme descent data with finite étale local structure maps.
All compatible local morphisms are retained, since this is a full subcategory.
Source: Stacks Project, Examples of Stacks, Tag 0BLZ; Descent, Tag 02W5
(blueprint: def-sfb-finite-etale-cover-descent). -/
abbrev FiniteEtaleCoverDescent
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}}
    (f : ∀ i, U i ⟶ T) :=
  ObjectProperty.FullSubcategory (fun D : SchemeCoverDescent f ↦
    ∀ i, IsFinite (D.localScheme i).hom ∧ Etale (D.localScheme i).hom)

/-- The local scheme morphism determined by a morphism of finite étale descent data.
Evaluate its local sheaf map on the universal represented point and use the specified
representing bijection; this is the usual inverse Yoneda construction.
Source: Stacks Project, Descent, Tag 02W5
(blueprint: def-sfb-finite-etale-cover-descent). -/
def FiniteEtaleCoverDescent.localMap
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}}
    {f : ∀ i, U i ⟶ T} {D E : FiniteEtaleCoverDescent f}
    (h : D ⟶ E) (i : I) : D.obj.localScheme i ⟶ E.obj.localScheme i :=
  (E.obj.representation i).homEquiv.symm
    ((h.hom.hom.hom i).hom.app (op (D.obj.localScheme i))
      ((D.obj.representation i).homEquiv (𝟙 (D.obj.localScheme i))))

/-- Equations characterizing the canonical pullback functor to finite étale family data.
The square identifies each local scheme with the fibre product; transport preserves the
coordinate in the global scheme; the last equation sends every morphism to its base change.
The source category is the recorded Mathlib category of finite étale schemes with all
base morphisms, i.e. the morphism property on arrows is `⊤`.
Source: Stacks Project, Descent, Tag 023V; Examples of Stacks, Tag 0BLZ
(blueprint: def-sfb-finite-etale-cover-descent). -/
def FiniteEtaleCoverDescentCompatible
    {I : Type (u + 1)} {T : Scheme.{u}} {U : I → Scheme.{u}}
    {f : ∀ i, U i ⟶ T}
    (F : (MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ T) ⥤ FiniteEtaleCoverDescent f)
    (q : ∀ P i, ((F.obj P).obj.localScheme i).left ⟶ P.left) : Prop :=
  (∀ P i, IsPullback (q P i) ((F.obj P).obj.localScheme i).hom P.hom (f i)) ∧
  (∀ (P : MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ T) (W : Scheme.{u}) (p : W ⟶ T)
    (i j : I) (a : W ⟶ U i) (b : W ⟶ U j)
    (ha : a ≫ f i = p) (hb : b ≫ f j = p)
    (x : ((F.obj P).obj.data.obj i).obj.obj (op ((Over.map a).obj (Over.mk (𝟙 W))))),
    (((F.obj P).obj.representation j).homEquiv.symm
      (((F.obj P).obj.data.hom p a b ha hb).hom.app (op (Over.mk (𝟙 W))) x)).left ≫
        q P j =
      (((F.obj P).obj.representation i).homEquiv.symm x).left ≫ q P i) ∧
  ∀ (P Q : MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ T) (g : P ⟶ Q) (i : I),
    (FiniteEtaleCoverDescent.localMap (F.map g) i).left ≫ q Q i = q P i ≫ g.left

end AlgebraicGeometry
