/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Stack descent and stackification on the big fppf site

Source: Stacks Project, stacks.tex, Tags 026F, 02ZP, and 0436
(blueprint: def-sfb-fppf-stackification).

This is the total-category interface of `IsModuliStack`, on the big fppf topology.
Stackification is characterized by its universal property for categories of functors
and vertical natural transformations; in particular its extension is unique up to
unique compatible isomorphism. No stackification object is chosen here.
-/

@[expose] public section

set_option autoImplicit false

universe u v v₁ w₁ v₂ w₂ v₃ w₃

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Stack descent on the big fppf topology, retaining the existing total-category
fibred-groupoid and cartesian descent conventions. An `IsColimit` cocone supplies
object descent and unique gluing of arrows.
Source: Stacks 026F (blueprint: def-sfb-fppf-stackification). -/
def IsFppfModuliStack {S : AlgebraicGeometry.Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) : Prop :=
  IsFibredInGroupoids F ∧
  ∀ (T : Over S) (R : Sieve T),
    R ∈ (AlgebraicGeometry.Scheme.fppfTopology.over S) T →
    ∀ (D : R.arrows.category ⥤ F.obj) (hD : D ⋙ F.p = R.arrows.diagram),
      ∃ (c : Cocone D) (hc : F.p.obj c.pt = T), Nonempty (IsColimit c) ∧
        ∀ i : R.arrows.category,
          F.p.map (c.ι.app i) ≫ eqToHom hc =
            eqToHom (Functor.congr_obj hD i) ≫ i.obj.hom

/-- Precomposition on categories of based functors and vertical natural transformations.
Source: Stacks 0436 (blueprint: def-sfb-fppf-stackification). -/
def stackificationPrecomp {B : Type u} [Category.{v} B]
    {P : BasedCategory.{v₁, w₁} B} {A : BasedCategory.{v₂, w₂} B}
    (i : BasedFunctor P A) (Y : BasedCategory.{v₃, w₃} B) :
    BasedFunctor A Y ⥤ BasedFunctor P Y where
  obj F := i.comp F
  map α := BasedCategory.whiskerLeft i α

/-- Stackification with its universal property. Test stacks lie in the same universe
as the stackification; the original groupoid may be smaller. Equivalence of
functor categories gives extension, uniqueness, and the full correspondence on arrows.
This is the universal stack of Stacks 02ZP; its arrow-sheafification and local-image
properties are the equivalent local description of that tag.
Source: Stacks 02ZP and 0436 (blueprint: def-sfb-fppf-stackification). -/
def IsFppfStackification {S : AlgebraicGeometry.Scheme.{u}}
    {P : BasedCategory.{v₁, w₁} (Over S)} {A : BasedCategory.{v₂, w₂} (Over S)}
    (i : BasedFunctor P A) : Prop :=
  IsFibredInGroupoids P ∧ IsFppfModuliStack A ∧
    ∀ (Y : BasedCategory.{v₂, w₂} (Over S)), IsFppfModuliStack Y →
      (stackificationPrecomp i Y).IsEquivalence

end CategoryTheory
