/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FieldShriekCompositionNormalization

/-! # Transport of completed tower components to given compactifications

Source: Stacks 0F7J, the six-square comparison of two compactification towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Transport of a single completed tower map to three specified compactifications.
Every factor is supplied explicitly; no choice of an unproved witness is made.
Source: Stacks 0F7J. -/
def sfCompletedCompositionTransport
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : DerivedCategory (scalarReductionSource l E X))
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
      ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K)))
    (hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
      e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K) hη))
    (ρf : (image (completed l E) e.restrict).obj K ≅ (image (completed l E) cf).obj K)
    (ρg : (image (completed l E) d).obj ((image (completed l E) e.restrict).obj K) ≅
      (image (completed l E) cg).obj ((image (completed l E) e.restrict).obj K))
    (ρfg : (image (completed l E) (d.comp e)).obj K ≅ (image (completed l E) cfg).obj K) :
    (image (completed l E) cg).obj ((image (completed l E) cf).obj K) ⟶
      (image (completed l E) cfg).obj K :=
  (image (completed l E) cg).map ρf.inv ≫ ρg.inv ≫
    sfCompletedCompositionOnTower l E d e K hη hLambda ≫ ρfg.hom

end WeilConjectures
