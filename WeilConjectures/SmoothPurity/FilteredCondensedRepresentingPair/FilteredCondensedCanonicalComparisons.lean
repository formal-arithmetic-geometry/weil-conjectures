/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.Pair.FilteredCondensedRepresentingPairData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility

/-! # A step of filtered condensed representing-pair descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
private theorem normalized_comparison
    {A B D Z : Type*} [Category A] [Category B] [Category D] [Category Z]
    (F : A ⥤ D) (G : B ⥤ Z) (T : D ⥤ Z)
    (e : F ≅ F) (d : G ≅ G) (he : e = Iso.refl _) (hd : d = Iso.refl _)
    (a : A) (b : B) (p : T.obj (F.obj a) ⟶ G.obj b) :
    T.map (e.inv.app a) ≫ p ≫ d.hom.app b = p := by
  subst e d
  simp

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

open CompactSupportCondensedRealization
open CondensedRing

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
set_option maxHeartbeats 800000 in
-- Matching the concrete scalar and support functors traverses large derived-category terms.
end WeilConjectures.FilteredCondensedRepresentingPair
