/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Defs

/-!

# Main Statements of Nagata Compactification

-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def NagataCompactification [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] :
    Compactification f := sorry

instance [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] : HasCompactification f :=
  (NagataCompactification f).hasCompactification

/-- A morphism `f : X ⟶ Y` over a quasi-compact and quasi-separated scheme `S`, between `S`-schemes
that are separated and of finite type over `S`, has a compactification: it is separated, locally
of finite type and quasi-compact, and `Y` is quasi-compact and quasi-separated, so Nagata's
compactification theorem applies. This is not an instance, since `S` cannot be inferred from `f`;
it can be used as a local instance. -/
theorem HasCompactification.of_isOver {S X Y : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⟶ Y)
    [f.IsOver S] [IsSeparated (X ↘ S)] [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [IsSeparated (Y ↘ S)] [QuasiCompact (Y ↘ S)] [CompactSpace S] [QuasiSeparatedSpace S] :
    HasCompactification f := by
  have e := comp_over f S
  have : IsSeparated (f ≫ (Y ↘ S)) := by rw [e]; infer_instance
  have : LocallyOfFiniteType (f ≫ (Y ↘ S)) := by rw [e]; infer_instance
  have : QuasiCompact (f ≫ (Y ↘ S)) := by rw [e]; infer_instance
  have := IsSeparated.of_comp f (Y ↘ S)
  have := locallyOfFiniteType_of_comp f (Y ↘ S)
  have := QuasiCompact.of_comp f (Y ↘ S)
  have := QuasiCompact.compactSpace_of_compactSpace (Y ↘ S)
  have := quasiSeparatedSpace_of_quasiSeparated (Y ↘ S)
  infer_instance

/-- The underlying morphism of schemes `f.left` of a morphism `f : X ⟶ Y` of `Over S`, `S`
quasi-compact and quasi-separated, between objects whose structure morphisms are separated and
of finite type, has a compactification: this is `HasCompactification.of_isOver`. This is not an
instance, since `S` cannot be inferred from `f.left`; it can be used as a local instance. -/
theorem HasCompactification.of_over {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [QuasiCompact Y.hom] [CompactSpace S] [QuasiSeparatedSpace S] :
    HasCompactification f.left :=
  have : IsSeparated (X.left ↘ S) := ‹IsSeparated X.hom›
  have : LocallyOfFiniteType (X.left ↘ S) := ‹LocallyOfFiniteType X.hom›
  have : QuasiCompact (X.left ↘ S) := ‹QuasiCompact X.hom›
  have : IsSeparated (Y.left ↘ S) := ‹IsSeparated Y.hom›
  have : QuasiCompact (Y.left ↘ S) := ‹QuasiCompact Y.hom›
  of_isOver (S := S) f.left

end AlgebraicGeometry
