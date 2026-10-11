/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import WeilConjectures.Compactification.BaseChange

/-!

# Compactifications of morphisms over a base scheme

Let `S` be a scheme and `f : X ⟶ Y` a morphism of `S`-schemes. A compactification
`c : X ⟶[i] Z ⟶[p] Y` of `f` makes `Z` an `S`-scheme through `p ≫ (Y ↘ S)`, for which `p` and
`i` are morphisms over `S`. If `Y` is separated and of finite type over `S`, so is `Z`, the
structure morphism `p` being proper. The same applies to the base change
`Z ×_Y Y' ⟶[snd] Y'` of a compactification along a morphism of `S`-schemes `g : Y' ⟶ Y`, and
the projection `Z ×_Y Y' ⟶ Z` is a morphism over `S`.

These instances let the compactifications of morphisms between separated `S`-schemes of finite
type be used in statements on such schemes, without any hypothesis on `Z`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {S X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The compactification `Z` of a morphism of `S`-schemes is an `S`-scheme, through the structure
morphism `p : Z ⟶ Y` followed by `Y ↘ S`. -/
instance overZ [Y.Over S] : c.Z.Over S :=
  OverClass.ofHom (c.g ≫ Y ↘ S)

instance isOver_g [Y.Over S] : c.g.IsOver S :=
  ⟨rfl⟩

instance isOver_i [X.Over S] [Y.Over S] [f.IsOver S] : c.i.IsOver S :=
  ⟨by
    change c.i ≫ c.g ≫ Y ↘ S = X ↘ S
    rw [← Category.assoc, ← c.comm]
    exact comp_over f S⟩

instance locallyOfFiniteType_over [Y.Over S] [LocallyOfFiniteType (Y ↘ S)] :
    LocallyOfFiniteType (c.Z ↘ S) :=
  inferInstanceAs (LocallyOfFiniteType (c.g ≫ Y ↘ S))

instance quasiCompact_over [Y.Over S] [QuasiCompact (Y ↘ S)] : QuasiCompact (c.Z ↘ S) :=
  inferInstanceAs (QuasiCompact (c.g ≫ Y ↘ S))

instance isSeparated_over [Y.Over S] [IsSeparated (Y ↘ S)] : IsSeparated (c.Z ↘ S) :=
  inferInstanceAs (IsSeparated (c.g ≫ Y ↘ S))

section BaseChange

variable {Y' : Scheme.{u}} (g : Y' ⟶ Y)

/-- The fibre product `Z ×_Y Y'` underlying the base change of a compactification along a
morphism `g : Y' ⟶ Y` of `S`-schemes is an `S`-scheme through the second projection, as the
compactification scheme of the base change (`Compactification.overZ`). -/
noncomputable instance overPullback [Y'.Over S] : (pullback c.g g).Over S :=
  OverClass.ofHom (pullback.snd c.g g ≫ Y' ↘ S)

/-- The projection `Z ×_Y Y' ⟶ Z` is a morphism over `S`. -/
instance isOver_pullback_fst [Y.Over S] [Y'.Over S] [g.IsOver S] :
    (pullback.fst c.g g).IsOver S :=
  ⟨by
    change pullback.fst c.g g ≫ c.g ≫ Y ↘ S = pullback.snd c.g g ≫ Y' ↘ S
    rw [pullback.condition_assoc, comp_over g S]⟩

instance locallyOfFiniteType_pullback_over [Y'.Over S] [LocallyOfFiniteType (Y' ↘ S)] :
    LocallyOfFiniteType (pullback c.g g ↘ S) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd c.g g ≫ Y' ↘ S))

instance quasiCompact_pullback_over [Y'.Over S] [QuasiCompact (Y' ↘ S)] :
    QuasiCompact (pullback c.g g ↘ S) :=
  inferInstanceAs (QuasiCompact (pullback.snd c.g g ≫ Y' ↘ S))

instance isSeparated_pullback_over [Y'.Over S] [IsSeparated (Y' ↘ S)] :
    IsSeparated (pullback c.g g ↘ S) :=
  inferInstanceAs (IsSeparated (pullback.snd c.g g ≫ Y' ↘ S))

end BaseChange

end AlgebraicGeometry.Compactification
