/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.PoincareDuality.Verdier

/-!

# Properness of the compactification of a separated scheme over a field

For a separated `k`-scheme `X` of finite type, the chosen compactification of its structure
morphism `X ⟶ Spec k` is proper over `k`
(`AlgebraicGeometry.ProEtale.CondensedRing.isProper_compactificationOverField_overObj`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Separated

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

instance isProper_compactificationOverField_overObj :
    IsProper (compactificationOverField (toPoint X)).overObj.hom :=
  have := (compactificationOverField (toPoint X)).isProper
  inferInstanceAs (IsProper (_ ≫ 𝟙 _))

end Separated

end AlgebraicGeometry.ProEtale.CondensedRing
