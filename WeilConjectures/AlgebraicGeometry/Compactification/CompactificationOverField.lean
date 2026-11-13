/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverBase
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# A chosen compactification over a field
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- One compactification of a morphism of `k`-schemes, chosen once and for all.
The source is separated and of finite type over `k`; the target is separated and
quasi-compact over `k`. The chosen compactification `i ≫ g = f` has a quasi-compact open
immersion `i` and a proper map `g`. No uniqueness or functoriality is asserted. -/
noncomputable def compactificationOverField (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    Compactification.BoundaryCompactification f :=
  Classical.choice (compactification_over_base (S := Spec (.of k)) f)

end AlgebraicGeometry
