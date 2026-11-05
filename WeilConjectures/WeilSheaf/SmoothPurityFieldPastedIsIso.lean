/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedUnit
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePoint
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeCongr

/-! # Invertibility for the actual compactification exchange -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  (c : Compactification f.left) (c' : Compactification f'.left)
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left} {πZ : c'.Z ⟶ c.Z}
  (hi : IsPullback c'.i πX πZ c.i) (hg : IsPullback πZ c'.g c.g πY)
  [WeaklyEtale πZ] [WeaklyEtale πY]

variable (e : (boundedConstructibleUpperStarOfMap l (X := Y) (Y := Y') πY).obj (𝟙_ _) ⟶ 𝟙_ _)

end AlgebraicGeometry.ProEtale.CondensedRing
