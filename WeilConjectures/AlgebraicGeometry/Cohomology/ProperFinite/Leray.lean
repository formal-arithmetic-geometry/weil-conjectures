/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Flasque
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp

/-!
# Higher direct images along a composite, at a direct-image acyclic module

If `R^q π_* M = 0` for `q > 0`, then `R^q (π ≫ g)_* M ≅ R^q g_* (π_* M)`: the degenerate case of
the Leray spectral sequence. Consequently finiteness of cohomology transfers along `π_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y T : Scheme.{u}}

/-- **Degenerate Leray.** If the higher direct images of `M` along `π` vanish, then
`R^q (π ≫ g)_* M ≅ R^q g_* (π_* M)`. -/
theorem nonempty_higherDirectImage_comp_iso (π : X ⟶ Y) (g : Y ⟶ T)
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Y.Modules] (M : X.Modules)
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage π (q + 1)).obj M)) (q : ℕ) :
    Nonempty ((higherDirectImage (π ≫ g) q).obj M ≅
      (higherDirectImage g q).obj ((pushforward π).obj M)) :=
  sorry

/-- The pushforward of a quasi-coherent module along a quasi-compact quasi-separated morphism is
quasi-coherent. -/
theorem isQuasicoherent_pushforward_of_qcqs (π : X ⟶ Y) [QuasiCompact π] [QuasiSeparated π]
    (M : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] :
    SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) ((pushforward π).obj M) :=
  sorry

variable {A : Type u} [CommRing A]

/-- If the higher direct images of `M` along `π` vanish, the cohomology of `π_* M` is finite
over `A` if and only if that of `M` is. -/
theorem finiteH_pushforward_iff_of_isZero (π : X ⟶ Y) (p : Y ⟶ Spec (.of A)) [QuasiCompact π]
    [IsSeparated π] [QuasiCompact p] [IsSeparated p] [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules] (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    (hM : ∀ q : ℕ, IsZero ((higherDirectImage π (q + 1)).obj M)) :
    FiniteH p ((pushforward π).obj M) ↔ FiniteH (π ≫ p) M :=
  sorry

end AlgebraicGeometry.Scheme.Modules
