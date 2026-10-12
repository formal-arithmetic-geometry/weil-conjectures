/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.Modules.DescentEffective
public import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
public import WeilConjectures.AlgebraicGeometry.Modules.ZariskiDescent

/-!
# Modules of finite presentation descend to a finite stage of a cofiltered limit

Let `{Dⱼ}` be a cofiltered system of quasi-compact separated schemes with affine transition
morphisms and limit `lim Dⱼ`. Every module of finite presentation on `lim Dⱼ` is the pullback of
a module of finite presentation on some stage `Dⱼ` (Stacks, Tag 01ZR; EGA IV₃, 8.5.2).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D}

/-- **Modules of finite presentation descend to a finite stage** (Stacks, Tag 01ZR). Let `{Dⱼ}`
be a cofiltered system of quasi-compact separated schemes with affine transition morphisms and
limit cone `c`. Every module of finite presentation `ℱ` on `lim Dⱼ` is isomorphic to the pullback
of a module of finite presentation on some stage `Dᵢ`. -/
theorem Scheme.Modules.exists_isFinitePresentation_pullback_iso_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, (D.obj i).IsSeparated] (hc : IsLimit c) (ℱ : c.pt.Modules)
    [ℱ.IsFinitePresentation] :
    ∃ (i : I) (𝒢 : (D.obj i).Modules), 𝒢.IsFinitePresentation ∧
      Nonempty ((Modules.pullback (c.π.app i)).obj 𝒢 ≅ ℱ) :=
  sorry

end AlgebraicGeometry
