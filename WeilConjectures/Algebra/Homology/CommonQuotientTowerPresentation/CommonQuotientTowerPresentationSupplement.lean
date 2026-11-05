/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.RingTheory.Ideal.Maps
public import WeilConjectures.AlgebraicGeometry.CommonQuotientTowerPresentation

/-! # Presentations of towers of common quotient ring sheaves

Source: Stacks Project, proetale.tex, Tag 099L, section-derived-completion-noetherian;
sites-modules.tex, Tag 03EK, section-tensor-product.
(blueprint: def-weil-pbc-common-quotient-tower-presentation).

A quotient is specified by its locally surjective projection, rather than by a
sectionwise surjection. Extension of its kernel ideal is specified by the pushout
universal property in ring sheaves. This includes quotients whose sections lift only locally.
-/

@[expose] public section
set_option autoImplicit false
universe u v r m
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{r}}

namespace CommonQuotientTowerPresentation
variable {φ : R ⟶ B} (D : CommonQuotientTowerPresentation φ)

end CommonQuotientTowerPresentation
end SheafOfModules
