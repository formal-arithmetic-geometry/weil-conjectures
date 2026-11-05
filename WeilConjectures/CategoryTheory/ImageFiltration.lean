/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.PBCFiltration

/-!
# Image filtrations

Source: blueprint node `def-sp-image-filtration`, order 508
(blueprint: def-sp-image-filtration).
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

end CategoryTheory
