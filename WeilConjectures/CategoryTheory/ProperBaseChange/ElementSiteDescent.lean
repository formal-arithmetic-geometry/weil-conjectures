/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceConstruction

/-!
# Descent along the element site

Source: Stacks Project, Tag 0791, lemma-localize-topos-site; sites-modules.tex Tag 04J4
(blueprint: lem-weil-pbc-element-site-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

end CategoryTheory
end
