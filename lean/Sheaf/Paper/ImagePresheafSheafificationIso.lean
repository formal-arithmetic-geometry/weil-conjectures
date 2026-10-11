/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Image presheaf and sheafification

Source: Stacks Project, Sites, Definition 00WM and Lemmas 00WJ, 00WK, 00WN
(blueprint: lem-weil-pbc-image-presheaf-sheafification-iso).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.GrothendieckTopology

namespace CategoryTheory

/-- The image presheaf of a morphism that is surjective after sheafification is
locally surjective, and its inclusion becomes an isomorphism after sheafification.
(Source: Stacks Project, Sites, Tags 00WM, 00WJ, 00WK, 00WN; blueprint:
(blueprint: lem-weil-pbc-image-presheaf-sheafification-iso).)
The proof proceeds by local representatives for sheafification sections, the
finite-limit preservation of sheafification, and the mono-plus-epi criterion
for sheaves of sets, as detailed in the node proof dependencies.
-/
theorem imagePresheaf_sheafification_iso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] {F G : Cᵒᵖ ⥤ Type w} (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type w)).map φ)) :
    Presheaf.IsLocallySurjective J φ ∧
      IsIso ((presheafToSheaf J (Type w)).map (Subfunctor.range φ).ι) := by
  sorry

end CategoryTheory
