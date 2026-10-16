/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Image presheaf and sheafification

Source: Stacks Project, Sites, Definition 00WM and Lemmas 00WJ, 00WK, 00WN
(blueprint: lem-weil-pbc-image-presheaf-sheafification-iso).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.GrothendieckTopology

namespace CategoryTheory

/-- The image presheaf of a morphism that is surjective after sheafification is
locally surjective, and its inclusion becomes an isomorphism after sheafification.
(Source: Stacks Project, Sites, Tags 00WM, 00WJ, 00WK, 00WN; blueprint:
(blueprint: lem-weil-pbc-image-presheaf-sheafification-iso).)
The value universe contains the object and morphism universes of the site.
Mathlib's local-surjectivity comparison reflects the hypothesis to presheaves.
The range factorization then makes the inclusion locally surjective; it is
locally injective because it is a subfunctor inclusion. A locally bijective
presheaf morphism becomes an isomorphism after sheafification.
-/
theorem imagePresheaf_sheafification_iso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (max u v))] {F G : Cᵒᵖ ⥤ Type (max u v)} (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max u v))).map φ)) :
    Presheaf.IsLocallySurjective J φ ∧
      IsIso ((presheafToSheaf J (Type (max u v))).map (Subfunctor.range φ).ι) := by
  have hφ' : Presheaf.IsLocallySurjective J φ :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J φ).mp hφ
  have : Presheaf.IsLocallySurjective J ((Subfunctor.range φ).ι) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (Subfunctor.toRange_ι φ)
  have hW : J.W ((Subfunctor.range φ).ι) :=
    J.W_of_isLocallyBijective ((Subfunctor.range φ).ι)
  exact ⟨hφ', (J.W_iff _).mp hW⟩

end CategoryTheory
