/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Quasi-isomorphisms in the homotopy category satisfy the two-out-of-three property

The class `HomotopyCategory.quasiIso C c` is the intersection over `n` of the inverse images
of the isomorphisms under the homology functors (`HomotopyCategory.quasiIso_eq_iInf`), hence
it has the two-out-of-three property (`HomotopyCategory.hasTwoOutOfThreeProperty_quasiIso`).
-/

@[expose] public section

open CategoryTheory

namespace HomotopyCategory

variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

/-- A morphism of the homotopy category is a quasi-isomorphism if and only if its image under
every homology functor is an isomorphism. -/
lemma quasiIso_eq_iInf : quasiIso C c =
    ⨅ n, (MorphismProperty.isomorphisms C).inverseImage (homologyFunctor C c n) := by
  ext X Y f
  simp [mem_quasiIso_iff, MorphismProperty.iInf_iff]

/-- The quasi-isomorphisms of the homotopy category have the two-out-of-three property. -/
instance hasTwoOutOfThreeProperty_quasiIso : (quasiIso C c).HasTwoOutOfThreeProperty := by
  rw [quasiIso_eq_iInf]
  infer_instance

end HomotopyCategory
