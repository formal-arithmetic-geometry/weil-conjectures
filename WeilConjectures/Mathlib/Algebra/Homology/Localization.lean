/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Localization

/-!
# Quasi-isomorphisms in the homotopy category satisfy the two-out-of-three property
-/

@[expose] public section

open CategoryTheory

namespace HomotopyCategory

variable (C : Type*) [Category C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

instance : (quasiIso C c).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg n := by
    have := hg n
    have : IsIso ((homologyFunctor C c n).map f ≫ (homologyFunctor C c n).map g) := by
      simpa only [Functor.map_comp] using hfg n
    exact IsIso.of_isIso_comp_right _ ((homologyFunctor C c n).map g)
  of_precomp f g hf hfg n := by
    have := hf n
    have : IsIso ((homologyFunctor C c n).map f ≫ (homologyFunctor C c n).map g) := by
      simpa only [Functor.map_comp] using hfg n
    exact IsIso.of_isIso_comp_left ((homologyFunctor C c n).map f) _

end HomotopyCategory
