/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorNaturalityComponent
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Degreewise currying for the Hom-total-tensor comparison

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
/-- The degreewise currying maps commute with simultaneous maps of all three complexes. -/
theorem homTensorDegreewiseMap_natural
    (K K' L L' M M' : CochainComplex Mod ℤ)
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M') (n : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    ((((homComplexFunctor (R := R)).map f.op).app (homComplex (R := R) L M)) ≫
        ((homComplexFunctor (R := R)).obj (op K')).map
          ((((homComplexFunctor (R := R)).map g.op).app M) ≫
            ((homComplexFunctor (R := R)).obj (op L')).map h)).f n ≫
        homTensorDegreewiseMap R K' L' M' n =
      homTensorDegreewiseMap R K L M n ≫
        ((((homComplexFunctor (R := R)).map
          (HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).op).app M) ≫
          ((homComplexFunctor (R := R)).obj
            (op (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)))).map h).f n := by
  let := SheafOfModules.monoidalCategory R
  have hlim := (Classical.choose_spec
    (homComplex_projections_exists (R := R))).1
      (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M' n
  apply CategoryTheory.Limits.Fan.IsLimit.hom_ext hlim.some
  intro p
  exact homTensorDegreewiseMap_natural_component R K K' L L' M M' f g h
    n p (p + n) rfl

end CategoryTheory
