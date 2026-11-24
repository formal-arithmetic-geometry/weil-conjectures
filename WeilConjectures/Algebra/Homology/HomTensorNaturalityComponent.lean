/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorLocalizedExt
import WeilConjectures.Algebra.Homology.HomTensorCurryNaturalPure

/-!
# A single component of currying naturality

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
/-- Naturality after one projection of the target Hom complex. -/
theorem homTensorDegreewiseMap_natural_component
    (K K' L L' M M' : CochainComplex Mod ℤ)
    (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M') (n p q : ℤ) (hpq : p + n = q) :
    letI := SheafOfModules.monoidalCategory R
    (((((homComplexFunctor (R := R)).map f.op).app (homComplex (R := R) L M)) ≫
        ((homComplexFunctor (R := R)).obj (op K')).map
          ((((homComplexFunctor (R := R)).map g.op).app M) ≫
            ((homComplexFunctor (R := R)).obj (op L')).map h)).f n ≫
        homTensorDegreewiseMap R K' L' M' n) ≫
      homTensorProjection R (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)) M' n p q hpq =
    (homTensorDegreewiseMap R K L M n ≫
        ((((homComplexFunctor (R := R)).map
          (HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).op).app M) ≫
          ((homComplexFunctor (R := R)).obj
            (op (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)))).map h).f n) ≫
      homTensorProjection R (CochainComplex.mapBifunctor K' L'
        (curriedTensor Mod)) M' n p q hpq := by
  let := SheafOfModules.monoidalCategory R
  subst q
  apply homTensorLocalized_ext R K' L' (M'.X (p + n)) _ p
  intro U s W i j hij x y
  subst p
  exact homTensorCurry_natural_pure R K K' L L' M M' f g h n
    (homTensorDegreewiseMap R K L M n) (homTensorDegreewiseMap R K' L' M' n)
    (homTensorDegreewiseMap_spec R K L M n).1
    (homTensorDegreewiseMap_spec R K' L' M' n).1 U s W i j x y

end CategoryTheory
