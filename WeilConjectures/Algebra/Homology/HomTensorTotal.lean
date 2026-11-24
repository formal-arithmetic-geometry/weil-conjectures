/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.HomTensorDifferential
import WeilConjectures.Algebra.Homology.HomTensorNaturality

/-!
# Hom complexes and the total tensor complex

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

-- The `max u v` module universe makes the `HasMapBifunctor` instance term exceed the default
-- `synthInstance.maxSize` of 128 (as for `CochainComplex.IsKFlatTensor`).
set_option synthInstance.maxSize 256 in
/-- The Hom-total-tensor isomorphism, natural contravariantly in `K` and `L` and
covariantly in `M`. -/
theorem homComplex_tensorTotal_iso :
    letI := SheafOfModules.monoidalCategory R
    ∃ e : ∀ (K L M : CochainComplex Mod ℤ),
      homComplex (R := R) K (homComplex (R := R) L M) ≅
        homComplex (R := R) (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M,
      ∀ (K K' L L' M M' : CochainComplex Mod ℤ)
        (f : K' ⟶ K) (g : L' ⟶ L) (h : M ⟶ M'),
        (((homComplexFunctor (R := R)).map f.op).app (homComplex (R := R) L M)) ≫
            ((homComplexFunctor (R := R)).obj (op K')).map
              ((((homComplexFunctor (R := R)).map g.op).app M) ≫
                ((homComplexFunctor (R := R)).obj (op L')).map h) ≫
            (e K' L' M').hom =
          (e K L M).hom ≫
            (((homComplexFunctor (R := R)).map
              (HomologicalComplex.mapBifunctorMap f g (curriedTensor Mod) (.up ℤ)).op).app M) ≫
            ((homComplexFunctor (R := R)).obj
              (op (CochainComplex.mapBifunctor K' L' (curriedTensor Mod)))).map h := by
  let := SheafOfModules.monoidalCategory R
  have (K L M : CochainComplex Mod ℤ) (n : ℤ) :
      IsIso (homTensorDegreewiseMap R K L M n) :=
    (homTensorDegreewiseMap_spec R K L M n).2
  let e (K L M : CochainComplex Mod ℤ) :
      homComplex (R := R) K (homComplex (R := R) L M) ≅
        homComplex (R := R) (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ asIso (homTensorDegreewiseMap R K L M n))
      (fun n m _ ↦ homTensorDegreewiseMap_comm R K L M n m)
  refine ⟨e, ?_⟩
  intro K K' L L' M M' f g h
  apply HomologicalComplex.hom_ext
  intro n
  dsimp [e]
  exact homTensorDegreewiseMap_natural R K K' L L' M M' f g h n

end CategoryTheory
