/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # Canonical H-zero identification for flat tensor models

## References

* Stacks Project, Tag 06YH (derived tensor), using right exactness of tensor.
-/

@[expose] public section

universe v u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]

/-- Tensoring a nonpositive flat resolution preserves its degree-zero augmentation class
(Stacks, Tag 06YH). This is the model calculation only; no flatness of `F` or `G` is
assumed. -/
theorem moduleCup_hzero_identification (F G : C) (P : CochainComplex C ℤ)
    (p : P ⟶ (CochainComplex.singleFunctor C 0).obj F)
    [P.IsStrictlyLE 0] [QuasiIso p]
    (_hflat : ∀ i : ℤ, ObjectProperty.flat (P.X i)) :
    IsIso (HomologicalComplex.homologyMap
      (((tensorRight G).mapHomologicalComplex (ComplexShape.up ℤ)).map p) 0) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorRight G) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight G)
  have hP : (P.sc 0).g = 0 := by
    have hz : IsZero (P.sc 0).X₃ := by
      simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
        P.isZero_of_isStrictlyLE 0 1
    exact hz.eq_of_tgt _ _
  have hF : (((CochainComplex.singleFunctor C 0).obj F).sc 0).g = 0 := by
    have hz : IsZero (((CochainComplex.singleFunctor C 0).obj F).sc 0).X₃ := by
      simpa [HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor] using
        ((CochainComplex.singleFunctor C 0).obj F).isZero_of_isStrictlyLE 0 1
    exact hz.eq_of_tgt _ _
  have := Functor.preservesRightHomology_of_zero_g (tensorRight G) (P.sc 0) hP
  have := Functor.preservesRightHomology_of_zero_g (tensorRight G)
    (((CochainComplex.singleFunctor C 0).obj F).sc 0) hF
  rw [← quasiIsoAt_iff_isIso_homologyMap,
    quasiIsoAt_iff]
  have : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map p) :=
    (quasiIsoAt_iff p 0).1 inferInstance
  exact ShortComplex.quasiIso_map_of_preservesRightHomology (tensorRight G)
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map p)

end DerivedCategory
