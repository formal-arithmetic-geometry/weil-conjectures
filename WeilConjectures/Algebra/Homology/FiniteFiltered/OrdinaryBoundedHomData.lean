/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import WeilConjectures.CategoryTheory.FiniteFilteredGradedExactness
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Ordinary bounded derived Hom data

Source: Varshavsky §5.1.5, ordinary Hom construction before the filtration.
(blueprint: lem-trf-ordinary-bounded-hom-data).
-/

@[expose] public section
set_option autoImplicit false
universe w v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CochainComplex.FiniteFiltered
variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable [HasDerivedCategory.{(max u v) + 1} AddCommGrpCat.{max u v}]

/-- Precomposition on the ordinary Hom complex, compatible with its differential.
Source: Varshavsky §5.1.5 (blueprint: lem-trf-ordinary-bounded-hom-data). -/
def homComplexPrecomp {K K' : CochainComplex A ℤ} (f : K' ⟶ K)
    (I : CochainComplex A ℤ) : HomComplex K I ⟶ HomComplex K' I where
  f n := AddCommGrpCat.ofHom
    { toFun z := (HomComplex.Cochain.ofHom f).comp z (zero_add n)
      map_zero' := HomComplex.Cochain.comp_zero _ _
      map_add' z z' := HomComplex.Cochain.comp_add _ z z' _ }
  comm' n m _ := by
    apply AddCommGrpCat.ext
    intro z
    exact HomComplex.δ_ofHom_comp f z m

/-- Postcomposition on the ordinary Hom complex, compatible with its differential.
Source: Varshavsky §5.1.5 (blueprint: lem-trf-ordinary-bounded-hom-data). -/
def homComplexPostcomp (K : CochainComplex A ℤ) {I I' : CochainComplex A ℤ}
    (f : I ⟶ I') : HomComplex K I ⟶ HomComplex K I' where
  f n := AddCommGrpCat.ofHom
    { toFun z := z.comp (HomComplex.Cochain.ofHom f) (add_zero n)
      map_zero' := HomComplex.Cochain.zero_comp _ _
      map_add' z z' := HomComplex.Cochain.add_comp z z' _ _ }
  comm' n m _ := by
    apply AddCommGrpCat.ext
    intro z
    exact HomComplex.δ_comp_ofHom z f m

end CochainComplex.FiniteFiltered
