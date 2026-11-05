/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Computing the cohomology presheaves with an injective resolution

Let `F` be an abelian sheaf on a site and `F ⟶ I^•` an injective resolution. For every object
`V`, the group `H^n(V, F) = Ext^n(ℤ_V^#, F)` (`CategoryTheory.Sheaf.cohomologyPresheaf`) is the
`n`-th cohomology of the complex of abelian groups `I^•(V)`, naturally in `V`.

This rests on two facts:
* a morphism `ℤ_V^# ⟶ I` from the sheafified free abelian presheaf on `V` is a section of `I`
  over `V` (`CategoryTheory.Sheaf.sheafifyFreeYonedaHomAddEquiv`);
* `Ext^n(X, Y)` is the `n`-th cohomology of `Hom(X, I^•)` for an injective resolution `I^•` of `Y`
  (`CategoryTheory.InjectiveResolution.homologyAddEquivExt`, stated for any complex of abelian
  groups identified degreewise with `Hom(X, I^•)`).

## Main definitions

- `CategoryTheory.Sheaf.complexSections`: the presheaf of complexes `V ↦ K^•(V)` attached to a
  complex of sheaves `K`.
- `CategoryTheory.Sheaf.cohomologyPresheafIso`: for an injective resolution `I^•` of `F`, the
  isomorphism of presheaves `V ↦ H^n(I^•(V))` with `F.cohomologyPresheaf n`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y : C}
  (R : InjectiveResolution Y)

/-- In degree `0`, the class `R.extMk f` vanishes only if `f` does. -/
lemma extMk_eq_zero_iff_of_zero (f : X ⟶ R.cocomplex.X 0) (hf : f ≫ R.cocomplex.d 0 1 = 0) :
    R.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact R.extMk_zero 1 rfl⟩
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq, extEquivCohomologyClass_extMk,
    extEquivCohomologyClass_zero, CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at h
  rw [CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (-1)
    (by lia)] at h
  obtain ⟨g, hg⟩ := h
  have hg0 : g = 0 :=
    (CochainComplex.isZero_of_isStrictlyGE R.cochainComplex 0 (-1) (by lia)).eq_of_tgt _ _
  rw [hg0, zero_comp] at hg
  simpa using hg.symm

variable {M : CochainComplex AddCommGrpCat.{w} ℕ} (θ : ∀ n, M.X n ≃+ (X ⟶ R.cocomplex.X n))
  (hθ : ∀ n (m : M.X n), θ (n + 1) (M.d n (n + 1) m) = θ n m ≫ R.cocomplex.d n (n + 1))

omit [HasExt.{w} C] in
include hθ in
lemma comp_d_eq_zero_of_d_eq_zero {n : ℕ} (m : M.X n) (hm : M.d n (n + 1) m = 0) :
    θ n m ≫ R.cocomplex.d n (n + 1) = 0 := by
  rw [← hθ, hm, map_zero]

omit [HasExt.{w} C] in
include hθ in
lemma θ_iCycles_comp_d (n : ℕ) (z : M.cycles n) :
    θ n (M.iCycles n z) ≫ R.cocomplex.d n (n + 1) = 0 :=
  comp_d_eq_zero_of_d_eq_zero R θ hθ _ (by
    rw [← ConcreteCategory.comp_apply, M.iCycles_d]
    rfl)

/-- The map from the cycles of `M` in degree `n` to `Ext^n(X, Y)`. -/
noncomputable def cyclesToExt (n : ℕ) : M.cycles n →+ Ext X Y n where
  toFun z := R.extMk (θ n (M.iCycles n z)) (n + 1) rfl (θ_iCycles_comp_d R θ hθ n z)
  map_zero' := by simp
  map_add' z z' := by
    simp only [map_add]
    rw [R.add_extMk]

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable [HasSheafify J AddCommGrpCat.{v}]

/-- The presheaf of complexes of sections `V ↦ K^•(V)` of a complex of abelian sheaves `K`. -/
@[simps]
noncomputable def complexSections (K : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ) :
    Cᵒᵖ ⥤ CochainComplex AddCommGrpCat.{v} ℕ where
  obj V :=
    { X n := (K.X n).obj.obj V
      d i j := (K.d i j).hom.app V
      shape i j h := by rw [K.shape i j h]; rfl
      d_comp_d' i j k _ _ := by
        rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, K.d_comp_d]
        rfl }
  map f :=
    { f n := (K.X n).obj.map f
      comm' i j _ := (K.d i j).hom.naturality f }

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] {F : Sheaf J AddCommGrpCat.{v}}
  (R : InjectiveResolution F)

end CategoryTheory.Sheaf
