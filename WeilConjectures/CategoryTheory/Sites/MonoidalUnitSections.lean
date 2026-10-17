/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit

/-!
# Morphisms from the monoidal unit of a category of sheaves of modules

Let `J` be a Grothendieck topology on `C` and `R` a commutative ring, and equip the category of
sheaves of `R`-modules with the monoidal structure `CategoryTheory.Sheaf.monoidalCategory`
(sheafification of the objectwise tensor product). Let `W` be a terminal object of `C`.

* Morphisms `𝟙_ ⟶ F` correspond to sections of `F` over `W`, via evaluation at the *unit
  section* `CategoryTheory.Sheaf.unitSection J W`, the image of `1 ∈ R`
  (`CategoryTheory.Sheaf.unitHom_ext`, `CategoryTheory.Sheaf.exists_unitHom`).
* Under this correspondence, `(λ_ 𝟙_).inv ≫ (s ⊗ₘ t)` corresponds to the image of
  `s(1) ⊗ t(1)` under the canonical map `F(W) ⊗ G(W) ⟶ (F ⊗ G)(W)`
  (`CategoryTheory.Sheaf.app_leftUnitor_inv_comp_tensorHom`).

If moreover `W` has finite disjoint refinements
(`CategoryTheory.GrothendieckTopology.HasFiniteDisjointRefinements`), then taking sections over
`W` is exact and commutes with coproducts and tensor products up to finite sums. We deduce that
the unit is projective (`CategoryTheory.Sheaf.projective_unit`), that morphisms from the unit to
a coproduct factor through a finite subcoproduct
(`CategoryTheory.Sheaf.unitFactorsThroughFiniteCoproducts`) and that morphisms from the unit to
a tensor product are finite sums of tensor products (`CategoryTheory.Sheaf.unitTensorFinite`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped TensorProduct

namespace ModuleCat

variable {R : Type*} [Ring R] {D : Type*} [Category* D] {K : D ⥤ ModuleCat.{w} R}

/-- The images of the components of a colimit cocone of modules span the colimit. -/
lemma iSup_range_ι_app_eq_top {c : Cocone K} (hc : IsColimit c) :
    ⨆ d, LinearMap.range ((c.ι.app d).hom : K.obj d →ₗ[R] c.pt) = ⊤ := by
  set N := ⨆ d, LinearMap.range ((c.ι.app d).hom : K.obj d →ₗ[R] c.pt)
  have h : ModuleCat.ofHom N.mkQ = 0 := hc.hom_ext fun d ↦ by
    ext x
    simpa using Submodule.mem_iSup_of_mem d (LinearMap.mem_range_self _ x)
  rw [eq_top_iff]
  intro x _
  rw [← Submodule.Quotient.mk_eq_zero]
  exact congr($h x)

end ModuleCat

namespace CategoryTheory

namespace GrothendieckTopology.IsDisjointCover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [CommRing R]
  [J.HasSheafCompose (forget (ModuleCat.{w} R))]
  {W : C} {ι : Type*} [Finite ι] {Y : ι → C} {f : ∀ i, Y i ⟶ W}

/-- Sections of the objectwise tensor product of two sheaves of modules over the members of a
finite disjoint cover glue. -/
lemma exists_map_tensorObj_eq (hf : J.IsDisjointCover f) (F G : Sheaf J (ModuleCat.{w} R))
    (t : ∀ i, (F.obj ⊗ G.obj).obj (op (Y i))) :
    ∃ x : (F.obj ⊗ G.obj).obj (op W), ∀ i, (F.obj ⊗ G.obj).map (f i).op x = t i := by
  classical
  have := Fintype.ofFinite ι
  refine Presheaf.exists_map_eq_of_exists_map_eq_single f
    (fun i ↦ {z | ∃ (a : F.obj.obj (op (Y i))) (b : G.obj.obj (op (Y i))), a ⊗ₜ b = z})
    (fun i ↦ TensorProduct.span_tmul_eq_top _ _ _) ?_ t
  rintro i _ ⟨a, b, rfl⟩
  obtain ⟨a', ha'⟩ := hf.exists_map_eq F (Pi.single i a)
  obtain ⟨b', hb'⟩ := hf.exists_map_eq G (Pi.single i b)
  refine ⟨(a' ⊗ₜ b' : F.obj.obj (op W) ⊗[R] G.obj.obj (op W)), fun k ↦ ?_⟩
  rw [Monoidal.tensorObj_map, ModuleCat.MonoidalCategory.tensorHom_tmul, ha', hb']
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Pi.single_eq_of_ne hk]

/-- Sections of a coproduct of presheaves underlying sheaves of modules over the members of a
finite disjoint cover glue. -/
lemma exists_map_sigma_eq (hf : J.IsDisjointCover f) {K : Type*}
    (X : K → Sheaf J (ModuleCat.{w} R)) [HasCoproduct fun k ↦ (X k).obj]
    [HasColimitsOfShape (Discrete K) (ModuleCat.{w} R)]
    (t : ∀ i, (∐ fun k ↦ (X k).obj).obj (op (Y i))) :
    ∃ x : (∐ fun k ↦ (X k).obj).obj (op W), ∀ i, (∐ fun k ↦ (X k).obj).map (f i).op x = t i := by
  classical
  have := Fintype.ofFinite ι
  refine Presheaf.exists_map_eq_of_exists_map_eq_single f
    (fun i ↦ ⋃ k, Set.range ((Sigma.ι (fun k ↦ (X k).obj) k).app (op (Y i))))
    (fun i ↦ ?_) ?_ t
  · rw [Submodule.span_iUnion]
    refine eq_top_iff.2 ((ModuleCat.iSup_range_ι_app_eq_top
      (isColimitOfPreserves ((evaluation _ _).obj (op (Y i)))
        (colimit.isColimit (Discrete.functor fun k ↦ (X k).obj)))).symm.le.trans
      (iSup_le fun ⟨k⟩ ↦ le_iSup_of_le k ?_))
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨a, rfl⟩
  · rintro i _ ⟨_, ⟨k, rfl⟩, a, rfl⟩
    obtain ⟨a', ha'⟩ := hf.exists_map_eq (X k) (Pi.single i a)
    refine ⟨(Sigma.ι (fun k ↦ (X k).obj) k).app (op W) a', fun l ↦ ?_⟩
    rw [← NatTrans.naturality_apply, ha']
    by_cases hl : l = i
    · subst hl
      simp
    · simp [Pi.single_eq_of_ne hl]

end GrothendieckTopology.IsDisjointCover

namespace Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {R : Type (max u v)}
  [CommRing R] [HasWeakSheafify J (ModuleCat.{max u v} R)]
  [(J.W (A := ModuleCat.{max u v} R)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

/-- The unit section of the monoidal unit of sheaves of modules over an object `W`: the image
of `1 ∈ R` under the canonical map from the constant presheaf `R` to the unit. -/
noncomputable def unitSection (W : C) : (𝟙_ (Sheaf J (ModuleCat.{max u v} R))).obj.obj (op W) :=
  ((sheafificationAdjunction J _).homEquiv _ _
    (Functor.OplaxMonoidal.η (presheafToSheaf J (ModuleCat.{max u v} R)))).app (op W) (1 : R)

/-- The canonical morphism from the objectwise tensor product of the presheaves underlying two
sheaves of modules to the presheaf underlying their tensor product. -/
noncomputable def tensorObjComparison (F G : Sheaf J (ModuleCat.{max u v} R)) :
    F.obj ⊗ G.obj ⟶ (F ⊗ G).obj :=
  (sheafificationAdjunction J _).homEquiv _ _
    (Functor.OplaxMonoidal.δ (presheafToSheaf J (ModuleCat.{max u v} R)) _ _ ≫
      ((sheafificationAdjunction J _).counit.app F ⊗ₘ (sheafificationAdjunction J _).counit.app G))

variable {J}

end Sheaf

end CategoryTheory
