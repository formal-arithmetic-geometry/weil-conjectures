/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.RingTheory.FilteredColimitAlgebrasUnderlyingModule
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Base change of a filtered colimit of algebras, elementwise

For a filtered colimit `A = colim Aᵢ` of commutative `R`-algebras and an `R`-module `N`, the
tensor product `A ⊗[R] N` is the colimit of the `Aᵢ ⊗[R] N`, described elementwise: every element
comes from a stage, and an element of a stage mapping to zero already vanishes at a later stage.
When `N` is an algebra, the maps involved are ring homomorphisms.

## Implementation details

The algebra colimit is first forgotten to a module colimit
(`filtered_colimit_algebras_underlying_module`); tensor products commute with colimits, and the
elementwise description of filtered colimits of modules then applies.

## References

* [Stacks, Tag 00DD], [Stacks, Tag 00D6], [Stacks, Tag 00D7]
* [Stacks, Tag 00CV], [Stacks, Tag 05G3]
-/

@[expose] public section

universe uR uI vA uN uM

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CommAlgCat

/-- The tensor product `(colim F) ⊗[R] N` is the colimit of the `F i ⊗[R] N` as modules:
every compatible family of linear maps factors uniquely through it. -/
theorem filteredColimit_tensorProduct_universal
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uI, uR} R) [HasColimit F]
    (N : Type uN) [AddCommGroup N] [Module R N]
    (M : Type uM) [AddCommGroup M] [Module R M]
    (μ : ∀ i : I, (F.obj i : Type uI) ⊗[R] N →ₗ[R] M)
    (hμ : ∀ (i j : I) (u : i ⟶ j),
      (μ j).comp (LinearMap.rTensor N (F.map u).hom.toLinearMap) = μ i) :
    ∃! l : (colimit F : CommAlgCat R) ⊗[R] N →ₗ[R] M,
      ∀ i : I, l.comp (LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap) = μ i := by
  classical
  let f (i : I) := TensorProduct.curry (μ i)
  have hf (i j : I) (u : i ⟶ j) :
      (f j).comp (F.map u).hom.toLinearMap = f i := by
    ext a n
    exact DFunLike.congr_fun (hμ i j u) (a ⊗ₜ[R] n)
  obtain ⟨g, hg, huniq⟩ :=
    filtered_colimit_algebras_underlying_module F (N →ₗ[R] M) f hf
  refine ⟨TensorProduct.lift g, ?_, ?_⟩
  · intro i
    apply TensorProduct.ext
    ext a n
    exact DFunLike.congr_fun (DFunLike.congr_fun (hg i) a) n
  · intro l hl
    have hc : TensorProduct.curry l = g := by
      apply huniq
      intro i
      ext a n
      exact DFunLike.congr_fun (hl i) (a ⊗ₜ[R] n)
    apply TensorProduct.curry_injective
    rw [hc]
    ext a n
    rfl

/--
Base change by tensor product preserves the elementwise description of a filtered
colimit of commutative algebras: every element of `(colim F) ⊗[R] N` comes from some
`F i ⊗[R] N`, and an element of `F i ⊗[R] N` mapping to zero vanishes in some `F j ⊗[R] N`.
-/
theorem filteredColimit_tensorProduct_elementwise
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uI, uR} R) [HasColimit F]
    (N : Type uN) [AddCommGroup N] [Module R N] :
    (∀ (x : (colimit F : CommAlgCat R) ⊗[R] N),
      ∃ (i : I) (t : (F.obj i : Type uI) ⊗[R] N),
        LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t = x) ∧
    (∀ (i : I) (t : (F.obj i : Type uI) ⊗[R] N),
      LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t = 0 →
        ∃ (j : I) (u : i ⟶ j),
          LinearMap.rTensor N (F.map u).hom.toLinearMap t = 0) := by
  classical
  let G : I ⥤ ModuleCat.{max uI uN} R :=
    { obj := fun i ↦ ModuleCat.of R ((F.obj i : Type uI) ⊗[R] N)
      map := fun u ↦ ModuleCat.ofHom (LinearMap.rTensor N (F.map u).hom.toLinearMap)
      map_id := by
        intro i
        ext a n
        simp
      map_comp := by
        intro i j k u v
        ext a n
        simp }
  let c : Cocone G :=
    { pt := ModuleCat.of R ((colimit F : CommAlgCat R) ⊗[R] N)
      ι :=
        { app := fun i ↦
            ModuleCat.ofHom (LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap)
          naturality := by
            intro i j u
            ext a n
            have h := ConcreteCategory.congr_hom (colimit.w F u) a
            change (colimit.ι F j).hom ((F.map u).hom a) = (colimit.ι F i).hom a at h
            simp [G, h] } }
  have hc : IsColimit c := by
    apply IsColimit.ofExistsUnique
    intro s
    let μ : ∀ i : I, (F.obj i : Type uI) ⊗[R] N →ₗ[R] s.pt :=
      fun i ↦ (s.ι.app i).hom
    obtain ⟨l, hl, hu⟩ := filteredColimit_tensorProduct_universal R F N s.pt μ (by
      intro i j u
      exact congrArg ModuleCat.Hom.hom (s.w u))
    refine ⟨ModuleCat.ofHom l, ?_, ?_⟩
    · intro i
      exact ModuleCat.hom_ext (hl i)
    · intro m hm
      apply ModuleCat.hom_ext
      apply hu
      intro i
      exact congrArg ModuleCat.Hom.hom (hm i)
  have : PreservesColimit G (forget (ModuleCat.{max uI uN} R)) := by
    change PreservesColimit G
      (forget₂ (ModuleCat.{max uI uN} R) AddCommGrpCat ⋙ forget AddCommGrpCat)
    have : PreservesFilteredColimitsOfSize.{uI, uI}
        (forget AddCommGrpCat.{max uI uN}) :=
      preservesFilteredColimitsOfSize_shrink _
    infer_instance
  constructor
  · intro x
    exact Concrete.isColimit_exists_rep G hc x
  · intro i t ht
    have h : c.ι.app i t = c.ι.app i 0 := by
      change LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t =
        LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap 0
      simpa only [map_zero] using ht
    obtain ⟨j, u, v, huv⟩ := Concrete.isColimit_exists_of_rep_eq G hc t 0 h
    exact ⟨j, u, by simpa [G] using huv⟩

/-- When the tensor factor is a commutative algebra, the tensor coprojections and
transition maps are underlying maps of ring homomorphisms. -/
theorem filteredColimit_tensorProduct_ringHom
    (R : Type uR) [CommRing R]
    {I : Type uI} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{vA, uR} R) [HasColimit F]
    (N : Type uN) [CommRing N] [Algebra R N] :
    (∀ i : I, ∃ φ : (F.obj i : Type vA) ⊗[R] N →+*
        (colimit F : CommAlgCat R) ⊗[R] N,
      ∀ t, φ t = LinearMap.rTensor N (colimit.ι F i).hom.toLinearMap t) ∧
    (∀ (i j : I) (u : i ⟶ j),
      ∃ φ : (F.obj i : Type vA) ⊗[R] N →+* (F.obj j : Type vA) ⊗[R] N,
        ∀ t, φ t = LinearMap.rTensor N (F.map u).hom.toLinearMap t) := by
  constructor
  · intro i
    let φ : (F.obj i : Type vA) ⊗[R] N →ₐ[R]
        (colimit F : CommAlgCat R) ⊗[R] N :=
      Algebra.TensorProduct.rTensor N (colimit.ι F i).hom
    refine ⟨φ.toRingHom, ?_⟩
    intro t
    rfl
  · intro i j u
    let φ : (F.obj i : Type vA) ⊗[R] N →ₐ[R] (F.obj j : Type vA) ⊗[R] N :=
      Algebra.TensorProduct.rTensor N (F.map u).hom
    refine ⟨φ.toRingHom, ?_⟩
    intro t
    rfl


end CommAlgCat
