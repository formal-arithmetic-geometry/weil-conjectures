/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.Triangulated.Brown.Basic

/-!
# Compact objects in preadditive categories

We record basic properties of compact objects (`CategoryTheory.Pretriangulated.IsCompactObject`)
in a preadditive category `C`, i.e. objects `X` such that every morphism from `X` to a
coproduct factors through a finite partial sum.

## Main statements

- `CategoryTheory.Pretriangulated.IsCompactObject.of_iso`: compactness is invariant under
  isomorphisms.
- `CategoryTheory.Pretriangulated.isCompactObject_of_exists_cofan`: it suffices to test
  compactness on one colimit cofan for each family of objects.
- `CategoryTheory.Pretriangulated.IsCompactObject.of_adjunction`: a left adjoint whose right
  adjoint preserves coproducts preserves compact objects.
- `CategoryTheory.Limits.Cofan.IsColimit.eq_zero_of_sum_eq_zero`: the injections into a
  coproduct are linearly independent.
- `ModuleCat.isCompactObject_self`: the free module of rank one is compact in `ModuleCat R`.
-/

@[expose] public section

universe w u u'

open CategoryTheory Limits Preadditive

namespace CategoryTheory.Limits.Cofan.IsColimit

variable {C : Type u} [Category.{w} C] [Preadditive C]

/-- If a finite sum `∑ χ j ≫ c.inj j` into a coproduct vanishes, then all the `χ j` with
`j ∈ s` vanish. -/
lemma eq_zero_of_sum_eq_zero {J : Type*} {f : J → C} {c : Cofan f} (hc : IsColimit c)
    {X : C} (s : Finset J) (χ : ∀ j, X ⟶ f j) (h : ∑ j ∈ s, χ j ≫ c.inj j = 0) {k : J}
    (hk : k ∈ s) : χ k = 0 := by
  classical
  let p : c.pt ⟶ f k := Cofan.IsColimit.desc hc fun j ↦
    if hj : j = k then eqToHom (congrArg f hj) else 0
  have hp (j : J) : c.inj j ≫ p = if hj : j = k then eqToHom (congrArg f hj) else 0 :=
    Cofan.IsColimit.fac hc _ j
  have := h =≫ p
  rw [sum_comp, zero_comp, Finset.sum_eq_single k (fun j _ hj ↦ by
    rw [Category.assoc, hp, dif_neg hj, comp_zero]) (fun h ↦ absurd hk h)] at this
  simpa [hp] using this

end CategoryTheory.Limits.Cofan.IsColimit

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{w} C] [Preadditive C]

/-- Compactness is invariant under isomorphisms. -/
lemma IsCompactObject.of_iso {X Y : C} (e : X ≅ Y) (hX : IsCompactObject X) :
    IsCompactObject Y := by
  intro J f c hc φ
  obtain ⟨s, ψ, h⟩ := hX f c hc (e.hom ≫ φ)
  refine ⟨s, fun j ↦ e.inv ≫ ψ j, ?_⟩
  rw [← e.inv_hom_id_assoc φ, h, comp_sum]
  simp only [Category.assoc]

/-- To show that `X` is compact, it suffices to show that for every family of objects, morphisms
from `X` to *some* coproduct of this family factor through a finite partial sum. -/
lemma isCompactObject_of_exists_cofan {X : C}
    (h : ∀ ⦃J : Type w⦄ (f : J → C), ∃ (c : Cofan f) (_ : IsColimit c), ∀ φ : X ⟶ c.pt,
      ∃ (s : Finset J) (ψ : ∀ j, X ⟶ f j), φ = ∑ j ∈ s, ψ j ≫ c.inj j) :
    IsCompactObject X := by
  intro J f c hc φ
  obtain ⟨c', hc', H⟩ := h f
  let e := hc.coconePointUniqueUpToIso hc'
  obtain ⟨s, ψ, hψ⟩ := H (φ ≫ e.hom)
  refine ⟨s, ψ, ?_⟩
  rw [← cancel_mono e.hom, hψ, sum_comp]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Category.assoc]
  congr 1
  exact (hc.comp_coconePointUniqueUpToIso_hom hc' ⟨j⟩).symm

/-- A left adjoint `L` whose right adjoint preserves coproducts sends compact objects to compact
objects. -/
lemma IsCompactObject.of_adjunction {D : Type u'} [Category.{w} D] [Preadditive D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) [L.Additive]
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) R] {X : C} (hX : IsCompactObject X) :
    IsCompactObject (L.obj X) := by
  intro J f c hc φ
  have hc' := isColimitCofanMkObjOfIsColimit R f c.inj (hc : IsColimit (Cofan.mk c.pt c.inj))
  obtain ⟨s, ψ, h⟩ := hX _ _ hc' (adj.homEquiv _ _ φ)
  refine ⟨s, fun j ↦ (adj.homEquiv _ _).symm (ψ j), (adj.homAddEquiv _ _).injective ?_⟩
  rw [map_sum, adj.homAddEquiv_apply, h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [adj.homAddEquiv_apply, Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rfl

end CategoryTheory.Pretriangulated

namespace ModuleCat

open CategoryTheory.Pretriangulated DirectSum

/-- The free module of rank one is compact in `ModuleCat R`: an element of a direct sum lies in
a finite partial sum. -/
lemma isCompactObject_self (R : Type w) [Ring R] : IsCompactObject (ModuleCat.of R R) := by
  classical
  refine isCompactObject_of_exists_cofan fun J f ↦
    ⟨_, coproductCoconeIsColimit f, fun φ ↦ ?_⟩
  let x : ⨁ j, f j := φ.hom 1
  refine ⟨x.support, fun j ↦ ofHom (LinearMap.toSpanSingleton R (f j) (x j)), ?_⟩
  ext : 1
  refine LinearMap.ext_ring ?_
  rw [hom_sum, LinearMap.sum_apply]
  simp only [coproductCocone, cofan_mk_inj, hom_comp, hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.toSpanSingleton_apply_one]
  exact (sum_support_of x).symm

end ModuleCat
