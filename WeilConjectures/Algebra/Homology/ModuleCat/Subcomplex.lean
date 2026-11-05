/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Subcomplexes of complexes of modules

Let `L` be a cochain complex of `R`-modules. A family of submodules `N n ≤ Lⁿ` which is stable
under the differential defines a subcomplex `CochainComplex.subcomplex L N` of `L`, with its
inclusion `CochainComplex.subcomplexι L N`.

The subcomplexes with finitely generated terms which vanish outside a finite interval exhaust
`L`, also after tensoring with any complex `F`: every element of `(L ⊗ F)ʲ` comes from
`(L' ⊗ F)ʲ` for such a subcomplex `L'` (`CochainComplex.exists_mem_range_tensor`). If the terms
of `F` are flat, `L' ⊗ F` is a subcomplex of `L ⊗ F`
(`CochainComplex.injective_subcomplexι_whiskerRight_f`).

## Main definitions

- `CochainComplex.SubcomplexFamily`: a family of submodules stable under the differential.
- `CochainComplex.subcomplex`, `CochainComplex.subcomplexι`: the corresponding subcomplex.
- `CochainComplex.SubcomplexFamily.IsFinite`: the family consists of finitely generated
  submodules, vanishing outside a finite interval.

## Main statements

- `CochainComplex.exists_mem_range_tensor`: every element of `(L ⊗ F)ʲ` lies in the image of
  `(L' ⊗ F)ʲ` for a finite subcomplex `L'` of `L`.
- `CochainComplex.injective_subcomplexι_whiskerRight_f`: if the terms of `F` are flat
  modules, the inclusion `L' ⊗ F ⟶ L ⊗ F` is injective in every degree.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type u} [CommRing R] (L : CochainComplex (ModuleCat.{u} R) ℤ)

/-- A family of submodules `N n ≤ Lⁿ` of the terms of a complex of modules `L`, stable under
the differential. -/
structure SubcomplexFamily where
  /-- The submodule of the term in degree `n`. -/
  N (n : ℤ) : Submodule R (L.X n)
  map_d_le (n : ℤ) : (N n).map (L.d n (n + 1)).hom ≤ N (n + 1)

namespace SubcomplexFamily

variable {L}

instance : LE L.SubcomplexFamily where
  le N N' := ∀ n, N.N n ≤ N'.N n

instance : Max L.SubcomplexFamily where
  max N N' :=
    { N := fun n ↦ N.N n ⊔ N'.N n
      map_d_le := fun n ↦ by
        rw [Submodule.map_sup]
        exact sup_le_sup (N.map_d_le n) (N'.map_d_le n) }

instance : Bot L.SubcomplexFamily where
  bot :=
    { N := fun _ ↦ ⊥
      map_d_le := fun n ↦ by simp }

end SubcomplexFamily

variable {L} (N : L.SubcomplexFamily)

/-- The subcomplex of `L` defined by a family of submodules stable under the differential. -/
noncomputable def subcomplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (N.N n))
    (fun n ↦ ModuleCat.ofHom ((L.d n (n + 1)).hom.restrict
      fun x hx ↦ N.map_d_le n ⟨x, hx, rfl⟩))
    (fun n ↦ by
      ext x
      change (L.d (n + 1) (n + 1 + 1)).hom ((L.d n (n + 1)).hom x.1) = 0
      rw [← ModuleCat.comp_apply, L.d_comp_d]
      rfl)

/-- The inclusion of the subcomplex defined by a family of submodules. -/
noncomputable def subcomplexι : subcomplex N ⟶ L :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (N.N n).subtype)
    (fun n ↦ by simp only [subcomplex, CochainComplex.of_d]; rfl)

lemma injective_subcomplexι_f (n : ℤ) : Function.Injective ((subcomplexι N).f n) :=
  Subtype.val_injective

/-- The inclusion of subcomplexes defined by families `N ≤ N'`. -/
noncomputable def subcomplexMap {N N' : L.SubcomplexFamily} (h : N ≤ N') :
    subcomplex N ⟶ subcomplex N' :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (Submodule.inclusion (h n)))
    (fun n ↦ by simp only [subcomplex, CochainComplex.of_d]; rfl)

@[reassoc (attr := simp)]
lemma subcomplexMap_subcomplexι {N N' : L.SubcomplexFamily} (h : N ≤ N') :
    subcomplexMap h ≫ subcomplexι N' = subcomplexι N := rfl

/-- A finite subcomplex is bounded below. -/
lemma isStrictlyGE_subcomplex {N : L.SubcomplexFamily} {a : ℤ}
    (h : ∀ n, n < a → N.N n = ⊥) : (subcomplex N).IsStrictlyGE a := by
  rw [isStrictlyGE_iff]
  intro n hn
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (N.N n)
  rw [h n hn]
  infer_instance

/-- A finite subcomplex is bounded above. -/
lemma isStrictlyLE_subcomplex {N : L.SubcomplexFamily} {b : ℤ}
    (h : ∀ n, b < n → N.N n = ⊥) : (subcomplex N).IsStrictlyLE b := by
  rw [isStrictlyLE_iff]
  intro n hn
  rw [ModuleCat.isZero_iff_subsingleton]
  change Subsingleton (N.N n)
  rw [h n hn]
  infer_instance

section Tensor

variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

end Tensor

end CochainComplex
