/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Descending lifts along epimorphisms through a faithful functor

Let `T : C ⥤ C'` and `Φ' : C' ⥤ C''` be functors, with `Φ'` faithful, and `E : Φ ≅ T ⋙ Φ'`.
A morphism `a₀ : T A ⟶ T G` lifting `Φ g ≫ φ` for an epimorphism `g : A ⟶ F` of an abelian
category descends to a morphism `T F ⟶ T G` lifting `φ`, as soon as `T` preserves cokernels:
faithfulness of `Φ'` shows that `a₀` kills `T` of the kernel of `g`, and `T g` is the cokernel of
that kernel.

Source: Stacks Project, Lemma 09YU (3), proof, paragraph "Fully faithful" (reduction of
morphisms out of a constructible sheaf to morphisms out of a finite sum of free sheaves).
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C C' C'' : Type*} [Category C] [Category C'] [Category C''] [Abelian C]
  [Preadditive C'] [Preadditive C'']

/-- Let `E : Φ ≅ T ⋙ Φ'` with `Φ'` faithful and `T` preserving cokernels. If `g : A ⟶ F` is an
epimorphism and `a₀ : T A ⟶ T G` satisfies `Φ' a₀ = Φ g ≫ φ` up to `E`, then there is
`a : T F ⟶ T G` with `Φ' a = φ` up to `E`. -/
lemma Functor.exists_map_comp_inv_app_eq_of_epi (T : C ⥤ C') (Φ' : C' ⥤ C'') (Φ : C ⥤ C'')
    [T.PreservesZeroMorphisms] [Φ'.PreservesZeroMorphisms] [Φ.PreservesZeroMorphisms]
    [Φ'.Faithful] [Φ'.PreservesEpimorphisms] [PreservesColimitsOfShape WalkingParallelPair T]
    (E : Φ ≅ T ⋙ Φ') {A F G : C} (g : A ⟶ F) [Epi g] (φ : Φ.obj F ⟶ Φ.obj G)
    (a₀ : T.obj A ⟶ T.obj G) (ha₀ : Φ'.map a₀ ≫ E.inv.app G = E.inv.app A ≫ Φ.map g ≫ φ) :
    ∃ a : T.obj F ⟶ T.obj G, Φ'.map a ≫ E.inv.app G = E.inv.app F ≫ φ := by
  have hTg := isColimitCoforkMapOfIsColimit' T (kernel.condition g)
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι _ (kernel.condition g)) (kernelIsKernel g))
  have hι : T.map (kernel.ι g) ≫ a₀ = 0 := by
    apply Φ'.map_injective
    rw [← cancel_mono (E.inv.app G), Φ'.map_comp, Category.assoc, ha₀, Φ'.map_zero, zero_comp,
      ← Functor.comp_map, ← E.inv.naturality_assoc, ← Functor.map_comp_assoc, kernel.condition,
      Functor.map_zero, zero_comp]
  have : Epi (T.map g) := epi_of_isColimit_cofork hTg
  have hfac : T.map g ≫ hTg.desc (CokernelCofork.ofπ a₀ hι) = a₀ :=
    hTg.fac _ WalkingParallelPair.one
  refine ⟨hTg.desc (CokernelCofork.ofπ a₀ hι), ?_⟩
  rw [← cancel_epi (Φ'.map (T.map g)), ← Φ'.map_comp_assoc, hfac, ha₀, ← Functor.comp_map,
    E.inv.naturality_assoc]

end CategoryTheory
