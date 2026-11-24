/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Functorial injective embeddings for group-ring modules

For a group `G` and a ring `R`, the category of modules over `R[G]` admits functorial injective
embeddings.

## Implementation details

The module category of `R[G]` is Grothendieck abelian, so the embedding is obtained from the
functorial (monomorphism, right lifting property) factorization of `M ⟶ 0`.

## References

* Stacks Project, Injectives, Section G-modules, paragraph before Tag 04JF.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace ModuleCat

/-- For a group `G` and a ring `R`, left modules over `R[G]` admit a functorial
monomorphism into injective modules: there are a functor `J` and a natural transformation
`j : 𝟭 ⟶ J` whose components are monomorphisms and whose values `J M` are injective. -/
theorem groupAlgebra_functorialInjectiveEmbeddings
    {G : Type v} [Group G] (R : Type u) [Ring R] :
    ∃ (J : ModuleCat.{max u v} (MonoidAlgebra R G) ⥤
        ModuleCat.{max u v} (MonoidAlgebra R G)) (j : 𝟭 _ ⟶ J),
      (∀ M, Mono (j.app M)) ∧ ∀ M, Injective (J.obj M) := by
  open scoped ZeroObject in
  exact by
    let C := ModuleCat.{max u v} (MonoidAlgebra R G)
    let F : C ⥤ Arrow C :=
      { obj := fun M ↦ Arrow.mk (0 : M ⟶ 0)
        map := fun f ↦ { left := f, right := 𝟙 0 } }
    let d := MorphismProperty.functorialFactorizationData
      (MorphismProperty.monomorphisms C) (MorphismProperty.monomorphisms C).rlp
    let j : 𝟭 C ⟶ F ⋙ d.Z :=
      { app := fun M ↦ d.i.app (F.obj M)
        naturality := fun M N f ↦ d.i.naturality (F.map f) }
    refine ⟨F ⋙ d.Z, j, ?_, ?_⟩
    · intro M
      exact d.hi (F.obj M)
    · intro M
      change Injective
        (IsGrothendieckAbelian.monoMapFactorizationDataRlp (0 : M ⟶ 0)).Z
      infer_instance

end ModuleCat
