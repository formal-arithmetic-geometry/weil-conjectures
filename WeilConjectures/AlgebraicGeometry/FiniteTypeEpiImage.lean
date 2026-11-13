/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.AlgebraicGeometry.EpiOverFunctor

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
set_option linter.style.haveILetI false


/-- Epimorphic images of finite type sheaves are finite type. (Stacks, Tag 01B7.) -/
theorem sheaf_finiteType_of_epi
    {C : Type v} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
    [∀ U, (J.over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    {A B : SheafOfModules.{u} R} (e : A ⟶ B) [Epi e] :
    A.IsFiniteType → B.IsFiniteType := by
  intro hA
  obtain ⟨σ, hσ⟩ := hA.exists_localGeneratorsData
  let τ : B.LocalGeneratorsData := {
    I := σ.I
    X := σ.X
    coversTop := σ.coversTop
    generators := fun i => by
      letI := epi_overFunctor_map e (σ.X i)
      exact (σ.generators i).ofEpi ((SheafOfModules.overFunctor R (σ.X i)).map e)
  }
  refine ⟨⟨τ, ?_⟩⟩
  refine ⟨fun i => ?_⟩
  dsimp [τ]
  haveI : (σ.generators i).IsFiniteType := hσ.isFiniteType i
  letI := epi_overFunctor_map e (σ.X i)
  infer_instance

end
